import os
import re
import shutil
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Dict, Tuple
import traceback
from openevolve.evaluation_result import EvaluationResult
from dotenv import load_dotenv


SUCCESS_MSG = "No error has been found"
MODULE_HEADER_RE = re.compile(r"^\s*-{2,}\s*MODULE\s+([A-Za-z0-9_]+)\s*-{2,}\s*$")
NAME_MISMATCH_RE = re.compile(r"File name '([^']+)' does not match the name '([^']+)'")
ARTIFACT_SEPARATOR = "\n---\n"
SYNTAX_ERR_LINE_RE = re.compile(r"(?i)\bline\s+(\d+)\s*,\s*column\s+(\d+)")


def _artifact_instructions(context: str = "tlc") -> str:
    if context == "translator":
        return (
            "These artifacts are from the PlusCal translator/TLA2Tools for the current program.\n"
            "Use them to fix syntax/semantic issues in the module header or PlusCal algorithm so translation succeeds.\n"
            "Once translation passes, TLC will run to check invariants."
        )
    return (
        "These artifacts are TLC outputs from running the current TLA+/PlusCal program.\n"
        "Use them to edit the PlusCal/TLA+ spec so TLC reports 'No error has been found'.\n"
        "Key fields:\n"
        "- summary: short human summary of the TLC result\n"
        "- stdout: full TLC console output, including any counterexample trace (State 1, State 2, ...)\n"
        "- stderr: tool diagnostics, if any\n"
        "Guidance:\n"
        "- If an invariant is violated, follow the trace to locate and fix the faulty algorithm step.\n"
        "- Do not modify the TLC config; make changes in the PlusCal/TLA+ spec.\n"
        "- Ensure the TLA+ module name matches the file name."
    )

INVARIANT_RE = re.compile(r"(?i)Invariant\s+([A-Za-z0-9_]+)\s+is\s+violated")
DEPTH_RES = [
    re.compile(r"(?i)Depth(?: of (?:the )?(?:search|state graph))\s*[:=]\s*(\d+)"),
    re.compile(r"(?i)The depth of the(?: state)? graph(?: search)? is\s*(\d+)"),
]
STATE_GEN_RE = re.compile(r"(?i)states generated\s*[:=]\s*([0-9,]+)")
STATE_DIST_RE = re.compile(r"(?i)(?:distinct states(?: found)?|states found)\s*[:=]\s*([0-9,]+)")

 


def _error_result(message: str, *, tb: str | None = None) -> EvaluationResult:
    metrics: Dict[str, float] = {
        "combined_score": 0.0,
        "trace_length": 0.0,
        "runtime_ms": 0.0,
    }
    metrics["error"] = message  # type: ignore[assignment]
    artifacts = {"stderr": message, "artifact_instructions": _artifact_instructions()}
    if tb:
        artifacts["traceback"] = tb
    return EvaluationResult(metrics=metrics, artifacts=artifacts)


def evaluate(program_path: str) -> EvaluationResult:
    try:
        return _evaluate(program_path)
    except subprocess.CalledProcessError as exc:  # Capture PlusCal translator errors with output
        stdout_text = getattr(exc, "stdout", "") or ""
        stderr_text = getattr(exc, "stderr", "") or ""
        # Surface the exact compiler error in the 'error' metric for next-iteration learning
        message = stderr_text or stdout_text or str(exc)

        # Compute syntax score based on how deep the first syntax error is in the file.
        # Score ranges 0..50 where 50 corresponds to successful translation or an error at EOF.
        syntax_score, syntax_breakdown = _syntax_score_from_translator_error(
            program_path, stdout_text, stderr_text
        )

        artifacts = {
            "translator_stdout": stdout_text,
            "translator_stderr": stderr_text or str(exc),
            "traceback": traceback.format_exc(),
            "artifact_instructions": _artifact_instructions("translator"),
        }
        if syntax_breakdown:
            artifacts["score_breakdown"] = syntax_breakdown  # includes syntax_score details

        return EvaluationResult(
            metrics={
                "combined_score": float(syntax_score),
                "trace_length": 0.0,
                "runtime_ms": 0.0,
                "error": message,  # type: ignore[dict-item]
            },
            artifacts=artifacts,
        )
    except subprocess.TimeoutExpired:
        return _error_result("Timeout during evaluation")
    except Exception as exc:  # noqa: BLE001 - return structured error
        return _error_result(str(exc), tb=traceback.format_exc())


def _evaluate(program_path: str) -> EvaluationResult:
    # Prefer .env at project root for TLA_TOOLS_JAR; fallback to tools/tla2tools.jar
    project_root = Path(__file__).resolve().parents[2]
    env_path = project_root / ".env"
    load_dotenv(env_path)
    jar_path = os.getenv("TLA_TOOLS_JAR") or str(project_root / "tools" / "tla2tools.jar")
    if not Path(jar_path).exists():
        return _error_result(f"Could not find tla2tools.jar at {jar_path}")

    program_src = Path(program_path)
    if not program_src.exists():
        return _error_result(f"Program path does not exist: {program_src}")

    with tempfile.TemporaryDirectory() as temp_dir_str:
        temp_dir = Path(temp_dir_str)
        module_name = _extract_module_name(program_src) or program_src.stem
        # Ensure module-file name match for PlusCal translation
        tla_filename = f"{module_name}.tla"
        tla_path = temp_dir / tla_filename
        shutil.copy2(program_src, tla_path)

        # Load TLC configuration from external pluscal.cfg
        # Prefer a cfg next to the input program; if not found (e.g., program is in a temp dir),
        # fall back to the cfg that lives next to this evaluator.
        cfg_src = program_src.parent / "tlc_config.cfg"
        if not cfg_src.exists():
            fallback_cfg = Path(__file__).resolve().parent / "tlc_config.cfg"
            if fallback_cfg.exists():
                cfg_src = fallback_cfg
            else:
                return _error_result(
                    f"Could not find TLC config file: {cfg_src}"
                )
        cfg_path = temp_dir / "tlc_config.cfg"
        shutil.copy2(cfg_src, cfg_path)

        ok, trace_length, elapsed_ms, stdout_text, stderr_text = _run_pluscal_stage(
            work_dir=temp_dir,
            jar_path=jar_path,
            tla_path=tla_path,
            cfg_path=cfg_path,
            timeout_seconds=60,
        )

        violated_invariant = _parse_violated_invariant(stdout_text)

        if ok:
            combined = 100.0
            effective_trace_len = 0
        elif violated_invariant:
            combined = 50.0
            effective_trace_len = trace_length
        else:
            combined = 0.0
            effective_trace_len = trace_length

        summary = _summarize_tlc_stdout(stdout_text)

        artifacts: Dict[str, str] = {
            "stdout": stdout_text,
            "stderr": stderr_text,
            "summary": summary,
            "artifact_instructions": _artifact_instructions(),
        }
        if violated_invariant:
            artifacts["violated_invariant"] = violated_invariant

        return EvaluationResult(
            metrics={
                "combined_score": float(combined),
                "trace_length": int(effective_trace_len),
                "runtime_ms": float(elapsed_ms),
            },
            artifacts=artifacts,
        )


def _run_pluscal_stage(
    work_dir: Path,
    jar_path: str,
    tla_path: Path,
    cfg_path: Path,
    timeout_seconds: int,
) -> Tuple[bool, int, float, str, str]:
    # Translate PlusCal to TLA+
    _translate_pluscal(work_dir=work_dir, jar_path=jar_path, tla_filename=tla_path.name, timeout_seconds=timeout_seconds)

    cmd = [
        "java",
        "-XX:+UseParallelGC",
        "-Xmx1g",
        "-jar",
        jar_path,
        "-tool",
        "-config",
        str(cfg_path),
        str(tla_path.name),
    ]

    start_time = time.time()
    proc = subprocess.run(
        cmd,
        cwd=work_dir,
        capture_output=True,
        text=True,
        timeout=timeout_seconds,
    )
    elapsed_ms = (time.time() - start_time) * 1000.0

    stdout_text = proc.stdout
    stderr_text = proc.stderr
    ok = SUCCESS_MSG in stdout_text

    trace_length = 0
    if not ok:
        trace_length = _estimate_trace_length(stdout_text)

    return ok, trace_length, elapsed_ms, stdout_text, stderr_text


def _translate_pluscal(work_dir: Path, jar_path: str, tla_filename: str, timeout_seconds: int) -> None:
    # pcal.trans is invoked via -cp
    cmd = [
        "java",
        "-cp",
        jar_path,
        "pcal.trans",
        tla_filename,
    ]
    subprocess.run(
        cmd,
        cwd=work_dir,
        capture_output=True,
        text=True,
        timeout=timeout_seconds,
        check=True,
    )


def _estimate_trace_length(tlc_stdout: str) -> int:
    return sum(1 for line in tlc_stdout.splitlines() if line.strip().startswith("State "))


def _extract_module_name(tla_path: Path) -> str | None:
    try:
        with tla_path.open("r", encoding="utf-8", errors="ignore") as f:
            for line in f:
                match = MODULE_HEADER_RE.match(line)
                if match:
                    return match.group(1)
    except Exception:
        return None
    return None


def _summarize_tlc_stdout(tlc_stdout: str) -> str:
    if SUCCESS_MSG in tlc_stdout:
        return "No error has been found. Specification satisfied."

    name_mismatch = NAME_MISMATCH_RE.search(tlc_stdout)
    if name_mismatch:
        file_stem, module_name = name_mismatch.group(1), name_mismatch.group(2)
        return (
            f"Module-file name mismatch: file '{file_stem}.tla' contains module '{module_name}'. "
            f"Rename the file to '{module_name}.tla' or ensure the evaluator stages it with that name."
        )

    if "Parsing or semantic analysis failed" in tlc_stdout:
        return "Parsing/semantic analysis failed. Check module header, constants, and syntax."

    return "TLC reported an error. See stdout for details."


def _parse_violated_invariant(tlc_stdout: str) -> str | None:
    match = INVARIANT_RE.search(tlc_stdout)
    return match.group(1) if match else None


def _parse_search_depth(tlc_stdout: str) -> int | None:
    for rx in DEPTH_RES:
        m = rx.search(tlc_stdout)
        if m:
            try:
                return int(m.group(1).replace(",", ""))
            except Exception:
                return None
    # Fallback: approximate from trace length
    tl = _estimate_trace_length(tlc_stdout)
    return max(0, tl - 1) if tl > 0 else None


def _parse_state_counts(tlc_stdout: str) -> Dict[str, int]:
    info: Dict[str, int] = {}
    m1 = STATE_GEN_RE.search(tlc_stdout)
    if m1:
        try:
            info["states_generated"] = int(m1.group(1).replace(",", ""))
        except Exception:
            pass
    m2 = STATE_DIST_RE.search(tlc_stdout)
    if m2:
        try:
            info["distinct_states"] = int(m2.group(1).replace(",", ""))
        except Exception:
            pass
    return info


def _syntax_score_from_translator_error(
    program_path: str, stdout_text: str, stderr_text: str
) -> tuple[float, Dict[str, float]]:
    """
    Derive a syntax score in [0, 50] based on the reported error line relative to
    total file length. If the error line cannot be determined, returns 0.
    """
    error_text = (stderr_text or "") + "\n" + (stdout_text or "")
    line_no: int | None = None
    m = SYNTAX_ERR_LINE_RE.search(error_text)
    if m:
        try:
            line_no = int(m.group(1))
        except Exception:
            line_no = None

    total_lines = 0
    try:
        with Path(program_path).open("r", encoding="utf-8", errors="ignore") as f:
            total_lines = sum(1 for _ in f)
    except Exception:
        total_lines = 0

    ratio = 0.0
    if line_no is not None and total_lines > 0:
        # Clamp ratio to [0, 1]
        ratio = max(0.0, min(1.0, line_no / float(total_lines)))

    syntax_score = 50.0 * ratio

    breakdown: Dict[str, float] = {
        "syntax_score": float(syntax_score),
        "syntax_error_line": float(line_no or 0),
        "total_lines": float(total_lines),
        "syntax_ratio": float(ratio),
    }

    return syntax_score, breakdown


 


if __name__ == "__main__":
    import sys

    if len(sys.argv) != 2:
        print("Usage: python evaluator.py <path/to/program_with_pluscal.tla>")
        raise SystemExit(2)
    result = evaluate(sys.argv[1])

    # Print metrics and artifacts for CLI usage
    if isinstance(result, EvaluationResult):
        print({k: v for k, v in result.metrics.items()})
        if result.artifacts:
            summary = result.artifacts.get("summary")
            if summary:
                print("\nSummary:")
                print(summary)
            
            stdout = result.artifacts.get("stdout")
            if stdout:
                print("\n--- stdout ---")
                print(stdout)
            
            stderr = result.artifacts.get("stderr")
            if stderr:
                print("\n--- stderr ---")
                print(stderr)
            
            score_breakdown = result.artifacts.get("score_breakdown")
            if score_breakdown:
                print("\n--- score_breakdown ---")
                print(score_breakdown)
    else:
        # Backward compatibility, though evaluate returns EvaluationResult
        print(result)
        try:
            artifacts = result.get("artifacts", {})
            summary = artifacts.get("summary")
            if summary:
                print("\nSummary:")
                print(summary)
        except Exception:
            pass



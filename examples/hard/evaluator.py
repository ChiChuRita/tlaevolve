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

INVARIANT_RE = re.compile(r"(?i)Invariant\s+([A-Za-z0-9_]+)\s+is\s+violated")

 


def _error_result(message: str, *, tb: str | None = None) -> EvaluationResult:
    metrics: Dict[str, float] = {
        "combined_score": 0.0,
        "trace_length": 0.0,
        "runtime_ms": 0.0,
    }
    metrics["error"] = message  # type: ignore[assignment]
    artifacts = {"stderr": message}
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
        return EvaluationResult(
            metrics={
                "combined_score": 0.0,
                "trace_length": 0.0,
                "runtime_ms": 0.0,
                "error": message,  # type: ignore[dict-item]
            },
            artifacts={
                "translator_stdout": stdout_text,
                "translator_stderr": stderr_text or str(exc),
                "traceback": traceback.format_exc(),
            },
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

        # Load TLC configuration: prefer config.cfg, fallback to pluscal.cfg (back-compat)
        # Prefer a cfg next to the input program; if not found (e.g., program is in a temp dir),
        # fall back to the cfg that lives next to this evaluator.
        cfg_candidates = [
            program_src.parent / "config.cfg",
            program_src.parent / "pluscal.cfg",
            Path(__file__).resolve().parent / "config.cfg",
            Path(__file__).resolve().parent / "pluscal.cfg",
        ]
        cfg_src = None
        for c in cfg_candidates:
            if c.exists():
                cfg_src = c
                break
        if cfg_src is None:
            return _error_result(
                "Could not find TLC config file (looked for config.cfg or pluscal.cfg)"
            )
        cfg_path = temp_dir / "config.cfg"
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
        return EvaluationResult(
            metrics={
                "combined_score": float(combined),
                "trace_length": int(effective_trace_len),
                "runtime_ms": float(elapsed_ms),
            },
            artifacts={
                "stdout": stdout_text,
                "stderr": stderr_text,
                "summary": summary,
            },
        )


# Cascade evaluation stages
def evaluate_stage1(program_path: str) -> EvaluationResult:
    """
    Stage 1: Compile-only check. Translates PlusCal to TLA+ using pcal.trans.
    Passes if translation succeeds (no syntax/semantic errors).
    """
    try:
        # Resolve TLA tools jar
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
            tla_filename = f"{module_name}.tla"
            tla_path = temp_dir / tla_filename
            shutil.copy2(program_src, tla_path)

            start_time = time.time()
            # Translate only; will raise CalledProcessError on failure
            _translate_pluscal(
                work_dir=temp_dir,
                jar_path=jar_path,
                tla_filename=tla_path.name,
                timeout_seconds=30,
            )
            elapsed_ms = (time.time() - start_time) * 1000.0

            return EvaluationResult(
                metrics={
                    "combined_score": 1.0,  # pass threshold for cascade
                    "stage1_passed": 1.0,
                    "trace_length": 0.0,
                    "runtime_ms": float(elapsed_ms),
                },
                artifacts={
                    "summary": "PlusCal translation succeeded (compile stage)",
                },
            )
    except subprocess.CalledProcessError as exc:
        stdout_text = getattr(exc, "stdout", "") or ""
        stderr_text = getattr(exc, "stderr", "") or ""
        message = stderr_text or stdout_text or str(exc)
        return EvaluationResult(
            metrics={
                "combined_score": 0.0,
                "stage1_passed": 0.0,
                "trace_length": 0.0,
                "runtime_ms": 0.0,
                "error": message,  # type: ignore[dict-item]
            },
            artifacts={
                "translator_stdout": stdout_text,
                "translator_stderr": stderr_text or str(exc),
                "traceback": traceback.format_exc(),
            },
        )
    except subprocess.TimeoutExpired:
        return _error_result("Timeout during stage1 translation")
    except Exception as exc:  # noqa: BLE001
        return _error_result(str(exc), tb=traceback.format_exc())


def evaluate_stage2(program_path: str) -> EvaluationResult:
    """
    Stage 2: Full TLC run with the resolved cfg (invariants/properties).
    """
    return _evaluate(program_path)


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



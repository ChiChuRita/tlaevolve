import os
import re
import shutil
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Dict, Optional, Tuple

from openevolve.evaluation_result import EvaluationResult


SUCCESS_MSG = "No error has been found"
MODULE_HEADER_RE = re.compile(r"^\s*-{2,}\s*MODULE\s+([A-Za-z0-9_]+)\s*-{2,}\s*$")


def evaluate(program_path: str) -> EvaluationResult:
    """
    Run PlusCal translation and TLC on the given .tla program and return a score.

    Scoring (0..1):
    - 0.0: Any failure (translation error, missing config/jar, TLC violations/deadlock/runtime errors/timeouts)
    - 1.0: TLC reports "No error has been found"

    Artifacts:
    - Always include textual artifacts "stdout" and "stderr"
      - Combine all tool outputs into "stdout" and all errors into "stderr"
      - If no output or error is produced, include empty strings
    """
    try:
        return _evaluate_core(program_path)
    except Exception as exc:  # noqa: BLE001
        # Any unexpected error maps to 0.0 with no artifacts
        return EvaluationResult(metrics={"combined_score": 0.0}, artifacts={"stdout": "", "stderr": ""})


def _evaluate_core(program_path: str) -> EvaluationResult:
    project_root = Path(__file__).resolve().parents[2]
    jar_path = os.getenv("TLA_TOOLS_JAR") or str(project_root / "tools" / "tla2tools.jar")
    if not Path(jar_path).exists():
        return EvaluationResult(metrics={"combined_score": 0.0}, artifacts={"stdout": "", "stderr": ""})

    program_src = Path(program_path)
    if not program_src.exists():
        return EvaluationResult(metrics={"combined_score": 0.0}, artifacts={"stdout": "", "stderr": ""})

    with tempfile.TemporaryDirectory() as temp_dir_str:
        temp_dir = Path(temp_dir_str)

        module_name = _extract_module_name(program_src) or program_src.stem
        tla_filename = f"{module_name}.tla"
        tla_path = temp_dir / tla_filename
        shutil.copy2(program_src, tla_path)

        cfg_src = _resolve_cfg(program_src.parent)
        if cfg_src is None:
            fallback_cfg = _resolve_cfg(Path(__file__).resolve().parent)
            if fallback_cfg is None:
                return EvaluationResult(metrics={"combined_score": 0.0}, artifacts={"stdout": "", "stderr": ""})
            cfg_src = fallback_cfg

        cfg_path = temp_dir / "tlc_config.cfg"
        shutil.copy2(cfg_src, cfg_path)

        # Translate PlusCal to TLA; if translation fails, return translator output/error as artifacts
        translator_stdout = ""
        translator_stderr = ""
        try:
            t_stdout, t_stderr = _translate_pluscal(
                work_dir=temp_dir, jar_path=jar_path, tla_filename=str(tla_path), timeout_seconds=180
            )
            translator_stdout = t_stdout or ""
            translator_stderr = t_stderr or ""
        except subprocess.CalledProcessError as exc:
            stdout_text = getattr(exc, "stdout", "") or ""
            stderr_text = getattr(exc, "stderr", "") or ""
            return _failure_result(stdout_text, stderr_text)
        except subprocess.TimeoutExpired as exc:
            stdout_text = getattr(exc, "stdout", "") or ""
            stderr_text = getattr(exc, "stderr", "") or "Timeout during translation"
            return _failure_result(stdout_text, stderr_text)

        try:
            tlc_ok, tlc_stdout, tlc_stderr, _, _ = _run_tlc(
                work_dir=temp_dir, jar_path=jar_path, tla_filename=str(tla_path), cfg_path=cfg_path, timeout_seconds=1200
            )
        except subprocess.TimeoutExpired as exc:
            # On TLC timeout, aggregate translator outputs with partial TLC outputs and return 0 score
            tlc_stdout = getattr(exc, "stdout", "") or ""
            tlc_stderr = getattr(exc, "stderr", "") or "Timeout during TLC"
            artifacts = _aggregate_artifacts(translator_stdout, translator_stderr, tlc_stdout, tlc_stderr)
            return EvaluationResult(metrics={"combined_score": 0.0}, artifacts=artifacts)

        score = _score_from_tlc_output(tlc_ok, tlc_stdout)

        # Aggregate all outputs/errors into unified stdout/stderr
        artifacts: Dict[str, str] = _aggregate_artifacts(translator_stdout, translator_stderr, tlc_stdout, tlc_stderr)

        return EvaluationResult(metrics={"combined_score": float(score)}, artifacts=artifacts)


def _translate_pluscal(*, work_dir: Path, jar_path: str, tla_filename: str, timeout_seconds: int) -> Tuple[str, str]:
    cmd = ["java", "-XX:+UseParallelGC", "-cp", jar_path, "pcal.trans", tla_filename]
    proc = subprocess.run(
        cmd,
        cwd=work_dir,
        capture_output=True,
        text=True,
        timeout=timeout_seconds,
        check=True,  # Raise on translation errors so we map to score 0
    )
    return proc.stdout, proc.stderr


def _run_tlc(*, work_dir: Path, jar_path: str, tla_filename: str, cfg_path: Path, timeout_seconds: int) -> Tuple[bool, str, str, int, float]:
    cmd = [
        "java",
        "-XX:+UseParallelGC",
        "-Xmx1g",
        "-jar",
        jar_path,
        "-tool",
        "-config",
        str(cfg_path),
        str(tla_filename),
    ]

    start = time.time()
    proc = subprocess.run(
        cmd,
        cwd=work_dir,
        capture_output=True,
        text=True,
        timeout=timeout_seconds,
    )
    elapsed_ms = (time.time() - start) * 1000.0

    stdout_text = proc.stdout or ""
    stderr_text = proc.stderr or ""
    ok = SUCCESS_MSG in stdout_text
    return ok, stdout_text, stderr_text, proc.returncode, elapsed_ms


def _resolve_cfg(search_dir: Path) -> Optional[Path]:
    for name in ("tcl_config.cfg", "tlc_config.cfg", "config.cfg"):
        candidate = search_dir / name
        if candidate.exists():
            return candidate
    return None


def _extract_module_name(tla_path: Path) -> Optional[str]:
    try:
        with tla_path.open("r", encoding="utf-8", errors="ignore") as f:
            for line in f:
                match = MODULE_HEADER_RE.match(line)
                if match:
                    return match.group(1)
    except Exception:
        return None
    return None


def _score_from_tlc_output(tlc_ok: bool, tlc_stdout: str) -> float:
    if tlc_ok:
        return 1.0
    # Any non-success TLC run maps to 0.0 (binary scoring without intermediate step)
    return 0.0


def _aggregate_artifacts(translator_stdout: str, translator_stderr: str, tlc_stdout: str = "", tlc_stderr: str = "") -> Dict[str, str]:
    stdout_parts = []
    stderr_parts = []
    if translator_stdout:
        stdout_parts.append(translator_stdout)
    if tlc_stdout:
        stdout_parts.append(tlc_stdout)
    if translator_stderr:
        stderr_parts.append(translator_stderr)
    if tlc_stderr:
        stderr_parts.append(tlc_stderr)
    return {"stdout": "\n".join(stdout_parts), "stderr": "\n".join(stderr_parts)}


def _failure_result(stdout_text: str, stderr_text: str) -> EvaluationResult:
    artifacts = {"stdout": stdout_text, "stderr": stderr_text}
    return EvaluationResult(metrics={"combined_score": 0.0}, artifacts=artifacts)



if __name__ == "__main__":
    import sys

    if len(sys.argv) != 2:
        print("Usage: python evaluator.py <path/to/program.tla>")
        raise SystemExit(2)

    result = evaluate(sys.argv[1])

    if isinstance(result, EvaluationResult):
        metrics = result.metrics
        print({k: v for k, v in metrics.items()})
        artifacts = result.artifacts
        score = float(metrics.get("combined_score", 0.0))
        if score <= 0.0:
            if artifacts:
                print("\n--- artifacts ---")
                for k, v in artifacts.items():
                    print(f"{k}:\n{v}")
        else:
            stdout = artifacts.get("stdout")
            if stdout:
                print("\n--- tlc_output ---")
                print(stdout)
    else:
        # Fallback if a dict is returned
        try:
            metrics = result
            print(metrics)
            score = float(metrics.get("combined_score", 0.0))
            artifacts = result.get("artifacts", {})
            if score <= 0.0 and artifacts:
                print("\n--- artifacts ---")
                for k, v in artifacts.items():
                    print(f"{k}:\n{v}")
            else:
                stdout = artifacts.get("stdout")
                if stdout:
                    print("\n--- tlc_output ---")
                    print(stdout)
        except Exception:
            pass
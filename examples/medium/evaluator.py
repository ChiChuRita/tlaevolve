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

    Scoring (0..100):
    - 0: fails to translate (PlusCal) or cannot run TLC
    - 50: TLC ran but did not report success (violations, deadlock, or runtime errors)
    - 100: TLC reports "No error has been found, so we have a valid solution"
    """
    try:
        print(f"[evaluator] evaluate(program_path={program_path})", flush=True)
        return _evaluate_core(program_path)
    except subprocess.TimeoutExpired:
        return EvaluationResult(metrics={"combined_score": 0.0}, artifacts={"error": "Timeout during evaluation"})
    except subprocess.CalledProcessError as exc:
        stdout_text = getattr(exc, "stdout", "") or ""
        stderr_text = getattr(exc, "stderr", "") or ""
        return EvaluationResult(
            metrics={"combined_score": 0.0},
            artifacts={
                "translator_stdout": stdout_text,
                "translator_stderr": stderr_text or str(exc),
                "error": "PlusCal translation failed",
            },
        )
    except Exception as exc:  # noqa: BLE001
        return EvaluationResult(metrics={"combined_score": 0.0}, artifacts={"error": str(exc)})


def _evaluate_core(program_path: str) -> EvaluationResult:
    project_root = Path(__file__).resolve().parents[2]
    jar_path = os.getenv("TLA_TOOLS_JAR") or str(project_root / "tools" / "tla2tools.jar")
    print(f"[evaluator] project_root={project_root}", flush=True)
    print(f"[evaluator] jar_path={jar_path} exists={Path(jar_path).exists()}", flush=True)
    if not Path(jar_path).exists():
        return EvaluationResult(metrics={"combined_score": 0.0}, artifacts={"error": f"Could not find tla2tools.jar at {jar_path}"})

    program_src = Path(program_path)
    print(f"[evaluator] program_src={program_src} exists={program_src.exists()}", flush=True)
    if not program_src.exists():
        return EvaluationResult(metrics={"combined_score": 0.0}, artifacts={"error": f"Program path does not exist: {program_src}"})

    with tempfile.TemporaryDirectory() as temp_dir_str:
        temp_dir = Path(temp_dir_str)
        print(f"[evaluator] temp_dir={temp_dir}", flush=True)

        module_name = _extract_module_name(program_src) or program_src.stem
        tla_filename = f"{module_name}.tla"
        tla_path = temp_dir / tla_filename
        shutil.copy2(program_src, tla_path)
        print(f"[evaluator] module_name={module_name}", flush=True)
        print(f"[evaluator] staged_tla={tla_path} exists={tla_path.exists()}", flush=True)

        cfg_src = _resolve_cfg(program_src.parent)
        if cfg_src is None:
            fallback_cfg = _resolve_cfg(Path(__file__).resolve().parent)
            if fallback_cfg is None:
                return EvaluationResult(
                    metrics={"combined_score": 0.0},
                    artifacts={"error": "Could not find a TLC config file (tcl_config.cfg/tlc_config.cfg/config.cfg)"},
                )
            cfg_src = fallback_cfg

        cfg_path = temp_dir / "tlc_config.cfg"
        shutil.copy2(cfg_src, cfg_path)
        print(f"[evaluator] cfg_src={cfg_src} exists={Path(cfg_src).exists()}", flush=True)
        print(f"[evaluator] staged_cfg={cfg_path} exists={cfg_path.exists()}", flush=True)
        try:
            entries = sorted(p.name for p in temp_dir.iterdir())
            print(f"[evaluator] temp_dir_contents={entries}", flush=True)
        except Exception:
            pass

        trans_out, trans_err = _translate_pluscal(
            work_dir=temp_dir, jar_path=jar_path, tla_filename=str(tla_path), timeout_seconds=180
        )
        print(f"[evaluator] translate stdout_len={len(trans_out or '')} stderr_len={len(trans_err or '')}", flush=True)

        tlc_ok, tlc_stdout, _, _, _ = _run_tlc(
            work_dir=temp_dir, jar_path=jar_path, tla_filename=str(tla_path), cfg_path=cfg_path, timeout_seconds=1200
        )
        print(f"[evaluator] tlc_ok={tlc_ok} tlc_stdout_len={len(tlc_stdout or '')}", flush=True)

        score = _score_from_tlc_output(tlc_ok, tlc_stdout)

        artifacts: Dict[str, str] = {
            "tlc_stdout": tlc_stdout,
        }

        return EvaluationResult(metrics={"combined_score": float(score)}, artifacts=artifacts)


def _translate_pluscal(*, work_dir: Path, jar_path: str, tla_filename: str, timeout_seconds: int) -> Tuple[str, str]:
    cmd = ["java", "-XX:+UseParallelGC", "-cp", jar_path, "pcal.trans", tla_filename]
    print(f"[evaluator] TRANSLATE cwd={work_dir} cmd={' '.join(cmd)} timeout={timeout_seconds}s", flush=True)
    proc = subprocess.run(
        cmd,
        cwd=work_dir,
        capture_output=True,
        text=True,
        timeout=timeout_seconds,
        check=True,  # Raise on translation errors so we map to score 0
    )
    print(f"[evaluator] TRANSLATE returncode={proc.returncode}", flush=True)
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
    print(f"[evaluator] TLC cwd={work_dir} cmd={' '.join(cmd)} timeout={timeout_seconds}s", flush=True)
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
    print(f"[evaluator] TLC returncode={proc.returncode} elapsed_ms={elapsed_ms:.0f} ok={ok} stdout_len={len(stdout_text)} stderr_len={len(stderr_text)}",
          flush=True)
    return ok, stdout_text, stderr_text, proc.returncode, elapsed_ms


def _resolve_cfg(search_dir: Path) -> Optional[Path]:
    print(f"[evaluator] resolve_cfg search_dir={search_dir}", flush=True)
    for name in ("tcl_config.cfg", "tlc_config.cfg", "config.cfg"):
        candidate = search_dir / name
        print(f"[evaluator] resolve_cfg try={candidate} exists={candidate.exists()}", flush=True)
        if candidate.exists():
            print(f"[evaluator] resolve_cfg found={candidate}", flush=True)
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
        return 100.0
    # Any non-success TLC run maps to 50 per rubric (compiled but failed checks/runtime)
    return 50.0


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
            stdout = artifacts.get("tlc_stdout")
            if stdout:
                print("\n--- tlc_stdout ---")
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
                stdout = artifacts.get("tlc_stdout")
                if stdout:
                    print("\n--- tlc_stdout ---")
                    print(stdout)
        except Exception:
            pass
import os
import re
import shutil
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Dict, Tuple
import traceback
from dotenv import load_dotenv
from openevolve.evaluation_result import EvaluationResult


SUCCESS_MSG = "No error has been found"
ARTIFACT_SEPARATOR = "\n---\n"
MODULE_HEADER_RE = re.compile(r"^\s*-{2,}\s*MODULE\s+([A-Za-z0-9_]+)\s*-{2,}\s*$")

INVARIANT_RE = re.compile(r"(?i)Invariant\s+([A-Za-z0-9_]+)\s+is\s+violated")
DEPTH_RES = [
    re.compile(r"(?i)Depth(?: of (?:the )?(?:search|state graph))\s*[:=]\s*(\d+)")
]
STATE_GEN_RE = re.compile(r"(?i)states generated\s*[:=]\s*([0-9,]+)")
STATE_DIST_RE = re.compile(r"(?i)(?:distinct states(?: found)?|states found)\s*[:=]\s*([0-9,]+)")


def _error_result(message: str, *, stdout: str = "", stderr: str = "") -> EvaluationResult:
    return EvaluationResult(
        metrics={"combined_score": 0.0, "error": message},
        artifacts={"stdout": stdout, "stderr": stderr},
    )


def evaluate(program_path: str) -> EvaluationResult:
    try:
        return _evaluate(program_path)
    except subprocess.TimeoutExpired:
        return _error_result("Timeout during evaluation")
    except subprocess.CalledProcessError as exc:  # TLC error surfaced
        return _error_result("TLC failed", stdout=getattr(exc, "stdout", "") or "", stderr=getattr(exc, "stderr", "") or str(exc))
    except Exception as exc:  # noqa: BLE001
        return _error_result(str(exc))


def _evaluate(program_path: str) -> EvaluationResult:
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

        # Translate PlusCal to TLA+
        _translate_pluscal(work_dir=temp_dir, jar_path=jar_path, tla_filename=tla_path.name, timeout_seconds=60)

        # Create TLC config
        cfg_path = temp_dir / "program.cfg"
        cfg_content = "\n".join([
            "SPECIFICATION Spec",
            "INVARIANTS SafeBounds",
        ])
        cfg_path.write_text(cfg_content)

        cmd = [
            "java",
            "-XX:+UseParallelGC",
            "-Xmx512m",
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
            cwd=temp_dir,
            capture_output=True,
            text=True,
            timeout=60,
        )
        elapsed_ms = (time.time() - start_time) * 1000.0

        stdout_text = proc.stdout
        stderr_text = proc.stderr
        ok = SUCCESS_MSG in stdout_text

        if not ok:
            inv = INVARIANT_RE.search(stdout_text)
            violated = inv is not None
            combined = 50.0 if violated else 0.0
            return EvaluationResult(
                metrics={
                    "combined_score": float(combined),
                    "trace_length": _estimate_trace_length(stdout_text),
                    "runtime_ms": float(elapsed_ms),
                    "passed": float(0.0),
                },
                artifacts={
                    "stdout": stdout_text,
                    "stderr": stderr_text,
                },
            )

        # Passed
        return EvaluationResult(
            metrics={
                "combined_score": 100.0,
                "trace_length": 0,
                "runtime_ms": float(elapsed_ms),
                "passed": float(1.0),
            },
            artifacts={
                "stdout": stdout_text,
                "stderr": stderr_text,
                "summary": "No error has been found. Specification satisfied.",
            },
        )


def _estimate_trace_length(tlc_stdout: str) -> int:
    return sum(1 for line in tlc_stdout.splitlines() if line.strip().startswith("State "))


def _parse_search_depth(tlc_stdout: str) -> int | None:
    for rx in DEPTH_RES:
        m = rx.search(tlc_stdout)
        if m:
            try:
                return int(m.group(1).replace(",", ""))
            except Exception:
                return None
    return None


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


if __name__ == "__main__":
    import sys
    if len(sys.argv) != 1 and len(sys.argv) != 2:
        print("Usage: python evaluator.py [path/to/initial_program.tla]")
        raise SystemExit(2)
    target = sys.argv[1] if len(sys.argv) == 2 else str(Path(__file__).with_name("initial_program.tla"))
    res = evaluate(target)
    if isinstance(res, EvaluationResult):
        print({k: v for k, v in res.metrics.items()})
        if res.artifacts.get("summary"):
            print("\nSummary:\n" + str(res.artifacts["summary"]))
    else:
        print(res)



def _translate_pluscal(work_dir: Path, jar_path: str, tla_filename: str, timeout_seconds: int) -> None:
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

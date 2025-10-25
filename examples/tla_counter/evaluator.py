import os
import re
import shutil
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Dict, Tuple
from dotenv import load_dotenv


def evaluate(program_path: str) -> Dict:
    try:
        return _evaluate(program_path)
    except subprocess.TimeoutExpired:
        return {
            "combined_score": 0.0,
            "error": "Timeout during evaluation",
        }
    except Exception as exc:  # noqa: BLE001 - return structured error
        return {
            "combined_score": 0.0,
            "error": str(exc),
        }


def _evaluate(program_path: str) -> Dict:
    # Prefer .env at project root for TLA_TOOLS_JAR; fallback to tools/tla2tools.jar
    project_root = Path(__file__).resolve().parents[2]
    env_path = project_root / ".env"
    if env_path.exists():
        load_dotenv(env_path)
    jar_path = os.getenv("TLA_TOOLS_JAR")
    if not jar_path:
        jar_path = str(project_root / "tools" / "tla2tools.jar")
    if not Path(jar_path).exists():
        return {
            "combined_score": 0.0,
            "error": f"Could not find tla2tools.jar at {jar_path}",
        }

    program_src = Path(program_path)
    if not program_src.exists():
        return {
            "combined_score": 0.0,
            "error": f"Program path does not exist: {program_src}",
        }

    with tempfile.TemporaryDirectory() as temp_dir_str:
        temp_dir = Path(temp_dir_str)
        module_name = _extract_module_name(program_src)
        tla_filename = f"{module_name}.tla" if module_name else (program_src.name if program_src.suffix == ".tla" else "program.tla")
        tla_path = temp_dir / tla_filename
        shutil.copy2(program_src, tla_path)

        stage1_ok, stage1_trace_len, stage1_ms, stage1_out, stage1_err = _run_stage(
            work_dir=temp_dir,
            jar_path=jar_path,
            tla_path=tla_path,
            max_value=2,
            max_depth=6,
            timeout_seconds=60,
        )

        if stage1_ok:
            score = 100.0
            stage2_ok, stage2_trace_len, stage2_ms, stage2_out, stage2_err = _run_stage(
                work_dir=temp_dir,
                jar_path=jar_path,
                tla_path=tla_path,
                max_value=3,
                max_depth=10,
                timeout_seconds=60,
            )
            if stage2_ok:
                score += 20.0
            else:
                score += max(-100.0, -5.0 * (10 - stage2_trace_len + 1))

            summary = _summarize_tlc_stdout(stage1_out)
            return {
                "combined_score": float(score),
                "trace_length": int(0 if stage2_ok else stage2_trace_len),
                "runtime_ms": float(stage1_ms + stage2_ms),
                "passed": bool(stage2_ok),
                "stage": 2,
                "artifacts": {
                    "stdout": stage1_out + "\n---\n" + stage2_out,
                    "stderr": stage1_err + "\n---\n" + stage2_err,
                    "summary": summary,
                },
            }

        score = max(0.0, 100.0 - 5.0 * (6 - stage1_trace_len + 1))
        summary = _summarize_tlc_stdout(stage1_out)
        return {
            "combined_score": float(score),
            "trace_length": int(stage1_trace_len),
            "runtime_ms": float(stage1_ms),
            "passed": False,
            "stage": 1,
            "artifacts": {
                "stdout": stage1_out,
                "stderr": stage1_err,
                "summary": summary,
            },
        }


def _run_stage(
    work_dir: Path,
    jar_path: str,
    tla_path: Path,
    max_value: int,
    max_depth: int,
    timeout_seconds: int,
) -> Tuple[bool, int, float, str, str]:
    cfg_path = work_dir / "program.cfg"
    cfg_content = (
        "SPECIFICATION Spec\n"
        "INVARIANTS WithinBounds\n"
        f"CONSTANTS Max = {max_value}\n"
        f"CONSTANTS MaxDepth = {max_depth}\n"
    )
    cfg_path.write_text(cfg_content)

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
    ok = "No error has been found" in stdout_text

    trace_length = 0
    if not ok:
        trace_length = _estimate_trace_length(stdout_text)

    return ok, trace_length, elapsed_ms, stdout_text, stderr_text


def _estimate_trace_length(tlc_stdout: str) -> int:
    count = 0
    for line in tlc_stdout.splitlines():
        stripped = line.strip()
        if stripped.startswith("State "):
            count += 1
    return count


def _extract_module_name(tla_path: Path) -> str | None:
    try:
        with tla_path.open("r", encoding="utf-8", errors="ignore") as f:
            for line in f:
                match = re.match(r"^\s*-{2,}\s*MODULE\s+([A-Za-z0-9_]+)\s*-{2,}\s*$", line)
                if match:
                    return match.group(1)
    except Exception:
        return None
    return None


def _summarize_tlc_stdout(tlc_stdout: str) -> str:
    if "No error has been found" in tlc_stdout:
        return "No error has been found. Specification satisfied."

    name_mismatch = re.search(r"File name '([^']+)' does not match the name '([^']+)'", tlc_stdout)
    if name_mismatch:
        file_stem, module_name = name_mismatch.group(1), name_mismatch.group(2)
        return (
            f"Module-file name mismatch: file '{file_stem}.tla' contains module '{module_name}'. "
            f"Rename the file to '{module_name}.tla' or ensure the evaluator stages it with that name."
        )

    if "Parsing or semantic analysis failed" in tlc_stdout:
        return "Parsing/semantic analysis failed. Check module header, constants, and syntax."

    return "TLC reported an error. See stdout for details."


if __name__ == "__main__":
    import sys

    if len(sys.argv) != 2:
        print("Usage: python evaluator.py <path/to/mutated_program.tla>")
        raise SystemExit(2)
    result = evaluate(sys.argv[1])
    print(result)
    try:
        artifacts = result.get("artifacts", {})
        summary = artifacts.get("summary")
        if summary:
            print("\nSummary:")
            print(summary)
    except Exception:
        pass



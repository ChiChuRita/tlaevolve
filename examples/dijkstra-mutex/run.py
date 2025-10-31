from __future__ import annotations

import subprocess
import sys
from pathlib import Path


def main() -> int:
    script_dir = Path(__file__).resolve().parent
    repo_root = script_dir.parents[1]

    initial_program = script_dir / "initial_program.tla"
    evaluator = script_dir / "evaluator.py"
    config_yaml = script_dir / "config.yaml"
    output_dir = repo_root / "runs" / "dijstra-mutex"

    output_dir.mkdir(parents=True, exist_ok=True)

    cmd = [
        "uv",
        "run",
        "openevolve-run",
        str(initial_program),
        str(evaluator),
        "--config",
        str(config_yaml),
        "--output",
        str(output_dir),
        "--target-score",
        "100",
    ]

    try:
        return subprocess.run(cmd, check=False).returncode
    except FileNotFoundError:
        print("Error: 'uv' not found in PATH. Please install uv or add it to PATH.", file=sys.stderr)
        return 127


if __name__ == "__main__":
    raise SystemExit(main())



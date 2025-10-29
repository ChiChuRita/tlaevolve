#!/usr/bin/env bash
set -euo pipefail

# Usage:
#   ./run_example.sh <name> <iterations> [extra_args...]
# Examples:
#   ./run_example.sh tla_counter 50
#   ./run_example.sh peterson_pluscal 120 --log-level DEBUG

NAME="${1:-tla_counter}"
ITERATIONS="${2:-50}"

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EXAMPLE_DIR="${ROOT_DIR}/examples/${NAME}"
PROGRAM="${EXAMPLE_DIR}/initial_program.tla"
EVALUATOR="${EXAMPLE_DIR}/evaluator.py"
CONFIG="${EXAMPLE_DIR}/config.yaml"
OUTPUT_DIR="${ROOT_DIR}/runs/${NAME}"

# Load environment variables from .env if present
if [[ -f "${ROOT_DIR}/.env" ]]; then
  echo "Loading environment from ${ROOT_DIR}/.env"
  set -a
  # Temporarily disable nounset to avoid errors on empty/unset variables in .env
  set +u
  # shellcheck source=/dev/null
  source "${ROOT_DIR}/.env"
  set -u
  set +a
fi

# Validate inputs
if [[ ! -f "${PROGRAM}" ]]; then
  echo "Program not found: ${PROGRAM}" >&2
  exit 1
fi
if [[ ! -f "${EVALUATOR}" ]]; then
  echo "Evaluator not found: ${EVALUATOR}" >&2
  exit 1
fi
if [[ ! -f "${CONFIG}" ]]; then
  echo "Config not found: ${CONFIG}" >&2
  exit 1
fi

mkdir -p "${OUTPUT_DIR}"

echo "Running example '${NAME}' for ${ITERATIONS} iterations..."
echo "Output directory: ${OUTPUT_DIR}"

uv run openevolve-run \
  "${PROGRAM}" \
  "${EVALUATOR}" \
  --config "${CONFIG}" \
  --output "${OUTPUT_DIR}" \
  --iterations "${ITERATIONS}" \
  "${@:3}"



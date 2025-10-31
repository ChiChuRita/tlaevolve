## TLAEvolve — evolve TLA+/PlusCal with LLMs and TLC

TLAEvolve aims to automatically synthesize and improve TLA+/PlusCal specifications using an LLM-driven evolutionary loop with TLC as the ground-truth judge. Starting from a seed program, the system proposes changes, runs TLC to check invariants/properties, scores candidates, and iterates until a good solution emerges.

Built on top of `openevolve`, it combines MAP-Elites style diversity, island-based search, and checkpointing with domain-specific evaluators that run TLC (and PlusCal translation when needed).

### Why this project

- Formal specs are precise but time-consuming to write and iterate on. We want a loop that proposes plausible changes and keeps only those that pass more checks.
- TLC provides an objective fitness function from the spec itself; LLMs supply creative, guided mutations.

### How it works (high level)

1. Seed: Provide a TLA+/PlusCal program and an evaluator that runs TLC with your `.cfg`.
2. Propose: The LLM suggests edits (diff-based by default).
3. Judge: The evaluator executes TLC, parses results, and returns `combined_score` plus artifacts.
4. Select + diversify: The search maintains diverse, high-scoring solutions and periodically migrates between islands.
5. Stop when done: Early-stop on reaching a target score or after N iterations; artifacts are saved.

---

## Prerequisites

- Java 11+ (17+ preferred)
- Python 3.10+ (repo uses `uv` for environment management)
- TLC tools JAR (`tla2tools.jar`)

### TLC JAR setup

1. Verify Java:

```bash
java -version
```

2. Get `tla2tools.jar` from `https://github.com/tlaplus/tlaplus/releases` (or use the copy at `tools/tla2tools.jar`).

3. Create `.env` in the repo root:

```
# If not set, defaults to tools/tla2tools.jar in this repo
TLA_TOOLS_JAR=/absolute/path/to/tla2tools.jar
OPENAI_API_KEY=YOUR_API_KEY
```

---

## Install

```bash
cd /Users/chichurita/Dev/tlaevolve
uv sync
```

Export env so the CLI sees keys/paths:

```bash
set -a; source .env; set +a
```

---

## Quickstart — PlusCal (Peterson)

Run evolution directly; the evaluator will translate PlusCal and run TLC with `pluscal.cfg`:

```bash
uv run openevolve-run \
  examples/pluscal/initial_program.tla \
  examples/pluscal/evaluator.py \
  --output runs/pluscal \
  --iterations 20 \
  --target-score 100
```

Outputs:

- Best program: `runs/pluscal/best/best_program.tla`
- Logs/checkpoints: `runs/pluscal/`

## Quickstart — Harder spec (custom cfg)

This example prefers `examples/hard/config.cfg` (falls back to `pluscal.cfg`). It includes an OpenEvolve YAML config you can tweak.

```bash
uv run openevolve-run \
  examples/hard/initial_program.tla \
  examples/hard/evaluator.py \
  --config examples/hard/config.yaml \
  --output runs/hard \
  --iterations 50 \
  --target-score 100
```

---

## Visualize checkpoints

Install minimal UI deps and launch the viewer against a checkpoint:

```bash
uv pip install -r openevolve/scripts/requirements.txt
uv run python openevolve/scripts/visualizer.py --path ./runs/pluscal/checkpoints/checkpoint_10
```

---

## Scoring and artifacts

Evaluators return an `EvaluationResult` with:

- `metrics.combined_score` in 0..100 (100 means TLC found no errors)
- `metrics.trace_length`, `metrics.runtime_ms`
- `artifacts.stdout`/`stderr` (TLC output), and a short `artifacts.summary`

Notes:

- PlusCal evaluators invoke `pcal.trans` before running TLC.
- `examples/hard/evaluator.py` supports cascade stages and prefers `config.cfg`.

---

## Tips

- If TLC complains about module/file name mismatch, the evaluators automatically stage the input under `<ModuleName>.tla`.
- Put your TLC `.cfg` next to the program under test; the evaluators will detect and use it.
- You can omit `--config`; defaults are loaded and environment vars are applied (`OPENAI_API_KEY`, optional `OPENAI_API_BASE`).

---

## Acknowledgments

This project builds on the `openevolve` engine (bundled here) and the TLA+ tools.

> [!NOTE]
> 🔗 Quick access: [Add your link here](https://example.com)

# TLC JAR setup

1. Install Java (11+ recommended; 17+ preferred). Verify:

```bash
java -version
```

2. Download `tla2tools.jar` from `https://github.com/tlaplus/tlaplus/releases`.

3. Create a `.env` at the project root (preferred):

```
# Optional: if not set, defaults to tools/tla2tools.jar in this repo
TLA_TOOLS_JAR=/path/to/tla2tools.jar
OPENAI_API_KEY=YOUR_OPENAI_API_KEY
```

4. Quick sanity check (optional):

```bash
cd examples/tla_counter
python evaluator.py initial_program.tla
```

If `combined_score` is positive and no `error` field appears, TLC is wired up.

## Run OpenEvolve (TLA counter example)

1. Install dependencies (creates `.venv`):

```bash
cd path/to/tlaevolve
uv sync
```

2. Export your `.env` into the current shell (needed for the CLI to see API keys):

```bash
cd path/to/tlaevolve
set -a; source .env; set +a
```

3. Run the evolution:

```bash
uv run openevolve-run \
  examples/tla_counter/initial_program.tla \
  examples/tla_counter/evaluator.py \
  --config examples/tla_counter/config.yaml \
  --output runs/tla_counter \
  --iterations 50
```

4. Results:

- Best program: `runs/tla_counter/best/best_program.tla`
- Logs/checkpoints: `runs/tla_counter/`

## Scoring

OpenEvolve uses a single `combined_score` in the range 0..120. The evaluator computes this directly from TLC output.

### TLC stages

Candidates are checked in two TLC "stages" with increasing difficulty:

- Stage 1: `Max=2`, `MaxDepth=6`
- Stage 2: `Max=3`, `MaxDepth=10`

### How `combined_score` is computed

We blend three signals into a normalized value and scale it to 0..120:

- Depth-of-failure (later failures are better)
- Coverage proxy via TLC search depth
- Severity weighting for violated invariants

Per stage (use `MaxDepth=6` for Stage 1, `MaxDepth=10` for Stage 2):

- `depth_ratio = min(trace_length, MaxDepth) / MaxDepth`
- `search_depth` is parsed from TLC stdout (e.g., `Depth of search: N`); fallback to `trace_length - 1`
- `coverage_ratio = min(search_depth, MaxDepth) / MaxDepth` (0 if unknown)
- Invariant weights (MVP): `WithinBounds -> 1.0` (unknown defaults to `1.0`)
- Blend and penalty:
  - `raw = 0.6 * depth_ratio + 0.4 * coverage_ratio`
  - `normalized = max(0, raw - 0.5 * weight * (1 - raw))`
  - `combined_score = clamp(0, 120, 120 * normalized)`

Success case: if TLC prints "No error has been found", `combined_score = 120`.

### Artifacts and breakdown

The evaluator attaches a detailed breakdown under `artifacts.score_breakdown`:

- `violated_invariant`: name if parsed (e.g., `WithinBounds`), otherwise null
- `trace_length`: number of counterexample states (0 on success)
- `search_depth`: parsed TLC maximum search depth (or approximation)
- `depth_ratio`, `coverage_ratio`: the normalized terms above
- `severity_weight`: weight for the violated invariant (MVP defaults to 1.0)
- `raw`: the pre-penalty blend
- `normalized`: post-penalty 0..1 signal used for scoring
- `combined_score`: final 0..120 score used by OpenEvolve

## Run OpenEvolve (PlusCal Peterson example)

1. Translate and evaluate automatically via the evaluator (no manual steps):

```bash
uv run openevolve-run \
  examples/pluscal/initial_program.tla \
  examples/pluscal/evaluator.py \
  --config examples/pluscal/config.yaml \
  --output runs/pluscal \
  --iterations 20
```

Notes:

- The evaluator invokes `pcal.trans` from `tla2tools.jar` automatically in a temp dir.
- The TLC config checks `SPECIFICATION Spec` and `INVARIANTS MutualExclusion`.
- The combined score blends depth-of-failure, coverage proxy, and invariant severity (see Scoring above).
- `states_generated`, `distinct_states` (when available): parsed from TLC stdout

### Notes

- The MVP formulation is intentionally simple and robust to minor TLC message variations.
- As the system matures, you can add invariant weights in config and adjust blending weights to better match your domain’s priorities.

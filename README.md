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

### Using OpenRouter

If you prefer OpenRouter, set your key and use the OpenRouter API base:

```bash
export OPENAI_API_KEY="$OPENROUTER_API_KEY"
uv run openevolve-run \
  /tlaevolve/examples/tla_counter/initial_program.tla \
  /tlaevolve/examples/tla_counter/evaluator.py \
  --config /tlaevolve/examples/tla_counter/config.yaml \
  --output /tlaevolve/runs/tla_counter \
```

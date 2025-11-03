Easy Test Case. There are sample solution for this in PlusCal, so it potentially simply recites the solution

```bash
uv run openevolve-run \
  examples/dijkstra-mutex/initial_program.tla \
  examples/dijkstra-mutex/evaluator.py \
  --config examples/dijkstra-mutex/config.yaml \
  --output runs/dijkstra-mutex \
  --target-score 100
```
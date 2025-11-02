Also an example from TLA examples, but without a PlusCal section (less change of recitation?)

```bash
uv run openevolve-run \
  examples/missionaries-and-cannibals/initial_program.tla \
  examples/missionaries-and-cannibals/evaluator.py \
  --config examples/missionaries-and-cannibals/config.yaml \
  --output runs/missionaries-and-cannibals \
  --iterations 50 \
  --target-score 100
```

```bash
uv run python openevolve/scripts/visualizer.py --path runs/missionaries-and-cannibals/checkpoints/checkpoint_20
```
Also an example from TLA examples, but without a PlusCal section (less change of recitation?)

```bash
openevolve-run \
  examples/missionaries-and-cannibals/initial_program.tla \
  examples/missionaries-and-cannibals/evaluator.py \
  --config examples/missionaries-and-cannibals/config.yaml \
  --output runs/missionaries-and-cannibals5 \
  --target-score 100
```

```bash
uv run python openevolve/scripts/visualizer.py --path runs/missionaries-and-cannibals6/checkpoints/checkpoint_4
```



```bash
uv run python -m openevolve.cli \
  examples/missionaries-and-cannibals/initial_program.tla \
  examples/missionaries-and-cannibals/evaluator.py \
  --config examples/missionaries-and-cannibals/config.yaml \
  --output runs/missionaries-and-cannibals \
  --iterations 50 \
  --target-score 100
```
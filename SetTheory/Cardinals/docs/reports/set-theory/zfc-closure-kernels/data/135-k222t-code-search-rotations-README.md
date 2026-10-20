# Scoped single-rotation screen

This directory preserves one completed, finite source-layout experiment. It is
supplementary research evidence; it is not needed to verify either delivered
222-state machine.

The frozen input is a reparenthesization of Seed-G222 that exposes a closed
206-instruction block at the original primitive interval `[3734,3940)`. Its
complete primitive word and guarded source CFG agree with Seed-G222, and its
literal table passes the finite intended decoder-role check. **This exploratory
input did not receive a fresh full unbounded binary-runtime replay.** The
certified Seed-G222 table remains the separate file in `machines/seed/`.

The screen considers one global associativity rotation of each distinct source
subtree, in either direction, and requires all three factors to be closed. It
found exactly **193** eligible rotations:

| Source DAG nodes | Maximum zero run | Rotations |
|---:|---:|---:|
| 208 | 6 | 30 |
| 208 | 7 | 47 |
| 209 | 6 | 81 |
| 209 | 7 | 35 |

Only the 30 layouts with at most 208 DAG nodes and zero run at most six were
passed to the inherited origin-based compiler. Of those, 22 passed the finite
check that each decoder reaches its intended source role; their best state
count was **222**. The accepted exploratory layouts were not subjected to full
unbounded instruction-runtime checks.

These results exclude a saving only within this exact, finite search family
and compiler allocation rule. **They are not a lower bound on Turing-machine
size, source encodings, or other rotations and compiler choices.**

## Files

- `scan_closed_rotations.py`: portable standard-library search script.
- `input_sites.json`: frozen exploratory source.
- `input.k.tm`: frozen exploratory table, in inherited K labels.
- `screen.json`: full record of the completed 193-rotation screen.

The source SHA-256 is
`1250c157996eb9a626df0161556637a3c99091e86bf1cf7593be8872da49650f`.
The table SHA-256 is
`3f9b36f48088c15af7e773ddaad9d227105ab1f0f78d909635bdb47d1e55f2f3`.

## Optional replay

From the package root:

```sh
python3 -B code/search/rotations/scan_closed_rotations.py \
  --support-dir code/support \
  --source code/search/rotations/input_sites.json \
  --table code/search/rotations/input.k.tm \
  --output code/search/rotations/replayed_screen.json
```

All paths are explicit arguments. The script records the supplied input hashes
and uses only the bundled support modules. A replay is an optional research
operation; it is separate from the package's certified-machine reproduction.

# Four separately released application commands

CWD: Computability/DiophantineConsistency. First commands were sequential;
fresh read-only commands ran concurrently. Every actual process exited0.

```sh
python -B research/fast-sparse-substitution-replay/replay.py --output /tmp/round16-fast-sub-normal.json --old-output /tmp/round16-fast-sub-normal-old.json > /tmp/round16-fast-sub-normal.stdout 2> /tmp/round16-fast-sub-normal.stderr
python -O -B research/fast-sparse-substitution-replay/replay.py --output /tmp/round16-fast-sub-optimized.json --old-output /tmp/round16-fast-sub-optimized-old.json > /tmp/round16-fast-sub-optimized.stdout 2> /tmp/round16-fast-sub-optimized.stderr
python -B research/fast-sparse-substitution-replay/replay.py --output /tmp/round16-fast-sub-root-normal.json --old-output /tmp/round16-fast-sub-root-normal-old.json > /tmp/round16-fast-sub-root-normal.stdout 2> /tmp/round16-fast-sub-root-normal.stderr
python -O -B research/fast-sparse-substitution-replay/replay.py --output /tmp/round16-fast-sub-root-optimized.json --old-output /tmp/round16-fast-sub-root-optimized-old.json > /tmp/round16-fast-sub-root-optimized.stdout 2> /tmp/round16-fast-sub-root-optimized.stderr
```

Retained evidence comprises all16 whole files, including empty stderr.
No process identifier or elapsed time is inserted into application receipts.
Root observations retain their actual session identifiers separately.

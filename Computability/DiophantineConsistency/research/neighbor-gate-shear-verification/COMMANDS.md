# Actual first and fresh fixed-neighbor commands

ROOT observed all nine commands actually exit0, sequentially from the repository
root under separate first/fresh releases. All captures are preserved verbatim
under captures/. These historical command strings are inert and are not rerun
by assembly. Closure is separately released in d9f4a110da.

```sh
python3 Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/build.py --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-build.json > /tmp/neighbor-gate-shear-build.stdout 2> /tmp/neighbor-gate-shear-build.stderr
```

```sh
python3 Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/check.py --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-check.json > /tmp/neighbor-gate-shear-check.stdout 2> /tmp/neighbor-gate-shear-check.stderr
```

```sh
python3 -O Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/check.py --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-check-optimized.json > /tmp/neighbor-gate-shear-check-optimized.stdout 2> /tmp/neighbor-gate-shear-check-optimized.stderr
```

```sh
python3 Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/build.py --check --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-rebuild.json > /tmp/neighbor-gate-shear-rebuild.stdout 2> /tmp/neighbor-gate-shear-rebuild.stderr
```

```sh
python3 -O Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/build.py --check --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-rebuild-optimized.json > /tmp/neighbor-gate-shear-rebuild-optimized.stdout 2> /tmp/neighbor-gate-shear-rebuild-optimized.stderr
```

```sh
python3 Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/check.py --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-root-check.json > /tmp/neighbor-gate-shear-root-check.stdout 2> /tmp/neighbor-gate-shear-root-check.stderr
```

```sh
python3 -O Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/check.py --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-root-check-optimized.json > /tmp/neighbor-gate-shear-root-check-optimized.stdout 2> /tmp/neighbor-gate-shear-root-check-optimized.stderr
```

```sh
python3 Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/build.py --check --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-root-rebuild.json > /tmp/neighbor-gate-shear-root-rebuild.stdout 2> /tmp/neighbor-gate-shear-root-rebuild.stderr
```

```sh
python3 -O Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/build.py --check --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-root-rebuild-optimized.json > /tmp/neighbor-gate-shear-root-rebuild-optimized.stdout 2> /tmp/neighbor-gate-shear-root-rebuild-optimized.stderr
```


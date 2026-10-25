# Exact held commands for the fixed two-neighbor shear

**NOT RUN.** No new/adopted module or helper may be imported, compiled,
AST-parsed or executed during preparation. Two complete static approvals
on the final held seal and a separate ROOT release are required before
commands1–5. Commands6–9 require their own later separate ROOT release.
Run only from the repository root after the applicable exact release.

Before command1 authenticate the whole held seal, all pins/whole trees
and a complete external input snapshot. The data directory and all27
capture paths below (28 paths in total) must be absent. Each command
must exit0 with a complete PASS JSON equal to its entire stdout before
advancing. Preserve full stdout/stderr and every warning. Stop on the
first failure or interruption; do not repair, retry, delete or reseal.

1. One normal materialization, exactly13 external canonical data files:

```sh
python3 Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/build.py --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-build.json > /tmp/neighbor-gate-shear-build.stdout 2> /tmp/neighbor-gate-shear-build.stderr
```

2. Complete normal independent verification, all92 negative/12 valid controls:

```sh
python3 Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/check.py --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-check.json > /tmp/neighbor-gate-shear-check.stdout 2> /tmp/neighbor-gate-shear-check.stderr
```

3. Complete optimized independent verification, all controls retained:

```sh
python3 -O Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/check.py --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-check-optimized.json > /tmp/neighbor-gate-shear-check-optimized.stdout 2> /tmp/neighbor-gate-shear-check-optimized.stderr
```

4. Pure normal rebuild, all13 canonical objects compared, no data writes:

```sh
python3 Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/build.py --check --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-rebuild.json > /tmp/neighbor-gate-shear-rebuild.stdout 2> /tmp/neighbor-gate-shear-rebuild.stderr
```

5. Pure optimized rebuild, all13 objects compared:

```sh
python3 -O Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/build.py --check --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-rebuild-optimized.json > /tmp/neighbor-gate-shear-rebuild-optimized.stdout 2> /tmp/neighbor-gate-shear-rebuild-optimized.stderr
```

After command5 compare every held/pinned source byte with the original
snapshot. No data, receipts or result/manifest files belong inside the
held source folder. New endpoint acceptance and final inert assembly
are later separate releases, as are the following fresh commands.

## Separately held read-only fresh commands

Keep every first capture intact. Before fresh execution all12 following
capture paths must be absent and held/input/data snapshots unchanged.
Stop at first failure. Compare each WHOLE same-mode JSON/stdout/stderr
triple byte for byte with its first counterpart; retain every warning.
No path or first/fresh label is serialized into the JSON.

6. Fresh complete normal independent verification:

```sh
python3 Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/check.py --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-root-check.json > /tmp/neighbor-gate-shear-root-check.stdout 2> /tmp/neighbor-gate-shear-root-check.stderr
```

7. Fresh complete optimized independent verification:

```sh
python3 -O Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/check.py --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-root-check-optimized.json > /tmp/neighbor-gate-shear-root-check-optimized.stdout 2> /tmp/neighbor-gate-shear-root-check-optimized.stderr
```

8. Fresh pure normal rebuild:

```sh
python3 Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/build.py --check --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-root-rebuild.json > /tmp/neighbor-gate-shear-root-rebuild.stdout 2> /tmp/neighbor-gate-shear-root-rebuild.stderr
```

9. Fresh pure optimized rebuild:

```sh
python3 -O Computability/DiophantineConsistency/research/neighbor-gate-shear-finite/build.py --check --data /tmp/proveit-neighbor-gate-shear-data-v1 --receipt /tmp/neighbor-gate-shear-root-rebuild-optimized.json > /tmp/neighbor-gate-shear-root-rebuild-optimized.stdout 2> /tmp/neighbor-gate-shear-root-rebuild-optimized.stderr
```

No extra materialization, path change, retry, old application/native
replay, new calibration, Lean, maintained-page or TeX/PDF action is
authorized. Inclusion of exact commands is a held plan, not a release.

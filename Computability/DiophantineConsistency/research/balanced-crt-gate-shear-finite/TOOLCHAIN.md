# Held commands: exact fixed balanced shear only

**NOT RUN.** Do not import, compile, AST-parse or execute new/adopted
modules or helpers during preparation. Two full static approvals on the
final held seal and a separate ROOT first-execution release are required.
Run from the repository root only after that release.

Before command1, authenticate the final held seal and complete pins.
The entire data destination and all27 first/fresh receipt/stdout/stderr
paths below must be absent:28 paths in total. Preserve exact hashes of all inputs outside the
held folder. Each command must finish with exit0 and a complete PASS
receipt equal to its entire stdout before advancing. Stop on the first
failure or interruption. No repair, retry, deletion or resealing is
authorized by these commands. Historical files must be preserved.

1. Materialize exactly13 new external data files, normal mode:

```sh
python3 Computability/DiophantineConsistency/research/balanced-crt-gate-shear-finite/build.py --data /tmp/proveit-balanced-crt-shear-data-v1 --receipt /tmp/balanced-crt-shear-build.json > /tmp/balanced-crt-shear-build.stdout 2> /tmp/balanced-crt-shear-build.stderr
```

2. Complete independent normal verification and all controls:

```sh
python3 Computability/DiophantineConsistency/research/balanced-crt-gate-shear-finite/check.py --data /tmp/proveit-balanced-crt-shear-data-v1 --receipt /tmp/balanced-crt-shear-check.json > /tmp/balanced-crt-shear-check.stdout 2> /tmp/balanced-crt-shear-check.stderr
```

3. Complete independent optimized verification and all controls:

```sh
python3 -O Computability/DiophantineConsistency/research/balanced-crt-gate-shear-finite/check.py --data /tmp/proveit-balanced-crt-shear-data-v1 --receipt /tmp/balanced-crt-shear-check-optimized.json > /tmp/balanced-crt-shear-check-optimized.stdout 2> /tmp/balanced-crt-shear-check-optimized.stderr
```

4. Pure normal rebuild, all canonical data compared, no new data writes:

```sh
python3 Computability/DiophantineConsistency/research/balanced-crt-gate-shear-finite/build.py --check --data /tmp/proveit-balanced-crt-shear-data-v1 --receipt /tmp/balanced-crt-shear-rebuild.json > /tmp/balanced-crt-shear-rebuild.stdout 2> /tmp/balanced-crt-shear-rebuild.stderr
```

5. Pure optimized rebuild, all canonical data compared:

```sh
python3 -O Computability/DiophantineConsistency/research/balanced-crt-gate-shear-finite/build.py --check --data /tmp/proveit-balanced-crt-shear-data-v1 --receipt /tmp/balanced-crt-shear-rebuild-optimized.json > /tmp/balanced-crt-shear-rebuild-optimized.stdout 2> /tmp/balanced-crt-shear-rebuild-optimized.stderr
```

Read and preserve every warning and complete stderr even on success.
After command5 verify all held and pinned input bytes unchanged. No new
result metadata, data, receipt or MANIFEST belongs inside this held
folder. Any later inert closure, fresh run or endpoint acceptance needs
a separate ROOT release. No maintained page, TeX/PDF, Lean or source
parent modification is within this toolchain.

## Separately held fresh ROOT commands

The initial checkpoint11444fb3... and both full first static findings
are preserved in27950a82da. The bounded source repair released in
1dd9d6aae4 adds only these four read-only receipt routes. No application
has run. The first five commands remain subject to two full final
static approvals and a separate first-execution release. The following
four commands require their own later separate ROOT release; inclusion
here is a plan, not execution authorization.

Keep all first JSON/stdout/stderr files at their original paths. Before
fresh execution, all twelve following capture paths must still be absent
and the complete held/input/data snapshot must authenticate unchanged.
Stop at the first failure without repair/retry. Each complete fresh
JSON/stdout must equal its first same-mode counterpart byte for byte;
compare all stderr and retain every warning. No pathname is inserted
into the mathematical JSON by choosing a fresh receipt.

6. Fresh complete normal verification:

```sh
python3 Computability/DiophantineConsistency/research/balanced-crt-gate-shear-finite/check.py --data /tmp/proveit-balanced-crt-shear-data-v1 --receipt /tmp/balanced-crt-shear-root-check.json > /tmp/balanced-crt-shear-root-check.stdout 2> /tmp/balanced-crt-shear-root-check.stderr
```

7. Fresh complete optimized verification:

```sh
python3 -O Computability/DiophantineConsistency/research/balanced-crt-gate-shear-finite/check.py --data /tmp/proveit-balanced-crt-shear-data-v1 --receipt /tmp/balanced-crt-shear-root-check-optimized.json > /tmp/balanced-crt-shear-root-check-optimized.stdout 2> /tmp/balanced-crt-shear-root-check-optimized.stderr
```

8. Fresh pure normal rebuild:

```sh
python3 Computability/DiophantineConsistency/research/balanced-crt-gate-shear-finite/build.py --check --data /tmp/proveit-balanced-crt-shear-data-v1 --receipt /tmp/balanced-crt-shear-root-rebuild.json > /tmp/balanced-crt-shear-root-rebuild.stdout 2> /tmp/balanced-crt-shear-root-rebuild.stderr
```

9. Fresh pure optimized rebuild:

```sh
python3 -O Computability/DiophantineConsistency/research/balanced-crt-gate-shear-finite/build.py --check --data /tmp/proveit-balanced-crt-shear-data-v1 --receipt /tmp/balanced-crt-shear-root-rebuild-optimized.json > /tmp/balanced-crt-shear-root-rebuild-optimized.stdout 2> /tmp/balanced-crt-shear-root-rebuild-optimized.stderr
```

These commands introduce no extra materialization and write only four
distinct fresh receipts plus their complete stdout/stderr captures.
Final inert closure/acceptance remains a later separately released step.

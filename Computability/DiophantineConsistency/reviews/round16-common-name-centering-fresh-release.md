# ROOT release of four fresh fixed-centering checks

All five exact commands from the original separate release passed on
their first attempts, with no edits or retries. ROOT inspected all five
full JSON/stdout pairs and the complete checker result; normal/optimized
checker records differ only in their optimization flag. Both modes pass
64 negative/four valid controls,58 shifts per profile, two signed fixtures
per profile and full quartic reverse substitution. Pure rebuilds match
all13 data files. The actual points are plain316/218/5737 and weighted
315/217/5743, both degree4, height128446 and row height256.

ROOT freshly authenticated the exact held core
`cdcec19a06bf8f5353952f45783ece8a174b370db4cfd2524c29b2a2a59ac87e`,
all108 external pins and all three whole parent inventories. The complete
pre-replay snapshot is externally saved at
`/tmp/round16-centering-root-pre-replay-snapshot.json`.

ROOT explicitly releases these four fresh read-only checks from repository
root. Retain full JSON/stdout/stderr externally at matching stems; compare
all eight complete JSON/stdout byte strings with the corresponding author
CHECK/CHECK_OPTIMIZED/BUILD_VERIFY/BUILD_VERIFY_OPTIMIZED records. The two
checker runs are independent reads with distinct receipts and may run
concurrently; the two pure rebuild checks likewise have no shared write.
Stop dependent work on any failure. Frozen inputs and all13 data files
must remain byte-identical to the snapshot. No search, optimizer, optional
shift, code edit, new compiler/native proof or Lean work is authorized.

```sh
python -B Computability/DiophantineConsistency/research/round16-common-name-centering/check.py --output /tmp/round16-centering-root-check.json
python -B -O Computability/DiophantineConsistency/research/round16-common-name-centering/check.py --output /tmp/round16-centering-root-check-optimized.json
python -B Computability/DiophantineConsistency/research/round16-common-name-centering/build.py --check --output /tmp/round16-centering-root-build-check.json
python -B -O Computability/DiophantineConsistency/research/round16-common-name-centering/build.py --check --output /tmp/round16-centering-root-build-check-optimized.json
```

Final result/author metadata and whole-inventory closure still require a
separate ROOT release after all four actual exits, eight byte comparisons
and full snapshot equality pass. This release neither accepts an unrun
result nor changes the maintained equation.pdf/TeX or the Lean pause.

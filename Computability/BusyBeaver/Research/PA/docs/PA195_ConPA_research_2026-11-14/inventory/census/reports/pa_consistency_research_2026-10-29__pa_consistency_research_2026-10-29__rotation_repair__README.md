# Rejected rotation fold: bounded repair research

**No accepted 207-state machine was obtained.** `rejected207.native.tm` is an experimental table which fails the finite interpreter replay. Its filename is a state census, not a correctness claim.

## Reproduction

This directory is self-contained. The original class-A Three-cell U208 native table, exact source map, and source-language utilities are in `inputs/`. The C++ finite replay engine and Python adapter are in `vendor/`.

Compile the replay adapter once:

```bash
c++ -O3 -std=c++17 -shared -fPIC vendor/finite_fast.cpp -o vendor/lib_finite_fast.so
```

Then run, from this directory or by absolute script path:

```bash
python3 repair_rotation.py
python3 repair_rotation_two.py
python3 replay_counterexamples.py
```

The first two searches take roughly 40 seconds and four minutes, respectively, in the preparation environment. The last needs only Python's standard library and runs independently of the compiled adapter. Run it before or after the searches; all required input files are supplied. Search outputs overwrite their corresponding saved results.

## Construction and search scope

Starting with the exact supplied Three-cell native U208 table, reassociate the source factors at state pairs `(155,85)` and `(52,154)`, both through their read-zero child, then identify the now-identical states 85 and 154 by retaining 85. The source instruction/ordinal graph remains the same, but shared physical arithmetic entries are affected.

The resulting 207-state table first fails the finite replay at source ordinal 25, a zero-valued `CD 1`. The replay adapter requires the exact expected whole-tape canonical frame within 100,000 literal steps. Each source instruction is tested with all nine registers zero, one zero spare, and gap zero; a decrement additionally has a positive test with its operand equal to one. Thus a complete pass would cover 5,084 guarded cases. It would remain finite evidence, not a universal interpreter proof.

The single-row screen considered seven rows on the known arithmetic-entry path plus 101 rows outside the collected read-preserving source-prefix footprint: 108 rows in total. For each, it tried every alternative write bit, L/R direction, and target among the 207 retained states or halt. This gives 831 alternative actions per row, **89,748 mutation evaluations**. Of these, 434 passed the original ordinal-25 zero prefilter, but none passed the whole guarded corpus. Nineteen patches advanced the first failing source ordinal to 70; for example, `152/0: 0L159 → 0L133`.

For each of those 19 first patches, the two-row screen selected 30–35 possible second rows from the ordinal-70 zero-case trace through its first visit back to dispatcher 84. It again tried all 831 alternative actions per selected row, skipping the already modified first row. In total, **516,051 two-row mutation evaluations** were tested. The ordinal-70 zero prefilter accepted 20,723 evaluations; none passed the whole guarded corpus. The best 19 combinations all additionally changed `147/1` to `1R12`, advancing the first failing ordinal to 311. This was a heuristic footprint restriction, not an exhaustive search over all two-row modifications.

The prefilter intentionally checks only the zero guard; the final finite screen checks both decrement guards. In particular, the best one-row repair's failure at ordinal 70 is its positive guard, with register 5 equal to one. A first return to dispatcher state 84 can carry a temporary, invalid source address and need not be a macro endpoint. It must not be interpreted as the next canonical source state without checking the complete tape.

## Bounded failure artifacts

`replay_counterexamples.py` freshly reproduces the failed ordinal-25 zero case and the repaired ordinal-70 positive case. It records their first dispatcher visits for diagnosis, then checks that neither reaches its exact expected macro frame in the first 100,000 literal steps. `counterexamples.json` explicitly distinguishes these finite failures from unbounded non-equivalence. The prefix decoded at an intermediate dispatcher visit can have stray address bits and is not claimed to be a valid canonical source return.

These checks reject the examined candidates for the existing finite replay gate. They do not prove that the rejected tables have a different blank-input halting behavior, that no longer macro simulation exists, or that no two-row repair exists outside this search family.

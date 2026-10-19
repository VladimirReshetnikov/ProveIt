# Guarded-continuation state-fold screen

This experiment uses a complete, clean output tape and exact primary registers,
but accepts any decoded continuation in the certified guarded class whose
silent-control rank is no greater than the intended successor's rank.
The mathematical sufficiency theorem is in the main report. The fixtures are
finite discovery tests, not universal runtime proofs.

From the archive root:

```sh
mkdir -p verification/bin
c++ -O3 -std=c++17 experiments/continuation/quotient_search.cpp -o verification/bin/quotient_search
verification/bin/quotient_search vendor/context246/machine/zfc_prefix246_old.tm experiments/continuation/decoder.txt experiments/audit_inputs/quotient_cases.txt mixed
```

The command reads the pinned original-label table (one initial comment line),
the exact fully unfolded decoder, and all 8,391 fixtures. The `mixed` mode tries
180,075 recipes: identify one non-dispatch working state with another and keep
the target's rows or either of the two mixed source/target row combinations.
The opposite full-row choice occurs through the opposite ordered pair.
All recipes reject in this bounded acceptance screen. The log records 773,357
case executions and 553,597,150 literal transitions including the baseline.

Bounds: a 512-cell tape window; initial head offset 128; at most 4,000 transitions
and 15 intermediate dispatch returns per case. An out-of-window access, missing
transition, malformed frame, guard/register mismatch, or exhausted limit rejects.
No accepted candidate or lower bound on arbitrary Turing machines follows.
The source graph certificate itself is exact and independently audited.

# Recovered auxiliary square/product82 science packet

This packet reconstructs the author proof and independently authored
bounded checker after the filesystem reset. It has fresh hashes and fresh
normal/optimized execution evidence. It does not claim byte identity with
the lost author files. `HISTORICAL_LOST_RELEASE.json` preserves the old
reported hashes only as historical metadata.

`COUNTERFAMILY.md` proves the complete strictly positive all-input
counterfamily for every unchanged genuine compiler slice. The result is
specific to the auxiliary square/product82 at commit
6ce2dcaaf49d28de43ce9396a094643308fb0595, distinct from the first-index-
deleted82 and free-coefficient83 candidates.

## Exact replay, from any working directory

    python3 /absolute/path/check_counterfamily.py --expect /absolute/path/CHECKS.json
    python3 -O /absolute/path/check_counterfamily.py --expect /absolute/path/CHECKS.json
    python3 /absolute/path/check_tamper.py --expect /absolute/path/TAMPER_CHECKS.json
    python3 -O /absolute/path/check_tamper.py --expect /absolute/path/TAMPER_CHECKS.json

Only the standard library is needed. Upstream Python and saved arithmetic
rows are never imported, executed or interpreted as a schedule. All eight
immutable snapshots are authenticated by SHA256; all 82 rows are compared
as static data. The five symbolic identities are evaluated solely from
new handwritten formulas.

The bounded arithmetic checks cover:

- 1,683 outer CRT/packing cases, 561 in each residue/sign branch
- 70 exponent-choice residue cases and five 8/9-exponent cases
- 21 small exact Pell families and 63 shared-input loads
- 180 direct auxiliary extensions, including 90 even-c cases
- 150 shared-projection recurrence checks
- Three optimized tamper checks, including False-to-zero type confusion

Large outer fixtures never form X=2^p or any associated Pell coordinate.
Their diagnostic numerals are not presented as actual compiled programs.
Small Pell fixtures test components only. The unbounded theorem and
empty-set language consequence follow from the proof, not finite search.

`CHECKS.json` pins the fresh proof/checker and source snapshots.
`MANIFEST.json` lists every current packet file except itself. Normal and
optimized logs are retained. No public repository changes or uploads were
made as part of this recovery.

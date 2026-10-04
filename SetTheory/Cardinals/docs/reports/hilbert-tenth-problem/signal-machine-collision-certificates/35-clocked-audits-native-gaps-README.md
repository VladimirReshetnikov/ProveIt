# Native-gap continuation: independent audit

**Verdict: PASS, accepted as stated.** Read `INDEPENDENT_AUDIT.md` for the source-bound mathematical audit and its limitations.

The candidate proof and manifest are pinned in the checker. No candidate code, upstream scientific code, Lean build, physical simulator, saved collision schedule or counter-machine interpreter was executed. All candidate files remain unchanged.

Contents:

- `INDEPENDENT_AUDIT.md`: all-input proof review, exact counts, POWER adapter, normalization and qualifications
- `check_native_gap.py`: independently authored and inspected Python standard-library checker
- `run-1/receipt.json`: passing static arithmetic, source pins and before/after metadata check
- `run-1/power-fixtures.json`: complete positive POWER assignments for C=1 and C=2
- `PORTABILITY.json`: successful relocated replay comparison
- `ORIGIN_COMPARISON.json`: byte identity of all eight retained copies against stated origins
- `AUDIT_MANIFEST.json`: dossier file hashes, excluding itself

Use Python 3.9 or newer. Run from any directory, supplying the unchanged candidate and a new output location outside it:

    python check_native_gap.py --source PATH_TO_CANDIDATE --output NEW_EXTERNAL_DIRECTORY

The recorded run checks 30 full symbolic instances, 27 full native assignments, 16,641 primitive normalizations, 49,923 scaled decodings, and all 142,880 positive gap triples of total scale at most 96. Full positive POWER assignments include semantic exponents zero and one. These are finite supporting checks; all-exponent equivalence still uses the explicitly retained Pell theorem pair. The physical corollary still uses the retained compiler theorem.

No new report number or delivery is implied by this audit.

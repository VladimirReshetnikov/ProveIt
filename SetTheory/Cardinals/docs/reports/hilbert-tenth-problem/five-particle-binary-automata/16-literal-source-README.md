# Literal universal reversible two-counter source

This new package materializes the source missing from the existing reversible
binary-five compiler. It does not change that compiler or any earlier release.

- `source.json`: strict `reversible-two-counter-v1`, 122,622 controls,
  141,561 fully expanded rows, cut J=0
- SHA-256: `38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a`
- Primitive operation counts: 33,436 increments, 32,630 decrements,
  23,429 zero tests, 52,036 positive tests, 30 identities
- Global partial injection on every natural counter pair; no incoming START,
  no outgoing HALT
- Universal clean input: `(START, C·2^L·3^R·5^T,0)` with naturals L,R,T,
  positive C coprime to2310. The standard tape loader sets T=0,C=1
- History and work are encoded in primes7 and11 during execution; their
  initial exponents are0. Do not reuse the old “every raw positive input” promise

## Read first

`PROOF.md` gives the exact theorem, primary-table/finite-input checks, every
layer’s composition argument, scope, and practical limits.
`independent-macro-audit.md` gives the independently checked macro invariants,
ranks, joins, and exact clocks. This is an ordinary mathematical proof with
executable checks, not a proof-assistant formalization or a record claim.

## Reproduce

Requires only Python3’s standard library. Run from this directory:

    python check_primary_table.py
    python verify_virtual3.py
    python validate_source.py
    python verify_affine.py
    python independent_audit.py
    python test_loader.py
    python test_concrete.py

`python build_source.py` regenerates all literal stages and certificates from
the pinned bundled three-counter input. Verify the source hash afterward.
The old nonreversible8408-row table is not an input to this construction.

`python loader.py --left 101 --right 01 --particles` converts finite
nearest-head-first half tapes, with scanned bit0 and omitted blank tails.
Its CLI uses hexadecimal strings to avoid interpreter decimal-digit limits;
its Python APIs return exact integer counters/coordinates. The public
five-particle loader rejects unclean inputs and derives constants only from
the SHA256-pinned source. It accepts no caller-supplied ledger override.

## What was actually checked

- Primary Table16: all30 cells independently compared; printed112 confirms
  initial scanned c=0 in the finite universal input family
- 437 affine paths cover all528 original three-counter rows
- 54,084 affine paths cover every5,451 reversible-five and141,561 two-counter row
- Independent whole-graph reconstruction of every compilation stage;
  all-domain source/image disjointness, plus27,743 prime and2,330 history traces
- Separate indexed strict-schema validator checks every emitted row using
  exact finite classes; no quadratic cross-product of controls and rows
- Public loader rejection tests and literal small-macro/fresh-entry replays

Morita1996 primary text was available but its scan screenshots were not.
All used graphs were independently proved, rather than trusting ambiguous OCR.
This limitation is recorded explicitly, not represented as visual verification.

## Additional corollary

For proper tape-loader inputs, the base five-particle CA is periodic or has a
positive return exactly when U halts, with least period2Theta+2. Here Theta
counts CA microedges, not literal source steps. The fixed-CA five-particle
return problem is r.e.-complete. Report12’s separate mass-at-most-four exact
reachability theorem gives decidability below5 via reachability fromF(x) to x.
See PROOF.md Section8 and periodicity-audit.md for scope and dependency hashes.

All proof-checker conditions remain active under Python−O; run_checks.py
replays every checker in normal and optimized modes.

## Binary-five compiler boundary

The unchanged reference schema, proof, and implementation are copied under
`compiler-reference/`. `target-ledger.json` is derived from its formulas,
not from constructing the eager object. This source entails269,291,358,255
local involution factors and radius bound3,292,955,588,459,274,804. The
old eager `compile_source` was NOT executed on the universal table. A full
CA truth table/factor array is not materialized. The fixed finite CA is
specified by its indexed construction and this explicit finite source.

Even the empty-tape prologue has a theorem-derived two-counter cost of
79,936,151,060,302. `prologue-predicted-clocks.json` records exact composed
clocks, not traversed traces. The proof uses terminating macro invariants;
finite tests do not establish universality by themselves.

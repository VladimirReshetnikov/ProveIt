# Independent exact-fusion audit

## Verdict: PASS

The candidate `fusion_source.py`, SHA-256
`5e433001dcdb4a26f7dcb0419a41f124fae983aeb76088d55d4b603802232f60`,
preserves the entire Report47/Report44 final integer polynomial for every
assignment of the same coordinates. This verdict is supported by a generic
ordinary-polynomial proof, exhaustive fixed-coefficient checks, exact polynomial
checks of the paid weights, and independent complete-source reconstruction.
It does not rely on modular samples, a quotient ring, W being nonzero, or W^S=1.
No issue or blocker was found. The original ant-dynamics assumptions are inherited,
not re-proved or strengthened.

The two-input source has 5,971,120 multiplications and 8,687,814
additions/subtractions, totaling **14,658,934 operations**.
The one-input source has 5,971,124 multiplications and 8,687,820
additions/subtractions, totaling **14,658,944 operations**.
Relative to the corresponding frozen Report47 joined source, each saves
**16,729,897 operations** (53.2989% for the two-input source).

## Independent proof and exact coefficient evidence

`GENERIC_PROOF.md` was written before running the verification scripts.
It proves the correction identity over a polynomial ring with independent formal
Q and T coefficients, then proves fixed-block grouping, finite geometric weights,
phase alignment, tile assembly, and the final full-source substitution.

- S=576000 is exactly the old initializer's V; the physical macro height is
  separately L=240619037200. There is no accidental dimension substitution.
- The reflection is j=(288650-x) mod576000. The second macro is represented by
  phase288000, as required by Full[x-288000].
- The bands are precisely dx0..50, 51..650, and651..1199. Their local exponent
  is 50+600b-dx and their block exponent is (480-b-s-phase/600) mod960.
- All 9,187,200 formal correction term identities across four operations, both
  phases, all957 occurrences and all1200 dx positions were checked, including
  zeros. All4800 signed Q masks came directly from the frozen data.
- All 6,912,000 entries of H/B/F/Hlow/Hhigh/first across both phases were checked
  against the frozen data. Every block group is exact, disjoint, and exhaustive.
- Distinct block counts for either phase are H5, B4, F6, Hlow3, Hhigh5, first4.
  The half phase is exactly a rotation of block positions by480.
- All18 actually used weight polynomials were evaluated exactly in Z[W], with
  their complete sparse coefficient dictionaries compared to sum_(k in J)W^(600k).
  All10 used geometric lengths were checked as exact pairs (Y^n,sum Y^i).
  These are symbolic coefficient checks, not numeric samples or modular tests.

All modulo operations act on fixed indices before evaluation. All W exponents
are nonnegative ordinary exponents. The proof therefore includes W=0,1,-1
without exceptions or assumptions. The final scalar-polynomial equality follows
by applying the proven coefficient identities and induction on retained gates.

## Cache and paid-arithmetic audit

All requested profile-cache keys are contained in the explicitly constructed
838 nonzero keys: 736 of width400,21 of width25,81 of width375. Thus calls through
the prefix-owned profile cache cannot append an unpaid or misplaced profile gate
during fusion. Spatial block caches live within one Fusion object with one fixed
W; weight/power/geometric caches live within that same object with Y=W^600.
Identical wire tuples are safe exact sharing keys, and zero/one aliases are paid
or permitted literals.

The independent closed ledger confirms the fixed-block stage:

- 26 spatial Horner blocks, each599M+599A
- 37 block/group products and29 group-sum additions
- 119M for cached Y powers
- 168M+104A for cached finite geometric pairs
- 13 run products and7 run-sum additions
- Total15,911M+15,714A

All other fused stages were actually generated and counted. The spatial source
is92,107 operations; the retained constant prefix is14,563,366 operations.
No multiplication by a zero or one coefficient is silently discounted from an
emitted Horner recurrence.

## Complete-source audit

`audit_exact.py` implements its own literal-source validator, counter, hasher,
and splice adapter. It reconstructs the candidate streams using fixed audited
old-main intervals, rather than reusing the candidate interval recognizer.
The frozen own arithmetic generators were authenticated before reuse; no
upstream physical ant, color-recipe, or saved-schedule implementation ran.

The exact removed half-open old-gate intervals are:

- Tile: [1264,1153262),1,151,998 gates
- First: [1153262,2305260),1,151,998 gates

Every removed record was checked against the dense Horner recurrence. Only each
interval's final output receives a replacement mapping. All other removed
intermediates are invalid references. No outside consumer uses one.
All other old records were translated, preserving their opcodes and references,
including hy*(hx*Tile+Wp*First), all anchors, all residuals, and the complete
sum-of-squares finalizer. The old canonical hashes were regenerated and matched.

Retained old-main gates are3461 for two inputs and3471 for one input. Witness
name lists and order match exactly:465/467. There remain285/286 residual metadata
records and one final equation. All598 surviving constant ports are bound; no
C: operand remains. Literal leaves are only1/3 plus the declared coordinates.
The final right-hand side is paid gate0=1-1.

Independently reproduced complete stream hashes:

- Two inputs: `62cf59e79cd5d3baf61b19ed50ccc8965e8fb4814bbdc33a6d7fad417d379667`
- One input: `722340689ce84f505af7d010db21d6b48178c5d6008b28966e9836aeca75b25b`

Final equations are gate14658933=gate0 and gate14658943=gate0 respectively.
The exact variable degree remains2,304,000 by polynomial equality, rather than
by a potentially cancellation-insensitive syntactic degree estimate.

## Reproducibility and preservation

Run the following in this fresh audit directory:

    python -B audit_exact.py
    python -B audit_caches_weights.py

The first script authenticates its local candidate snapshot against18 frozen
inputs, verifies exact finite identities, regenerates all arithmetic, and writes
`audit-receipt.json`. The second writes `caches-weights-receipt.json`.
`finite-identities.json` records the earlier exact-data checkpoint.
Both scripts prohibit bytecode writes and keep output outside the frozen roots.
All95 frozen Report47 files have identical before/after hashes in
`frozen-before.json` and `frozen-after.json`. The candidate source remained
byte-identical to the audited snapshot after verification. No finalQA file was
modified. The author's separate modular-test receipt is supplementary evidence;
those numeric tests were not substituted for, or claimed as, this independent proof.

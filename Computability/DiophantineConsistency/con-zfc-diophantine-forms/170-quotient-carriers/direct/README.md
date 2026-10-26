# Diagonal growth and an affine radix for Diophantine consistency

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI
assistance. `PROOF.md` is the complete new ordinary arithmetic argument.
The parent arithmetic package, source proofs and calibration interfaces
are retained under `baseline/` with their original notices.

## Selected explicit equations

Each equation is the sum of squares of every quadratic residual in its
`equation.json`. All coordinates range over the unrestricted integers.
Every collected quartic coefficient is supplied in
`expanded_polynomial.json`; no variable exponent occurs in these files.

The later compositions below are the preferred direct endpoints. The
217-variable source pools the exact powers in the diagonal source and uses
the separately supplied strict-horizon proof retained in `diagonal_pool/`.
The 218–220-variable source starts with the unchanged incoming Pooled Powers
225-variable equation. `RADICAL_PROOF.md` supplies the full algebraic argument.
Directory numbers `radical238` and `radical239` identify their source dimensions;
their outputs have 232 and 233 variables respectively.

| Preferred directory | Variables | Residuals | Degree | Collected terms | Height |
|---|---:|---:|---:|---:|---:|
| `pooled217_height5184` | 217 | 154 | 4 | 19,112 | 5,184 |
| `pooled217_height6144` | 217 | 154 | 4 | 18,148 | 5,888 |
| `pooled218_height4576` | 218 | 155 | 4 | 16,706 | 4,544 |
| `pooled218_height6144` | 218 | 155 | 4 | 15,153 | 5,888 |
| `pooled219_height6144` | 219 | 156 | 4 | 8,666 | 5,888 |
| `pooled220_height2736` | 220 | 157 | 4 | 8,847 | 2,336 |
| `pooled220_height4408` | 220 | 157 | 4 | 8,018 | 3,597 |
| `radical238_height4576` | 232 | 168 | 4 | 13,372 | 4,408 |
| `radical239_height4576` | 233 | 169 | 4 | 7,403 | 4,408 |

The suffixes are height thresholds used by the prefix search; actual heights
can be smaller. The exact metrics JSON controls every value in the table.
The original direct profiles remain for provenance and independent review:

| Directory | Variables | Residuals | Degree | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|---:|
| `diagonal238_reduced` | 238 | 174 | 4 | 12,850 | 7,968 |
| `diagonal239_reduced` | 239 | 175 | 4 | 5,089 | 7,968 |
| `diagonal238_centered` | 238 | 174 | 4 | 12,747 | 11,232 |
| `diagonal239_centered` | 239 | 175 | 4 | 5,021 | 11,232 |

The final two centered profiles trade a little support for larger
coefficients. The intermediate `diagonal_raw`, `diagonal238`,
`diagonal239`, and `_balanced` folders make the exact transformations
reviewable. Each selected reduced residual has coefficient magnitude at
most 64. Literal polynomial coefficients have the greater height listed
above because the residuals are squared and collected.

The new unbounded argument gives, through the identified inherited
C222/ZF/ZFC refutation calibration,

    ZFC proves: (P has no integer zero) <-> Con(ZFC).

This establishes the requested equivalence. It does not assert consistency
or inconsistency, a global simplicity minimum, or a new end-to-end formal
proof-assistant build. This is a direct numerical proof-calculus route,
using neither K215 simulation nor Jones's universal polynomial.

## Arithmetic mechanism and priority

The source uses the semantic choices

    t=16+2h^2, F=t^t, R=F,
    y=F(2v+1), q=6z+3, H=3+6*sum(actual CRT representatives).

The power and binomial symbols are proof notation for retained ordinary
polynomial graphs. One diagonal power does three jobs: large evaluation
recovers proof-label multiplicities, its size exceeds the squared lcm
needed by the binomial selector, and its 2-adic divisibility supplies the
cofinal beta construction. The affine radix ensures that both q and q+1
are nonunit before either sign is known. The existing exponent y+1 then
recovers the positivity of the linear beta multiplier, removing its old
square certificate. The proof treats negative q and the boundary y=F.

The pinned incoming `ConZFC_Linear_CRT_2026-10-25.zip` already contains
the choices F=t^t, R=F and y=F(2v+1), with a different sign bootstrap.
These diagonal choices are therefore not claimed as new here. The
q congruent to 3 modulo 6 bootstrap, the elementary even-horizon lcm
bound, and their tested composition are the alternative developed here.
The incoming `ConZFC_Pooled_Powers_2026-10-25.zip` already gives a
225-variable quartic, so these 238/239-variable profiles are not variable
records. `PROVENANCE.json` pins all twelve incoming archives, and
`AUDIT.md` records the comparison and its precise read scope.

## Exact reproduction

Python 3.10 or newer and the standard library suffice:

    python3 -B verify.py
    python3 -B -O verify.py --skip-parent
    python3 -B reproduce.py

The first command includes the retained parent's independent exact
source/guard audit. `--skip-parent` repeats every new finite check while
omitting that unchanged inherited replay. All check conditions use
explicit exceptions, so optimized Python does not silently remove them.
`reproduce.py` reconstructs the nine original diagonal-stage JSON groups in a temporary directory
and compares their complete bytes. It preserves the delivered files.

For the later radical, coordinate-shear, affine and row-basis compositions:

    python3 -B verify_compositions.py
    python3 -B -O verify_compositions.py

This independent audit binds the unchanged source archives and code, replays
the entire finite diagonal-source audit and new pooling checker, replays the
unchanged incoming pooled225 audit and deterministic rebuild in a temporary
directory, reconstructs all exact maps, computes every complete expansion,
checks all coordinate occurrences and runs targeted corruption controls
inherited from the independent projection auditor. The 217-variable stage's
separate strict-horizon/pooled-power proof and independent checker are retained
in `diagonal_pool/`; `POOLED223_SOURCE.json` fixes its exact output. All paths
needed by the checker are relative to this directory. No network is used.

`build.py` and `finish.py` intentionally regenerate the new files in place.
They are not needed for a read-only verification. An optional `--receipt`
path on the verification and reproduction tools records their results.

The independent checker verifies all literal source edits, every one of
the 18 exact-power requests, all 14 principal pairs, all 37 distinct
frame atoms, the inherited Horn factorizations, 203 integral monic
eliminations, translations, coordinate and residual shears, affine
restorations, every collected coefficient, all coordinates' occurrence,
and intentional corruption controls. These exact finite checks do not
replace the unbounded argument in `PROOF.md`.

## Maps and attribution

The raw source changes are in `diagonal_raw/source_delta.json`. The
factorization, monic projection and integer translation certificates are
beside it. Each 238/239-variable endpoint records the inherited six
coordinate shears and three/four affine exposures. The `_balanced`
profiles transfer 34/36 attributed residual-row operations from the
factorial-free parent. The centered profiles translate one integer
coordinate; the reduced profiles add twice one residual to another.
All maps are exact and invertible at the indicated source level, except
that unused private raw coordinates may be freely restored.

The baseline's finite C222 calculus, signed Pell frame, binomial CRT,
normalization and affine exposures are prior work, credited in their
retained sources. Distinct source choices and their proofs are in this contribution;
overlap with the already submitted Linear CRT construction is disclosed above.
Separate review in this workflow is AI-assisted mathematical review,
not external human refereeing. No repository files were changed.

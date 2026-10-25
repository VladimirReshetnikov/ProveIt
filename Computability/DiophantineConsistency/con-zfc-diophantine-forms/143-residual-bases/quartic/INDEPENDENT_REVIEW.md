# Independent mathematical review: quartic row exposure

## Verdict and scope

**PASS.** The five frozen endpoints in `round18/quartic/release` are exact
quartics over unrestricted integers and have bijective integer zero sets
with their stated incoming parents. No mathematical defect was found in
the new transformations, displayed proof, report section, coefficient
data, restoration maps, or selected comparisons.

This review establishes the finite algebra and the ordinary equivalence
argument. The Con(ZFC) interpretation is inherited from the incoming
Cofinal Anchors parent theorem and its identified arithmetic and
C222/ZF/ZFC calibration. It is not a fresh end-to-end Lean build,
consistency test, or global optimality claim.

## Materials inspected before execution

I read the complete release `build.py`, `check.py`, `affine_rank.py` and,
when added, `export_readable.py` before executing them. I also read
`PROOF.md`, `SOURCE_PROVENANCE.json`, `ENDPOINTS.json`, the certificates,
the retained upstream coordinate-shear certificates, and the complete
`report_section.tex` and `README.md`. The top-level report's residual-operation and
unit-affine-projection lemmas agree with the component proof.

For the source boundary, I read the incoming `CLOSURE_MAP.md`, direct
`PROOF.md`, `README.md`, `PROOF_315.md`, `ORIENTATION_FIRST_PROOF.md`, and
`STRICT_BUDGET_PROOF.md`. The three source equations are the final strict
centered endpoints, not the historical 315-variable checkpoint. The
orientation-first interpretation uses actual nonnegative semantic
representatives; it does not falsely restore old shifted coordinates
pointwise. Nothing in the new work requires such a restoration or a
semantic acceptance assumption for the upstream V-R1 endpoint.

The incoming ZIP was independently SHA256-checked as
`1efcb1831b7b57f34385e4171923dd801573b74b4529346b9d153246cd0294e6`.
Every release source is byte-identical to its declared member of that ZIP.
All five retained upstream shear-certificate files match both their
declared hashes and the pinned local upstream copies. Their policies
produce exactly the six recorded shears in exactly the recorded order.
No new source research, remote write, or upstream modification was made.

## Mathematical checks

1. **Coordinate changes.** Each of the six changes is an integral shear
   whose added linear form omits its target. Each inverse is obtained by
   negating its coefficients. I checked the entire composed substitution
   followed by the reverse inverse sequence on every original residual,
   not only each shear in isolation. The composition order matters for
   the `mul.137`, `mul.75`, and `mul.64` targets and is correct.
2. **Exposed rows.** In each of the three sources, the exact transformed
   identities are

       Q21 - Q6 = 4 + 4*x10 + 8*x11 + 4*x21 - x22 + x37,
       Q73 - Q71 - 4*Q70 - 8*Q68
         = 12 - 6*x3 - 8*x84 - 4*x85 - x86 + x89,
       Q122 - Q120 = 3 - 2*x107 + 2*x151 - x167 + x169.

   Their five elementary row operations are unimodular and have unchanged
   donors. The source-to-exposed-row inverse was checked exactly.
3. **Projection.** Every removed row is affine immediately before its
   deletion and its chosen coordinate coefficient is a unit. Every
   replacement is integral, affine, and nonrecursive. Every deleted row
   becomes the zero polynomial, every deleted coordinate disappears from
   all residuals, and no target row or coordinate is deleted twice.
   The three new targets are `add.145`, `mul.346`, and `base4.T`.
   The 278-coordinate endpoint additionally removes the already affine
   `add.380` coordinate using precisely the displayed 16-term formula.
4. **Final row changes.** The final certificates contain respectively
   7, 70, 91, 64, and 65 elementary row shears for the endpoints in the
   table below. Both forward replay and full reverse replay match.
   These alter the sum-of-squares polynomial, not the simultaneous zero
   set; the proof and report correctly distinguish these statements.
5. **Total restoration.** Every original coordinate was independently
   reconstructed as an integral affine polynomial in final coordinates.
   Every original residual pullback equals the corresponding inverse-row
   reconstruction identically. All exported `RESTORATION.json` entries,
   coordinate names, indices and polynomials match these separately
   computed maps. This covers all 282, 282, 282, 287, and 309 original
   coordinates and all 192, 192, 192, 197, and 219 original residuals,
   respectively. The proof therefore establishes both directions for
   every integer zero without relying on sampled solutions.
6. **Full expansion.** Independent all-pairs multiplication and collection
   of every residual square reproduces every coefficient in the expanded
   polynomials. Coordinate bounds, canonical unique monomials, exact
   variable lists, unrestricted integer domains, degrees, row heights,
   row support and all declared metrics were checked. Each polynomial
   has a nonzero degree-four term, and every declared coordinate occurs
   in its collected polynomial.
7. **Readable exports.** The exporter's normal and optimized check-only
   runs pass. Every text and TeX residual parses back to the full sparse
   coefficient list; generated files match their deterministic payloads.

## Recomputed endpoints and comparisons

| Endpoint | Variables | Rows | Degree | Monomials | Height |
|---|---:|---:|---:|---:|---:|
| integer278 | 278 | 188 | 4 | 12884 | 12227 |
| integer279_balanced | 279 | 189 | 4 | 5483 | 7200 |
| integer279_sparse | 279 | 189 | 4 | 5202 | 12662 |
| integer284_sparse | 284 | 194 | 4 | 4270 | 10864 |
| integer306_sparse | 306 | 216 | 4 | 3870 | 14512 |

The recomputed parent tuples `(variables, rows, monomials, height)` are
`(282,192,5491,128446)`, `(287,197,4313,128446)`, and
`(309,219,3922,128446)`. Both 279-coordinate profiles strictly improve all
four varying metrics of the 282-coordinate parent. The 284 and 306 points
strictly improve all four metrics of their matched parents. The 278 point
is correctly described as a variable/support tradeoff, not domination of
the 279 points or of the dimension parent. All five supplied new points
are pairwise nondominated in these four metrics within this selected set.
No assertion about the entire literature or every possible quartic follows.

## Finite row-span obstruction

The rank replay passes: the dimension parent's quadratic-part row rank
is at least 188 modulo 1000003, and the final 188-row endpoint has rank
188 modulo that modulus. I independently checked that 1000003 is prime
by trial division through its integer square root. The four explicitly
independent affine row combinations give parent nullity at least four;
with 192 rows the modular lower bound therefore fixes its rational
quadratic-part rank at exactly 188. The final row map has no nonzero
rational affine row-span consequence. The text correctly limits this to
the current residual span; it does not exclude nonlinear ideal
consequences, different encodings, or smaller quartics.

## Replay evidence

All commands were run against the frozen math files. No Python `assert`
statement is needed for the checks.

```text
python -B round18/quartic/release/check.py --rebuild
python -O -B round18/quartic/release/check.py --rebuild
python -B round18/quartic/release/affine_rank.py
python -B round18/quartic/release/export_readable.py --check
python -O -B round18/quartic/release/export_readable.py --check
python -B round18/review/quartic_independent_audit.py
python -O -B round18/review/quartic_independent_audit.py
```

Both release-checker runs pass, reject all five deliberate corruptions
(affine reconstruction, row shear, coordinate shear, final residual, and
expanded coefficient), and rebuild all equation, polynomial and metrics
files byte-identically. The second audit implementation imports no
release code and independently checks the source pins, displayed
identities, complete maps, expansions and comparisons. Both its normal
and optimized runs pass. An initial reviewer-script reporting error
(`next` applied to a list rather than an iterator) was corrected before
these final runs; it was not an endpoint or producer defect.
The author's final additions checking published restoration maps and
trial-dividing the rank modulus were inspected; the complete normal and
optimized release replays and rank replay were then run again and passed.

Receipts and the separate audit implementation are retained in this
directory as `quartic_normal_replay.json`,
`quartic_optimized_replay.json`, `quartic_rank_replay.json`,
`quartic_exports_normal.json`, `quartic_exports_optimized.json`,
`quartic_independent_audit.py`, `quartic_independent_audit.json`, and
`quartic_independent_audit_optimized.json`. Reviewed release file hashes
are recorded in `quartic_reviewed_hashes.json`.

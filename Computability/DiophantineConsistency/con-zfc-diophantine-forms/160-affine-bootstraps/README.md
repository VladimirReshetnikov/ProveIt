# Affine parameters and a linear CRT selector for Con(ZFC)

**An explicit ordinary quartic in 237 unrestricted integer variables, together with a substantially sparser 238-variable form.**

Prepared for Vladimir Reshetnikov on 25 October 2026. The source snapshot is [ProveIt commit `7a8da414376a80b90ecf799f37ceb26fb9ac674e`](https://github.com/VladimirReshetnikov/ProveIt/tree/7a8da414376a80b90ecf799f37ceb26fb9ac674e).

The ordinary mathematical proof, composed with the retained C222/ZF/ZFC calibration, establishes

\[
\mathrm{ZFC}\vdash
\bigl(\neg\exists\boldsymbol{x}\in\mathbb Z^n\;P_n(\boldsymbol{x})=0\bigr)
\longleftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

Consistency here is syntactic consistency for the repository's recursively presented ZFC proof relation. All coefficients are explicit fixed integers. No coefficient is defined by a consistency decision, and no exponentiation or binomial function occurs as a primitive in a delivered polynomial.

## Results

Every endpoint below has exact degree four and coefficient height 7,968. Height is measured after collecting the entire quartic.

| Endpoint key | Integer variables | Quadratic residuals | Collected monomials | Directory |
|---|---:|---:|---:|---|
| `compact_support` | 239 | 175 | 5,017 | `equations/original_horizon/balanced/` |
| `primary` | 238 | 174 | 5,479 | `equations/horizon8_difference_frame/balanced/` |
| `minimum_dimension` | **237** | **173** | **14,129** | `equations/horizon8_difference_frame/dimension/` |

For each endpoint, the equation is the sum of the squares of all residuals in `equation.json`, set equal to zero. Thus the 237-variable equation is

\[
P_{237}(x_0,\ldots,x_{236})=\sum_{j=0}^{172}S_j(x_0,\ldots,x_{236})^2=0.
\]

The report prints every residual for both the 238-variable and 237-variable equations. The archive also supplies the complete collected coefficients and plain-text residual lists. The retained `original_horizon/dimension` endpoint has 238 variables, 174 residuals and 12,743 monomials at the same height; it is a reproducible control dominated by the new primary endpoint.

This improves the direct small-coefficient quartic family in the inspected snapshot. Other repository constructions use far fewer variables with different degree or coefficient architectures. No global minimum or literature-wide novelty claim is made. The construction uses the numerical C222 proof calculus directly; it does not encode a K215 execution or specialize Jones's universal expression.

## What is new

The final semantic front is

\[
t=8h,\qquad d=t+2,\qquad F=d^t,\qquad R=F,
\qquad y=F(2v+1),\qquad q=4z+1.
\]

The notation `F=d^t` describes what a retained ordinary polynomial power certificate proves. It is not an extra operation in the quartic.

1. **Recover order from the existing certificates.** Because `d=8h+2` is never zero or a unit, the signed power certificate forces `t >= 0`. The two endpoint congruences rule out `t=0`, so `t >= 8`. The nonunit base `q+1=4z+2`, the existing power request with exponent `y+1`, and the first binomial digit then recover the remaining signs in an acyclic order. This permits affine horizon, beta and radix parameters.
2. **Use the growth register as the selector offset.** The generalized binomial CRT selector needs `R >= lcm(1,...,t)^2`, not a square as such. The elementary bound `lcm(1,...,t) <= 4^(t-1)`, with a direct check at `t=8`, proves that `R=F` suffices. Both directions of prime-power coverage are retained.
3. **Bound underlying coordinates once.** Thirty-seven required affine atoms use only 33 underlying coordinates. The integer inequality `abs(c + sum(a_i*u_i)) <= sum(u_i^2) + abs(c) + sum(floor(a_i^2/4))` permits the smaller frame `W=19+sum(u_i^2)`. The exact atom ledger is checked by code. The frame contains no private Pell coordinate.
4. **Replace one orientation error by a difference.** Keeping `e_t` and using `e_(F+t)-e_t` removes a repeated horizon square. The revised pooled error obeys `E < 65 W^2 + 60 < 4 W^3 < abs(A-1)`. Its divisibility therefore still forces every original error to vanish. This is a semantic certificate change; the subsequent exact row transformations are a separate part of the construction.
5. **Collect the polynomial only after exact integral reductions.** Explicit restoration maps account for every eliminated coordinate. A final integral row subtraction removes a repeated `64 h^2` coefficient and keeps the collected height at 7,968.

The report includes the exceptional unit-anchor case, the smaller growth threshold, signed binomial digit recovery, integrality of normalized remainders, label multiplicities, finite derivability closure, and completeness with all parity and cofinality choices. It also records why the tempting further specialization `y=F+1` fails.

## Start here

- `ConZFC_Affine_Bootstraps.pdf`: mathematical report and both complete principal residual lists.
- `report/main.tex`: editable LaTeX source; generated inputs are included.
- `ENDPOINTS.json`: names and paths of the selected equations.
- `equations/`: literal residuals, collected coefficients, source edits, frame ledger and all finite transformation certificates.
- `proofs/FRAME_PROOF.md`: detailed proof of the final frame, error pool and growth changes.
- `review/`: separate mathematical reviews and actual verification receipts. Earlier review notes describe intermediate versions; the final PDF and final frame review govern the frozen result.
- `inherited_factorial_free/`: the unchanged predecessor packet, including its proofs, sources, provenance and checking modules.
- `PROVENANCE.json`, `NOTICE.md`, `INTEGRATION.md`, `MANIFEST.sha256`: source identities, attribution, integration guidance and release integrity.

## Reproduce the finite checks

Use Python 3.10 or later. The checks and producer require only the standard library and work offline after extraction.

```sh
python3 -B verify.py
python3 -B verify.py --rebuild
python3 -B -O code/verify_endpoints.py
```

The root verifier checks the release manifest, source edits, every finite algebraic map, every coefficient of all six quartics, all advertised metrics, deliberate negative controls and the literal report exports. `--rebuild` additionally generates all 37 equation JSON files in a temporary directory and compares them byte for byte. The optimized run establishes that verification does not depend on Python assertions. The retained receipts report successful normal and optimized runs.

The independently authored root collector imports no producer or inherited compiler. The source/map checker uses the predecessor's separately authored checker, never its production/search modules. These are separate implementations within the same AI-assisted workflow, not an external human audit.

To build the PDF with a standard pdfLaTeX installation:

```sh
sh build_report.sh
```

The build makes three passes and rejects overfull boxes or unresolved references. Rebuilt PDF metadata may differ; the release manifest records the distributed PDF's exact bytes. For a clean archival comparison, rebuild a separate copy of the package.

For exact evaluation at a supplied integer tuple:

```sh
python3 -B code/evaluate.py point.json --profile minimum_dimension
```

Here `point.json` is a JSON list of exactly 237 integers in the specified coordinate order. Evaluation is an arithmetic utility, not a consistency decision procedure.

## Data format

Each sparse term is `[coefficient, [coordinate_indices]]`. For example, `[3,[0,2,2]]` means `3*x0*x2^2`; the empty index list is a constant. Repeated indices are repeated factors. Indices are zero-based. An `equation.json` gives the full coordinate order and residual list; `expanded_polynomial.json` gives every nonzero collected coefficient of their sum of squares. `METRICS.json` records exact dimensions, degree, support, residual height and quartic height.

The semantic source edits preserve existence via translations to and from finite refutations. They do not claim a pointwise bijection with every predecessor solution. The later monic projections have explicit integral restorations, and the invertible row/coordinate transformations give the exact algebraic equivalences recorded in their certificates.

## Proof status

The new unbounded arguments are ordinary mathematics formalizable in ZFC and are given in the report. They are composed with the repository's named C222/ZF/ZFC logical calibration. The exact finite polynomial artifacts were independently checked and rebuilt. The full transitive Lean/Rocq development was not rebuilt, and this contribution does not include a newly checked encoded object-language ZFC proof. It does not prove or refute `Con(ZFC)` itself.

No upstream branch, repository file, issue or pull request was modified. The archive is ready for review and incorporation under the retained MIT No Attribution license.

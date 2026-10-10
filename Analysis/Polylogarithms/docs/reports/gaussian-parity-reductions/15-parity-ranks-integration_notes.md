# Integration notes for the ProveIt polylogarithm manuscript

## Source and scope

This package continues `Analysis/Polylogarithms/docs/manuscript` in
`VladimirReshetnikov/ProveIt`, inspected at the pinned commit
`0599fe867a0c7d0819b4e9f3cd92ce90a3b62b8d`.

Pinned source:
[the consolidated manuscript](https://github.com/VladimirReshetnikov/ProveIt/tree/0599fe867a0c7d0819b4e9f3cd92ce90a3b62b8d/Analysis/Polylogarithms/docs/manuscript).

The mappings below refer to that consolidated source, including its
qualifications about numerical evidence and period independence. They do
not silently reinstate stronger claims from earlier drafts. New-result
anchors are LaTeX labels in this package's `article.tex`; preserve or
translate these labels when merging text into the chapter structure.

This is an integration guide and a self-contained research package. No
remote repository files, commits, branches, issues, or pull requests were
changed.

## Chapter 4: exact mappings and status changes

All source anchors in this table occur in `chapters/04-depth.tex`.

| Exact source label or containing label | Source statement | New article anchor | Status and integration action |
| --- | --- | --- | --- |
| `gauss:eq:g51` | Weight-six evaluation of `g_{5,1}` | `cor:weight-six`, `eq:g51` | **Proved.** Preserve the displayed coefficients and replace its numerical-only status with the explicit Gaussian parity proof. |
| `gauss:eq:g42` | Weight-six evaluation of `g_{4,2}` | `cor:weight-six`, `eq:g42` | **Proved**, by the same exact specialization. |
| `gauss:eq:g33` | Weight-six evaluation of `g_{3,3}` | `cor:weight-six`, `eq:g33` | **Proved**, by the same exact specialization. |
| `gauss:eq:g24` | Weight-six evaluation of `g_{2,4}` | `cor:weight-six`, `eq:g24` | **Proved**, by the same exact specialization. |
| `gauss:eq:g15` | Weight-six evaluation of `g_{1,5}` | `cor:weight-six`, `eq:g15` | **Proved.** Retain the boundary-convergence justification for the leading index one. |
| `gauss:eq:wt5-sporadic` | `576 g41 + 288 g32 + 736 g23 + 960 g14 = 21 G zeta(3) - 480 beta(4) log(2)` | `thm:weightfive`, `eq:weightfive`, `eq:shuffle-A`, `eq:shuffle-B` | **Proved and strengthened.** The exact certificate is `960 A - 224 B`; the power-of-pi terms cancel. Keeping both independent shuffle rows shows that at most two of these four double coordinates are needed modulo the declared single-value products. No numerical independence is asserted. |
| `mixed:sec:eisdim` | Weight-five candidate `Re Li_{4,1}(rho^2,rho)` in the residual table | `thm:four`, `eq:four-rho-real` | **Candidate removed.** Its explicit formula uses only the single-value algebra already listed by the source. |
| `mixed:sec:eisdim` | Weight-six candidate `Im Li_{5,1}(rho^2,rho)` in the residual table | `thm:four`, `eq:four-rho-im` | **Candidate removed**, with an exact single-value evaluation. |
| `mixed:sec:gauss` | Weight-five candidate `Re Li_{4,1}(i,-i)` | `thm:four`, `eq:four-i-real` | **Candidate removed**, with an exact single-value evaluation. |
| `mixed:sec:gauss` | Weight-six candidate `Im Li_{5,1}(i,-i)` | `thm:four`, `eq:four-i-im` | **Candidate removed**, with an exact single-value evaluation. |
| `mixed:thm:parallel` | The interpretation that both towers add two mixed directions in the same positions | `sec:four`, especially “What the reductions change” | **Interpretation superseded.** Both pairs have precisely the conjugation parity forced to reduce. Preserve the historical observation only as a record of the earlier search. |
| `mixed:sec:eisforms` | Reported failure of the tested single-value basket to reduce the mixed weight-five real and weight-six directions | `thm:mixed`, `cor:mixed-height-one`, `thm:four` | Replace the unresolved status of the four named quantities with their exact formulas. Do not assert which implementation detail caused the historical negative searches; their scripts were not in the inspected snapshot. |
| `mixed:eq:gauss-w2` | `Li_{1,1}(i,-i) = -Li_2((1-i)/2)`, previously checked numerically | `app:Li11`, `prop:Li11`, `eq:Li11` | **Proved directly.** The principal-branch integral evaluation includes the first-index-one boundary case. |
| `mixed:eq:eis-w2` | The two real/imaginary formulas for `Li_{1,1}(rho^2,rho)` in terms of `Li_{1,1}(rho,1)` and `Cl_2(2*pi/3)` | `app:Li11`, `prop:Li11`, `eq:Li11` | **Proved consequences.** The appendix's Eisenstein half-point evaluation is equivalent to both source formulas by the elementary Landen identity; the explicit equivalence is recorded below. |
| `gauss:eq:S4-closed` | The proposed formula for the odd-weight harmonic sum `S_4` | `prop:S4-reduction`, `eq:Sp-mixed`, `problem:S4`, `eq:S4-open`, `eq:S4-source` | **Still open in this package.** A direct series identity proves `S_p = Im Li_{p,1}(i,1) + Im Li_{p,1}(i,-1)` for `p >= 2`, but the additional relation needed for the displayed `S_4` formula has not been proved. |
| `gauss:eq:even-general` | The generating-integral formula for every `S_{2m+1}` | Discussion preceding `prop:S4-reduction` | **Already proved in the source.** Retain its status; do not count it as a new result of this continuation. |

The residual values in `mixed:sec:eisdim` and `mixed:sec:gauss` do not
have separate original equation labels. Their containing section labels
above are exact source anchors, not invented equation labels.

### Suggested chapter structure

Insert the reciprocal-argument theorem and its elementary proof before
the source's mixed-point residual discussion. The natural sequence is:

1. `thm:mixed` and `lem:bilateral`: a general formula for
   `Li_{a,b}(z,z^{-1})`, with integers `a >= 2`, `b >= 1`, `|z| = 1`,
   `z != 1`.
2. `cor:mixed-height-one`: the complete parity-selected family with
   second index one.
3. `thm:four`: the four actual source targets.
4. Higher instances `eq:mixed-i-w7`, `eq:mixed-i-w8`,
   `eq:mixed-rho-w7`, `eq:mixed-rho-w8`, `eq:mixed-i-w9`, and
   `eq:mixed-rho-w9`.

Insert `thm:gaussian` before the source's weight-six displays, then use
`cor:weight-six` to promote precisely those five equations. The arbitrary
even-weight edge family and the support proposition are additional
proved consequences (`cor:edge`, `prop:support`). The ordinary two-shuffle
proof of the weight-five relation can follow the weight-five display.

Keep the two weight-five shuffle rows themselves, rather than only their
particular combination reproducing the source. They give the stronger
explicit eliminations

\[
g_{2,3}=-6g_{4,1}-3g_{3,2}
-\frac{3}{32}G\zeta(3)-\frac{\pi^5}{1536},
\]

\[
g_{1,4}=4g_{4,1}+2g_{3,2}
+\frac{3}{32}G\zeta(3)-\frac12\beta(4)\log2
+\frac{23\pi^5}{46080}.
\]

Thus `g41` and `g32` span this four-value family modulo
`pi^5`, `G*zeta(3)`, and `beta(4)*log(2)`. The source's single selected
relation alone gave the weaker upper bound of three coordinates. The
two-row result proves an upper bound of two, not that two are necessary.

### The weight-two boundary formulas

Appendix A proves, on the stated principal branches,

\[
\operatorname{Li}_{1,1}(z,z^{-1})
=-\operatorname{Li}_2\!\left(\frac{z}{z-1}\right),
\qquad |z|=1,\ z\ne1.
\]

The Möbius-transformed argument has real part `1/2`, so it stays off the
principal dilogarithm cut. This directly promotes `mixed:eq:gauss-w2`.
To see the exact correspondence with both parts of `mixed:eq:eis-w2`,
use the elementary principal-branch Landen identity

\[
\operatorname{Li}_2(z)+\operatorname{Li}_2\!\left(\frac{z}{z-1}\right)
=-\frac12\log^2(1-z).
\]

It follows either by differentiating both sides on the slit plane and
matching the value at zero, or by the usual elementary dilogarithm
integral. Since `Li_{1,1}(z,1)=log^2(1-z)/2`, the appendix gives
`Li_{1,1}(z,z^{-1})=Li_2(z)+Li_{1,1}(z,1)`. At the Eisenstein point,
put

\[
H=\operatorname{Li}_{1,1}(\rho,1)
=\frac18\log^2 3-\frac{\pi^2}{72}
-\frac{\mathrm i\pi}{12}\log3.
\]

Then the mixed value is `Li_2(rho^2)+conj(H)`. Its imaginary part is
`-C_2-Im(H)`, and its real part is `5 Re(H)-log^2(3)/2`, exactly the
two source equations. These consequences use only integer-order
polylogarithms and the explicit sine convention for `C_2`.

### Claims that should not be inferred from these changes

- Removing these four candidates does not compute a complete regularized
  double-shuffle quotient. Do not revise every historical dimension table
  solely by subtracting the number of removed entries.
- The other Gaussian and Eisenstein residuals do not acquire an
  independence proof. A spanning set and a basis of actual periods remain
  different claims.
- The source's unproved triple-polylogarithm displays are not promoted by
  the double-polylogarithm work in this package.
- The weight-five imaginary relation is proved by shuffle; odd-weight
  imaginary components are not individually eliminated by the parity
  projection used here.
- The `S_4` point `(i,-1)` is not the reciprocal point `(i,-i)`. The
  reciprocal theorem therefore does not settle `gauss:eq:S4-closed`.

## Chapter 7: all-denominator reflection and distribution ranks

The following source labels occur in `chapters/07-integration.tex`.

| Exact source label or section title | Source statement | New article anchor | Status and integration action |
| --- | --- | --- | --- |
| `stieltjes:prop:jetrank` and its following epistemic-status paragraph | The exact finite pattern for `3 <= q <= 30`, `1 <= k <= 4`, with its all-`q` extension expressly conjectural | `thm:jet-rank`, `eq:jet-rank`, `eq:jet-character-count`, `thm:distribution`, `cor:primitive` | **The all-parameter formal presentation law is proved.** Apply weight `lambda(p)=p^{-k}`, endpoint pinning, and reflection sign `epsilon=(-1)^{k+1}`. |
| `stieltjes:eq:negmult` | Negative-integer Hurwitz-zeta derivative multiplication relation | `eq:distribution-prime`, `lem:composite`, `eq:distribution-composite` | This is a proved input retained from the source. After moving its explicit inhomogeneous part to the known side, it supplies the weight `p^{-k}` distribution rows. |
| `stieltjes:thm:negrefl` | Reflection at the negative-jet floor | `eq:pin-reflect`, `thm:distribution` | This is a proved input retained from the source. Its known right side is removed before imposing the homogeneous sign relation. |
| Unlabelled section “Underived Stieltjes grids and character coordinates” | The first-Stieltjes finite-grid count `phi(q)/2 - 1` | `cor:stieltjes-rank`, `eq:stieltjes-rank`, `thm:distribution` | **The all-`q` formal presentation count is proved**, using `lambda(p)=p` and `epsilon=+1`, after pinning the endpoint and removing the known inhomogeneous distribution and reflection terms. No original LaTeX label is available for this section. |
| `stieltjes:prop:tzbridge` and `stieltjes:thm:hbridge` | Functional-equation bridges for character derivatives | Character interpretation surrounding `thm:distribution` | Preserve these existing results and their primitive-character and conjugation conventions. The rank theorem organizes the formal coordinates; it does not give new evaluations of all remaining character derivatives. |
| `stieltjes:sec:negq5812` and `stieltjes:thm:negq5812` | Composite-denominator examples and their interpretation as new constants | `cor:primitive`, `eq:q12-normal` | Retain the explicit special-value formulas. Qualify “forces genuinely new constants” as formal residual directions after the declared relations, unless an additional period-independence theorem is supplied. |

For every integer `q >= 3` and `k >= 1`, the negative-jet presentation
has the proved residual dimension

\[
r_{q,k}=\begin{cases}
\varphi(q)/2-1,&k\text{ odd},\\
\varphi(q)/2,&k\text{ even}.
\end{cases}
\]

The theorem first establishes that the unpinned weighted distribution
module is the regular representation of the unit group over the complex
numbers, and consequently has rational dimension `phi(q)`. Pinning the
endpoint removes the principal character. Reflection retains the specified
parity half. This proves the rank of the declared relation presentation,
not linear independence of the resulting numerical periods.

The primitive-residue basis has an additional hypothesis:
`lambda(m)=m^s` with a **nonzero integer** `s`. Do not extend that basis
claim automatically to ordinary weight `s=0`; the general dimension
theorem permits vanishing character multipliers, whereas this particular
basis theorem uses their nonvanishing.

The endpoint convention is part of the proof: the class `0` in
`(1/q) Z / Z` represents the Hurwitz parameter `1`, with its value moved
to the known side. It does not authorize evaluating the Hurwitz zeta
function literally at parameter zero.

## Chapter 8: the parameter-derivative distribution tower

The following exact source anchors occur in
`chapters/08-differentiation.tex`.

| Exact source label | Source statement | New article anchor | Status and integration action |
| --- | --- | --- | --- |
| `tower:thm:rank` | The finite distribution-rank observation for `3 <= q <= 30`, `k=1,2,3`, with residual count `phi(q)-1` | `cor:parameter-rank`, `eq:parameter-rank`, `thm:distribution` | **The all-`q`, all-`k` presentation law is proved.** For every `q >= 3`, `k >= 1`, use weight `lambda(m)=m^{k+1}` and pin the endpoint. No reflection relations are imposed. |
| `tower:prop:dist`, `tower:eq:dist` | Distribution of the parameter derivatives `gamma_1^{(k)}(x)` | `eq:parameter-master`, `eq:parameter-distribution` | Retain the source identity as an established input. Move its explicit polygamma term to the known side before taking the homogeneous presentation. |

The resulting exact formal residual dimension is

\[
\dim=\varphi(q)-1\qquad(q\ge3,\ k\ge1).
\]

This is the no-reflection case of the common weighted distribution
theorem. It must not be confused with the parity-halved dimensions of
the negative-jet and underived first-Stieltjes presentations. Adding
reflection or additional analytic identities defines a different quotient
and can lower the count. Here the superscript on `gamma_1^{(k)}` denotes
parameter differentiation; the prime on `zeta'(s,x)` denotes spectral
differentiation.

## Chapter 10 and the editorial ledger

In `chapters/10-discovery.tex`, the unlabelled section “The surviving
research programme” asks for a uniform proof of the Stieltjes divisor-row
structure and for certified mixed-point relations. Its task list can now
record:

- the complete proof of the specified all-denominator reflection and
  distribution presentation;
- a constructive primitive-residue normal form and exact row-space
  certificates;
- exact removal of the four named reciprocal-root candidates;
- proofs of the five Gaussian weight-six displays and the selected
  weight-five relation;
- retention of the complete regularized double-shuffle computation,
  complementary-parity evaluations, actual period independence, and the
  specified `S_4` identity as further research.

Update any manuscript-level editorial ledger to distinguish an analytic
proof from a finite exact check and from a numerical check. The article's
source comparisons are deliberately narrower than a claim that all
Chapter 4 or Chapter 7 open questions have been settled.

## Reproducibility and evidence types

| Artifact | What it establishes or checks |
| --- | --- |
| `article.tex` / `article.pdf` | The complete analytic and algebraic proofs, with hypotheses and remaining questions. |
| `code/mixed_parity.py` | Exact coefficients, symbolic reductions, and independent Mellin-integral evaluation for reciprocal doubles. |
| `code/verify_mixed.py` | Sixteen exact partial-fraction identities, ten exact displayed specializations, twelve general-index numerical checks, and checks against the archived height-one values. |
| `results/height_one_quadrature.json` | Twenty-seven independent height-one quadratures at 90-digit working precision; maximum recorded parity residual below `4.93e-88`. |
| `results/mixed_verification.json` / `.csv` | General-index checks at 80-digit working precision; maximum recorded residual below `1.53e-79`, plus exact symbolic checks and generated formulas. |
| `code/gaussian_parity.py`, `code/verify_gaussian.py` | The Gaussian symbolic formula and its independent verification workflow. |
| `results/gaussian_checks.json` | Twenty-three independent Gaussian quadrature checks at 65-digit working precision; maximum recorded residual below `4.50e-64`. |
| `results/weight5_shuffle_certificate.json` | Exact word-shuffle enumeration and the integer row combination proving `gauss:eq:wt5-sporadic`. |
| `code/distribution_grids.py` | Exact rational reflection and distribution matrices and constructive normal forms. |
| `results/distribution_validation_summary.json` | All 1,087 finite matrix checks passed; no floating-point rank decisions were used. |
| `results/primitive_normal_form_certificates.json` | Eight exact normal-form certificates, including agreement with the defining row space. |

The quadrature residuals are diagnostic numerical evidence, not
interval-certified error bounds and not substitutes for the proofs. The
finite exact distribution checks corroborate the all-parameter proof;
they do not themselves establish the infinite family.

## Notation and attribution checks before merging

1. **Reverse both index and argument vectors when comparing conventions.**
   This package uses `n > m` in `Li_{a,b}(x,y)`. Panzer uses increasing
   nested indices, so his `Li_{b,a}(y,x)` denotes the same value.

2. **Keep the Eisenstein point fixed.** Here
   `rho=exp(2*pi*i/3)`, not the sixth-root CM point `exp(pi*i/3)` that
   is also denoted by `rho` in some local source chapters. The reciprocal
   point in the Eisenstein formulas is `(rho^2,rho)`.

3. **Avoid an implicit generalized-Clausen convention.** The new article
   defines `C_{2r}=Im Li_{2r}(rho)` and uses only positive integer `r`
   in that notation. It separately defines `I_j(z)=Im Li_j(z)` for
   every integer index used in the height-one family. No noninteger-order
   Clausen identity is asserted. If a future extension uses `Cl_s` for
   noninteger `s`, an even/odd-integer convention does not define it:
   specify the sine or cosine series and its analytic continuation instead.

4. **Keep parity attribution explicit.** Erik Panzer, *The parity theorem
   for multiple polylogarithms*, Journal of Number Theory **172** (2017),
   93–113, DOI `10.1016/j.jnt.2016.08.004`, arXiv `1512.04482`, supplies
   the general functional theorem, its root-of-unity corollary, and the
   explicit depth-two formula. The reciprocal Fourier proof here is an
   independent derivation of a specialization, not a new general parity
   theorem.

5. **Retain the earlier unit-circle attribution.** Takashi Nakamura,
   *A simple proof of the functional relation for the Lerch type Tornheim
   double zeta function*, Tokyo Journal of Mathematics **35** (2012),
   333–337, arXiv `1012.1144`, Proposition 1.2, precedes Panzer's
   depth-two unit-circle specialization. Panzer notes a typo in Nakamura's
   equation (1.3): `zeta(a;-y) zeta(b;x)` should read
   `zeta(a;x) zeta(b;-y)`. The package's independent Fourier proof does not
   depend on that printed formula.

6. **Retain the universal-distribution context.** Cite Kubert's work on
   universal distributions and the cohomology reference recorded under
   the article's `Kubert` and `KubertCohomology` bibliography keys. The
   package proves its precise weighted finite presentation directly;
   neither the general mechanism of universal distributions nor its
   classical ordinary-weight case is claimed as newly discovered.

7. **Preserve the scope of novelty.** “Proved here” means that this package
   contains a proof resolving the identified manuscript target. It does
   not establish that every resulting special-value formula has never
   appeared elsewhere. The numerical basis searches also do not establish
   independence of beta values, Clausen values, zeta values, or character
   derivatives.

# Review of the cube application and manuscript integration

The section filenames in this review refer to the modular drafting sources, which are incorporated in the single delivered TeX article. Initial proof-note reviews were supplemented by the final section and integration audits.

This review covers `sections/cube_application.tex`, `sections/introduction.tex`, `sections/research_agenda.tex`, and the joint-scale corollary `loc:cor:joint-scale` in `sections/localization.tex`. It is an internal mathematical review by a separate ChatGPT instance, not external peer review or formal verification.

## Final status

**Resolved: no outstanding mathematical or integration issue was found.** The introductory attribution, density normalization, degree wording, finite hypotheses, and lower-decimal presentation have been corrected. The research agenda now recognizes the proved joint-scale profile and asks whether another localization construction can improve its scale requirement. The new full joint-scale profile was independently checked, including the zero and infinite endpoints.

## Cube application: no mathematical gap found

The four-vertex classification is valid over every finite odd-order abelian group. Reflecting cube coordinates is an invertible change of the base and increment variables. Two distinct nonzero binary vectors have a nonzero two-by-two minor of determinant `±1`, proving joint uniformity for up to three distinct vertices over every finite abelian group. Three independent binary vectors have a three-by-three minor of determinant `±1` or `±2`; this acts invertibly on an odd-order group. In the rank-two case, projection onto two independent coordinates maps the four vertices injectively onto the binary square, so the lifted parallelogram relation is exact over the integers.

The parallelogram count is correct. There are `6^d` ordered solutions to the coordinatewise diagonal equation. The two trivial pairing families have union size `2·4^d−2^d`; every repeated-entry solution belongs to that union. Each remaining unordered parallelogram has exactly eight ordered descriptions. Therefore

    P_d=(6^d−2·4^d+2^d)/8.

The centered expansion retains all terms correctly. Joint uniformity kills support sizes one through three and the independent four-vertex supports. Each parallelogram contributes exactly the normalized `U2^4`. For each higher support, the mixed Gowers–Cauchy–Schwarz inequality applied with constants one at omitted vertices bounds its magnitude by `u^j`. The treatment of `d=2`, `delta=0`, and empty remainders is consistent with the stated power conventions.

The exact reduction `A_d=P_d c_d^odd` is proved in both directions. The upper bound follows directly from the norm comparison. For necessity, fixing a finite group and a real centered function, scaling by a positive parameter tending to zero, and dividing by its fourth power isolates the quartic coefficient. The error is of order five for each fixed group and function, which is sufficient for the argument. Since every function on the fixed finite group is bounded, these scaled perturbations can be required to lie in `[0,1]` around any fixed background strictly between zero and one. This proves weighted sharpness without asserting indicator sharpness.

The resulting asymptotic `A_d~6^d/24` and the explicit high-order bound have the correct powers. The text correctly keeps the small-perturbation limit separate from the dimension limit and does not claim a new global Szemerédi bound.

## Introduction: resolved precision checks

1. **Attribution of the old limiting upper bound.** The introduction now correctly attributes `c_d<=B_d` with `B_d` decreasing to `1/2` specifically to Source 29. Source 28 supplied a different, weaker uniform estimate and a non-extremality result for a single cosine. The inspected consolidated source distinguishes these contributions explicitly.
2. **Background density in the quartic coefficient.** The introduction now states the quartic term at background `delta` as `P_d delta^(2^d−4)||f||U2^4`, matching the application section.
3. **Phase theorem hypotheses and degree.** The short introductory description now says that the phase has degree at most `k+1` and invokes the cited finite theorem's derivative-energy and width hypotheses. The detailed localization section explicitly supplies the multi-affine extension assumption and all finite conditions.

The main norm limit, finite-order formula, localization denominator bounds, source-relative research scope, and distinction from external peer review are otherwise accurately represented.

## The joint-scale corollary and revised research agenda

The manuscript now proves the full transition profile for its explicit finite localization coefficient. In particular,

    k→infinity and m/k²→infinity imply R_{k,m,N}/v_k→1

uniformly in prime `N>=m²`. The agenda correctly treats this as proved and asks whether a different construction can improve the scale regime or finite corrections.

Here is a proof using only the article's formulas. Put `ell=m−1` and

    H_k(a)=sum_{j=0}^k binom(k,j) (2a)^j (k−j+2)!/(k+2)!.

The termwise exponential estimate already proved in the localization section gives

    1 <= H_k(a) <= exp(2ka/(k+2)).

Since `T_k(m−1,w)=(m−1)^k H_k(w/(m−1))` and `L<=w<L+1`,

    exp(−2kw/((k+2)(m−1)) − 3k(k+2)/m)
      <= R_{k,m,N}/v_k
      <= exp(k/(m−1)).

For the lower bound, use `(m/(m−1))^k>=1`,
`w/(L+1)>=L/(L+1)`, `log(1+1/L)<=1/L`, and
`L>=m/(3k)`. For the upper bound, use `H_k>=1`, `w/(L+1)<=1`,
and `log(m/(m−1))<=1/(m−1)`. Finally `w<=m/(3k)+2`, uniformly
in `N`, so both exponents tend to zero under the stated condition.

### Independent check of the full profile

The stronger corollary asserts, along any admissible sequence with `k→infinity` and `m/k²→lambda`,

    R_{k,m,N}/v_k → 0                  if lambda=0,
    R_{k,m,N}/v_k → exp(−3/lambda)     if 0<lambda<infinity,
    R_{k,m,N}/v_k → 1                  if lambda=infinity.

All three cases are correct, uniformly in prime `N>=m²`.

The factorization

    R/v = (m/(m−1))^k (w/(L+1))^(k+2) H_k(2w/(m−1))^(−1)

is exact with the corollary's definition of `H_k`. Its coefficientwise bound `1<=H_k(z)<=exp(kz/(k+2))` is valid for every nonnegative `z`.

The new rounding estimate is essential for identifying the profile rather than only obtaining a sufficient condition. Since `m>3k`, one has `L<2m/(3k)`, and `M=floor(N/L)>=N/(2L)`. Writing the remainder after division by `L` gives

    0 < w−L < L/M <= 2L²/N < 8/(9k²).

Thus the error in replacing `w` by `L` is uniform in the ambient prime.

For `0<lambda<=infinity`, `L~m/(3k)` and `L` grows at least on the scale of `k`. The first logarithmic factor is `k log(m/(m−1))=o(1)`, and `log H_k(2w/(m−1))=o(1)`. The middle logarithmic factor is

    (k+2) log(w/(L+1))
      = −(k+2)/L + O(k/L²) + O(1/(kL)).

The two error terms tend to zero, and `(k+2)/L→3/lambda`, with the convention `3/infinity=0`. This proves the positive and infinite cases.

For `lambda=0`, one has `L=o(k)`, but the admissibility condition still gives `k/(m−1)<=1/3`. The rounding bound implies `w<=L+1/2` eventually. Dropping the inverse `H_k` factor and bounding the first factor gives

    R/v <= exp(1/3) (1−1/(2(L+1)))^(k+2)
        <= exp(1/3−(k+2)/(2(L+1))) → 0.

This separately handles sequences where `L` stays bounded; no large-`L` Taylor expansion is incorrectly used at the zero endpoint. The corollary also correctly limits its necessity interpretation to the explicit coefficient `R`, without claiming that every possible finite localization construction must obey the same scale requirement.

The other research questions remain legitimately open relative to the proofs provided. In particular, the exact fourth-order constant, optimal norm convergence rate, equality classification on fixed groups, fixed-exponent numerical limits, optimal face-cover mass, fixed-degree local coefficient, and next relative term of the local optimum are not determined here.

The fourth-order upper decimal was independently checked:

    (832/4795)^(1/4) = 0.6454070108505990837483...

For the lower decimal, the source provides the certified truncated inequality `0.5587725<=c_4^odd`. The final agenda now displays that truncated number without an ellipsis and explains that the underlying finite construction is the certificate.

## Scope of this review

No additional empirical tests were needed for these integration checks. The conclusions above come from inspecting the mathematical arguments and comparing their normalizations. No edits to the audited sections were made by this reviewer.

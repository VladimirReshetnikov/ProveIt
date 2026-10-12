# Independent audit: all-power trigamma moments and generators

Audited file: `output/ProveIt_Bernoulli_Tails_and_Spectral_Faces_2026-10-11/sections/02_all_powers.tex`.
Scope: the finite arithmetic span, convergence of the generator, the multiple-polylogarithm depth claim, and the resonant Laurent/Stieltjes formulas. The Bernoulli recurrence itself was taken as separately audited. This is a proof audit; no numerical tests were repeated.

## Verdict

The finite-span theorem, analyticity for `|t| < 2 pi`, and exact Laurent radius `2` are correct. The claimed multiple-polylogarithm depth bound is also correct, but its current endpoint paragraph is underjustified and uses potentially misleading generic regularization terminology. An elementary strengthened induction removes this issue completely. One sentence in the Laurent proof should explicitly include the logarithmic factor in derivative bounds.

## 1. Finite arithmetic span: sound

All operations on the formal Taylor series in the recursive generator are linear over the rational numbers: multiplication by the elementary factors with rational Taylor coefficients, anchored integrations, and division by `2 sinh(t/2)` after its removable zero is factored out. At fixed power, only finitely many explicitly listed anchors in the polynomials `R_e`, `e <= d`, occur.

The maximal anchor weight is `2d-1`. In fact, the even-power initial anchor `Z_{e,1}` has weight `2e-1`; the odd-power term `zeta(2)^(e-1)` has weight `2e-2`; and a lower anchor `Z_{e-2j,k-4j}` has weight `2e-k <= 2e-2`. Products of convergent MZVs in the first two types reduce to a finite rational combination of convergent MZVs by the usual stuffle product. The recurrence does not multiply a moment by a new zeta constant. Thus no weight or span issue is hidden in the induction.

If an entirely explicit, albeit larger, coordinate space is desired, the theorem may state

\[
 M_{d,m}\in\operatorname{span}_{\mathbb Q}
 \left(\{1\}\cup
 \{\zeta(s_1,\ldots,s_\ell):s_1\ge2,\ s_i\ge1,
                    s_1+\cdots+s_\ell\le2d-1\}\right).
\]

This set is finite. The smaller recursive set of anchors already specified in the manuscript is preferable for computations. The finite weight bound concerns the Taylor coefficients; an explicit functional polylogarithm representation can introduce endpoint constants of larger weight which cancel in the relevant coefficients.

## 2. Analytic generator: sound

The induction starts with the polynomial `H_1=-t^2/4`. Anchored integrations preserve holomorphy on the disk, which is simply connected and star-shaped. The numerator in the formula for `G_d` has the stated parity and vanishes at zero; the other zeros of `2 sinh(t/2)` are `2 pi i k`, so none lies in the open disk except zero. The quotient is therefore holomorphic throughout `|t|<2 pi`. The formal coefficient argument preceding this induction avoids assuming convergence in advance. Only convergence on this disk is asserted, not exact radius, so there is no missing boundary-singularity argument.

For the functional representation, add this branch statement:

> The following multiple-polylogarithm formulas are first obtained for real `t>0` from their absolutely convergent defining series. The assembled expression then denotes the analytic continuation supplied by the anchored generator on `|t|<2 pi`.

One should not claim that each separated polylogarithm term individually extends holomorphically through zero.

## 3. Strengthen the endpoint/depth proof

The generic phrase “usual finite harmonic-stuffle regularizations” is unnecessarily broad. For arbitrary words, the constant term as `t -> 0` of a one-variable polylogarithm is naturally an iterated-integral/shuffle endpoint regularization; conversion to harmonic regularization requires care. The words needed here are much simpler, and no general regularization theorem is needed.

### The useful invariant

Prove by induction that `H_d` is a finite sum of polynomials times `L_a(t)`, with **every nonempty word `a` having first index at least 2**, and with depth at most `d-1`. Coefficients are finite rational combinations of convergent MZVs, and polynomials without an MPL are included as the empty word.

Ordinary integrations only increase the first index. The new operation is

\[
 I^2\!\left(\frac{z}{1-z}\,t^mL_{\boldsymbol a}(t)\right),
 \qquad z=e^{-t},
\]

where `a` is admissible or empty. Before anchoring, an explicit double primitive is

\[
 P_{m,\boldsymbol a}(t)
 =\sum_{j=0}^m(j+1)\frac{m!}{(m-j)!}
         t^{m-j}L_{j+2,\boldsymbol a}(t).
\]

Indeed `L_{1,a}'=-z L_a/(1-z)` and subsequent primitives raise the leading index. This expression has only leading indices at least 2 and raises depth by exactly one for each such nonempty term. The other recursive operation `I^{4j}` does not increase depth. Hence the induction gives the claimed upper bound `d-1` and the stronger leading-index invariant.

### Endpoints are explicitly convergent MZVs

The value of every `P_{m,a}(0)` is a convergent MZV. Its first derivative is

\[
 P_{m,\boldsymbol a}'(t)
 =-\sum_{j=0}^m\frac{m!}{(m-j)!}
          t^{m-j}L_{j+1,\boldsymbol a}(t).
\]

When `m>0`, its limit is `-m! zeta(m+1,a)`, again convergent. When `m=0`, there is only the possible divergence `-L_{1,a}(t)`.

For an admissible word `a=(a_1,...,a_l)`, let `zeta(empty)=1` and define

\[
 K(\boldsymbol a)=
 -\sum_{i=1}^{\ell}
   \zeta(a_1,\ldots,a_i,1,a_{i+1},\ldots,a_\ell)
 -\sum_{i=1}^{\ell}
   \zeta(a_1,\ldots,a_i+1,\ldots,a_\ell),
 \qquad K(\varnothing)=0.
\]

All these MZVs converge. The elementary endpoint formula is

\[
 L_{1,\boldsymbol a}(t)
   =\zeta(\boldsymbol a)L_1(t)+K(\boldsymbol a)+o(1),
       \qquad t\downarrow0.
\]

To prove it, subtract `zeta(a) L_1(t)` termwise:

\[
 L_{1,\boldsymbol a}(t)-\zeta(\boldsymbol a)L_1(t)
 =\sum_{n\ge1}\frac{e^{-tn}}n
        \bigl(H_{n-1}(\boldsymbol a)-\zeta(\boldsymbol a)\bigr).
\]

The last series converges absolutely even at `t=0`, because the tail of an admissible multiple zeta sum is `O(n^{-a_1+1}(1+log n)^{l-1})`. Dominated convergence applies. Order the added index `n <= m_1` among the strictly descending zeta indices: either it is inserted after one of them, or equals one of them. These cases give precisely the two sums in `K(a)`.

In the complete double primitive, the coefficient of `L_1(t)` in its derivative is the negative of `H_{d-1}(0)`, hence zero. Its derivative therefore has a finite limit given entirely by the displayed convergent MZVs. Subtracting the value and this derivative at zero anchors the double primitive. This supplies every integration constant and proves the depth assertion without divergent MZV notation. It also proves that no `L_{1,1,...}` endpoint is actually needed in the chosen representation.

If space does not permit this elementary formula, a safe shorter replacement is “shuffle-regularized iterated-integral endpoint values, equivalently harmonic regularization after the standard conversion”; however, the explicit single-leading-one argument is both stronger and simpler for this theorem.

## 4. Laurent coefficients and exact radius: sound, with one wording fix

After subtracting the terms through `j=r`, the square bracket in the theorem is `O(x_n^-3)`. Thus the remainder multiplied by `x_n^-epsilon` is normally convergent on `Re epsilon > -2`, and differentiating it gives the stated factor `(-log x_n)^q`. The added Hurwitz zeta terms give the signs `(-1)^q h_{d,r} gamma_q(1/2)` with the displayed exponential-Taylor normalization. The half-shift conversion formula also has the correct signs and factorial factors.

The pole-subtracted meromorphic function has no poles at distance less than 2 from zero, and it has a genuine pole at `epsilon=-2` with nonzero residue `h_{d,r+1}`. The proof that all those residues are nonzero is already present. Therefore the radius really is exactly 2; this is not merely a lower bound from the remainder estimate. For `r>=1`, the previous pole also lies at `epsilon=2`, which is consistent with the statement.

Replace the sentence claiming the same `O(x_n^{-3-Re epsilon})` bound “with all fixed epsilon derivatives,” since derivatives acquire logarithms. A precise replacement is:

> The square bracket is `O(x_n^{-3})`. On each compact set `K` contained in `Re epsilon > -2`, its product with `x_n^{-epsilon}` has `q`th epsilon derivative bounded by
> `O_{K,q}(x_n^{-3-min_{epsilon in K} Re epsilon}(1+log x_n)^q)`.
> This bound is summable for every fixed `q`, so the remainder and all its fixed derivatives converge normally there.

The identity initially agrees with the defining Dirichlet series in `Re epsilon>2r`, and then continues meromorphically into the stated half-plane. This provides a precise common domain if desired.

## Recommended changes

1. Keep the finite-span and radius statements unchanged; optionally display the finite weight-bounded span.
2. Add the branch/assembled-continuation sentence for the MPL representation.
3. Replace the general endpoint regularization paragraph with the leading-index invariant and the explicit single-leading-one endpoint argument above.
4. Include logarithmic factors in the Laurent derivative bound.

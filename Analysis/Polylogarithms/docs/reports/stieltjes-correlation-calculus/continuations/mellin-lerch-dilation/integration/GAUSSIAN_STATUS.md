# Gaussian harmonic research status and integration note

Audit baseline: ProveIt commit `fc4d3bf80534ad7c901d3b8c9e71baf2df0064ed`.
All repository paths below are relative to that commit. This note records the
status of the actual pinned manuscript, not the chronology of earlier reports.

## Definitions and present status

Write

\[
S_p=\sum_{n\ge0}\frac{(-1)^nH_n}{(2n+1)^p},\qquad
g_{a,b}=\operatorname{Im}\operatorname{Li}_{a,b}(i,1),\qquad G=\beta(2),
\]

with `Li_{a,b}(x,y) = sum_{n>m>=1} x^n y^m/(n^a m^b)`.

| Claim | Pinned manuscript status | Status after the present work |
| --- | --- | --- |
| The displayed reduction of `S4` | Proved by a finite exact certificate plus a convergent octahedral relation | Already proved; no new proof claim is made here |
| The displayed reduction of `S6` | Conjecture, with numerical evidence and certified proximity | Remains conjectural |
| Equivalence of two displayed `S6` coordinate baskets | Proved by two convergent same-point shuffles | Already proved; this does not prove either conjectural equality |
| The current odd-inner-index `S8` vector | Conjecture, with certified proximity | Remains conjectural |
| A different, earlier `S8` vector | Rigorously rejected by an interval excluding zero | Remains rejected; it must not be confused with the current candidate |

### S4: already a theorem

The proved identity is

\[
S_4=\frac{4g_{4,1}-3g_{3,2}-9g_{2,3}}7
 +\frac{\pi^5}{224}-\frac{27}{224}G\zeta(3)-2\beta(4)\log2.
\]

The precise source is
`Analysis/Polylogarithms/docs/manuscript/chapters/04-S4-proof.tex`,
Theorem `s4proof:thm:s4`, equation `gauss:eq:S4-closed`. Its proof combines
911 rational standard-relation rows with one explicitly convergent octahedral
duality seed; the supplied `S4_certificate.json` and `verify_s4.py` make the
finite rational combination replayable. This audit read the analytic proof
and its certificate description but did not independently replay that existing
certificate. The theorem does not assert independence or irreducibility of the
remaining double values.

The same file, equation `gaussian:eq:S-mixed`, proves the exact arithmetic
translation

\[
S_p=\operatorname{Im}\bigl(\operatorname{Li}_{p,1}(i,1)
                         +\operatorname{Li}_{p,1}(i,-1)\bigr).
\]

### S6: the exact remaining relation

The equality still to prove is

\[
\begin{aligned}
S_6={}&\frac{722}{527}g_{6,1}+\frac{40}{527}g_{4,3}
       -\frac{128}{155}g_{2,5}+\frac{15191}{28569600}\pi^7\\
 &-\frac3{124}G\zeta(5)-\frac{2373}{10540}\beta(4)\zeta(3)
       -2\beta(6)\log2.
\end{aligned}
\]

Source:
`Analysis/Polylogarithms/docs/manuscript/chapters/04-cyclotomic-quotients.tex`,
Conjecture `cycloquot:conj:S6`, equation `cycloquot:eq:S6`.

In that same file, Proposition `s6change:prop:coordinates`, equation
`s6change:eq:identity`, already proves

\[
g_{2,5}=30g_{6,1}+15g_{5,2}+5g_{4,3}
 -\frac{15}{512}G\zeta(5)+\frac3{16}\beta(4)\zeta(3)
 -\frac{11\pi^7}{368640}.
\]

Substituting this identity only rewrites the conjecture in another basket.
The two residuals differ by `-128/155` times this exact zero relation, with
the residual ordering specified in the manuscript. The manuscript's separating
functional, `cycloquot:eq:separating`, is an obstruction to the stated restricted
product-row proof strategy. It does not imply that the conjecture is false or
that its numerical constants are arithmetically independent.

### S8: keep the current candidate separate from the rejected one

The current equality still to prove is

\[
\begin{aligned}
S_8={}&\frac{52334}{37973}g_{8,1}+\frac{2824}{37973}g_{6,3}
 -\frac{6832}{189865}g_{4,5}-\frac{139760}{265811}g_{2,7}\\
 &+\frac{998183\pi^9}{17283022848}
 -\frac{78615}{19442176}G\zeta(7)
 -\frac{201021}{4252976}\beta(4)\zeta(5)\\
 &-\frac{290505}{1063244}\beta(6)\zeta(3)-2\beta(8)\log2.
\end{aligned}
\]

Source:
`Analysis/Polylogarithms/docs/manuscript/chapters/04-S8-candidate.tex`,
Conjecture `s8new:conj:S8`, equation `s8new:eq:formula`.
This chapter reports rational enclosures giving an absolute residual below
`10^-355`, and a corresponding improved bound for the normalized `S6`
residual. The intervals contain zero. Such enclosures prove proximity and do
not prove equality.

The distinct rejected vector is in
`Analysis/Polylogarithms/docs/manuscript/chapters/10-discovery.tex`,
Proposition `research:prop:S8-rejected`. Its residual is rigorously negative,
between `-1.3274179020580459e-86` and `-1.3274179020580457e-86`.
The current candidate's first paragraph explicitly distinguishes the two.

## What the new harmonic reflection settles, and what it cannot settle

The present fragment `sections/04-harmonic.tex` defines

\[
h_n^{(r)}(u)=\sum_{j=1}^n(j-u)^{-r},\quad
A(z,u)=\sum_{n\ge1}\frac{(-1)^n h_n^{(1)}(u)}{2n+1-z},\quad
Q_{p,r}=\sum_{n\ge1}\frac{(-1)^n H_n^{(r)}}{(2n+1)^p}.
\]

It proves an explicit digamma formula for `A(z,u)+A(-z,-u)`, including the
full nonsingular parameter domain, removal of apparent poles, and ordinary
locally uniform convergence of all fixed mixed derivatives. Consequently it
gives finite exact beta/zeta formulas for `Q_{p,r}` when `p+r` is even, as well
as two-shift differentiated identities and the rational shift `u=1/4` example.

The precise obstruction is elementary and definitive for this formula:

\[
[z^{p-1}u^{r-1}]\{A(z,u)+A(-z,-u)\}
       =(1+(-1)^{p+r})Q_{p,r}.
\]

For `r=1`, `Q_{p,1}=S_p`; hence `S4`, `S6`, and `S8` have total weights
5, 7, and 9. Their coefficients all vanish in this reflected sum. Therefore
the present reflection gives no equation for the residual of either current
`S6` or `S8` conjecture. A proof requires additional information determining
the complementary odd projection `A(z,u)-A(-z,-u)` or a functional relation
that controls its required Gaussian mixed-color coefficients. The existing
octahedral `S4` certificate is a concrete precedent for such additional input.
This is a limitation of the present method, not an arithmetic impossibility
claim. Differentiating the even projection further does not recover the missing
Taylor coefficients.

The unshifted scalar parity formula is attributed to Ce Xu and Weiping Wang,
*Dirichlet type extensions of Euler sums*, C. R. Math. 361 (2023), 979–1010,
Section 3.4, equation (20), DOI `10.5802/crmath.453`; their normalization is
`R_{r,p}^{(1,-1)} = 2^p Q_{p,r}`. The corresponding unshifted `r=1` attribution
already appears in pinned `chapters/04-depth.tex`. Priority of the specific
two-variable resummation has not been established. It should be presented as
a proved synthesis and extension, not asserted to be the first such formula.

Use `Q_{p,r}` rather than reusing the manuscript's `S_{p,r}`: the latter family
in `chapters/04-depth.tex` uses elementary symmetric harmonic numbers
`e_r(n)=[v^r] product_{j=1}^n(1+v/j)`, not `H_n^{(r)}`.

## Error status and integration cautions

No new genuine mathematical error was found in the sampled pinned Gaussian
claims above. In particular, the separation of theorem, candidate equivalence,
certified proximity, and rejection is already explicit and correct. The earlier
false `S8` vector and the false mixed-color symmetry discussed in
`chapters/04-depth.tex`, equation `colors:audit:eq:mixed-counterexample`, are
pre-existing documented corrections, not discoveries of this audit. Formal
quotient dimensions must continue to be distinguished from arithmetic
independence of their numerical period values.

Independent checks for the new fragment are preserved in
`code/derive_parity.py`, `results/parity_checks.json`, and `verification.log`.
They corroborate the analytic proofs; their tiny residuals are not substitutes
for the proofs or new evidence that settles `S6` or `S8`.

## Independent algebra check of the new Mellin section

Read-only audit target:
`sections/02-mellin.tex`.
No algebra error was found in either requested check, and no root source was
edited.

1. **Integer moment table determinant.** For
   `Q_{N,m}(X)=binom(X+m-1,N-1)`, the determinant-one row operation replacing
   row `k` by the `k`th forward difference at zero gives
   `binom(X-1,N-1-k)`. These rows have descending degrees and leading
   coefficients `1/(N-1-k)!`. Reversing the columns gives exactly
   `det(q_{N,j}(m)) = (-1)^{N(N-1)/2}/product_{j=0}^{N-1} j!`, including
   `N=1`. The resulting rational invertibility claim is justified.

2. **Negative-order beta evaluation.** The finite identity
   `Li_{-r}(-x) = sum_{k=0}^r (-1)^{k+1} k! S(r+1,k+1)
   x^{k+1}/(1+x)^{k+1}` has the correct signs and Stirling index/factorial.
   After multiplying by `x^{a-1}/(1+x)^N`, each term integrates to
   `B(a+k+1,N-a)`. Every individual beta integral is convergent on the stated
   common strip `-1 < Re(a) < N`; no divergent-term separation is involved.
   Fixed logarithmic derivatives are justified on compact substrips. The
   formula is a valid independent check of the negative-spectral-order
   cancellations in the Mellin–Lerch expressions.

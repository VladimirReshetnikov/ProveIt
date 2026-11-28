# Source audit and research decisions

Accessed via the GitHub connector on 27 November 2026. The repository was actively being updated; the following are exact **blob** identifiers returned by the connector, not a claim that all reads came from one immutable commit. For a path below, use `https://github.com/VladimirReshetnikov/ProveIt/blob/main/Analysis/GeneralizedRiemannHypothesis/<path>` to see its live version, or `https://api.github.com/repos/VladimirReshetnikov/ProveIt/git/blobs/<sha>` to identify the retrieved blob.

| Relative path | Git blob SHA | Material inspected |
|---|---|---|
| README.md | 7aa9ee91a8e41fdfeb62d46656b3bfed5d228b09 | Corpus history, vendored upstream, unverified merge |
| Article/README.md | c9fe005bd5cbdee34dbcfacf1d5127a59ba46d0d | Current 209-report, 982-page scope; results and statuses |
| Article/sections/src.tex | b0ac2147291b7da3a74cdf6072cc557b1e1f5ee8 | Input statement, arithmetic lattice comparison and one-sided prime remainder |
| Article/sections/fil.tex | ee4a2a3294242cdb7594a09c5b47b350aad5c2fa | Positive interpolation, lower bound, stopband factor, support theorem, prime average, open questions |
| Article/sections/zer.tex | f371b0ba813187a2324184cd75cdf8ac5dd263ab | Prime ramp formula, zero counts, class weights, open question index |
| Article/sections/rec.tex | e45489226dcf219f78ea1c0879db6c8510cc8d60 | Inverse-problem topic index and open-question excerpt |
| Article/sections/ana.tex | ac65e70dd6325fe798dd470ace97a228957603d6 | Analytic detector topic index and open-question excerpt |
| Article/remarkable-results.tex | bc7f7cf2a948f60a9ddfc8abd1950bfbe8f2b6b4 | Assessment and warning about major conjectures |
| Lean/README.md | e38a68316ac775342e8b926c4ce64ccdc091356c | Formalization scope excerpt |
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa | Unbuilt vendor status and upstream pin |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | Actual definitions of RH and Dirichlet GRH statements |

Other section headings (dir, nab, gra, sel) and the Research directory inventory were examined for target selection, not read exhaustively. Root README and article README were not synchronized during retrieval (the former described 194 merged reports plus 15 pending; the latter described 209 merged reports). The target is present in the retrieved `fil.tex` regardless.

## Direct comparison

| Prior label | Prior result | Contribution here |
|---|---|---|
| fil:lem:phase | positive near-lattice interpolation at half-width `(pi+eta)/delta` | reused with full proof |
| fil:thm:cancel | multiplicity-preserving filter, upper `pi*a*log B + O(1+log log B)` | replacement by `pi*a*log B + O(1)` via nested carry |
| fil:thm:slit | additive slit-plane lower bound | reused with proof of the relevant consequence |
| fil:prop:cheb | positive stopband factor | reused with constructive proof |
| fil:thm:optsupport / rec:thm:logfilter | asymptotic optimum with `O(log log B)` error | bounded additive error |
| fil:cor:free | free cutoff optimum with `O(log log L)` error | bounded additive error |
| rec:thm:polylogavg | common positive averages with half-width `(phi(q)/2)*log log X + O_q(1+log log log X)` | bounded excess and explicit arbitrary fixed-order corrections |
| fil:thm:zetaprime | special zeta residue-matched prime filter | does not imply the new bounded-excess multiset theorem or general all-class corrected average |
| fil:sec:open | asks for bounded excess and exact second-order term | first answered, second not answered |

The new allocation proof is independent of the upstream automorphic lattice estimates: it uses the frequency counting law, reuses interpolation from the article, and then uses RH/GRH only for the arithmetic application. No inference from Dirichlet GRH to GRH for arbitrary number fields is made.

## External background checked

- Lean FRO/Mathlib Initiative, 21 Nov 2026: https://leanprover-community.github.io/blog/posts/riemann-hypothesis/ (statement of verification of RH; upstream and article describe the Dirichlet statements).
- Upstream readable proof pin: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207 . Not rebuilt here.
- Bennett, Martin, O'Bryant, Rechnitzer, *Counting zeros of Dirichlet L-functions*, Math. Comp. 90 (2021), 1455–1482, https://doi.org/10.1090/mcom/3599 . Its two-sided count gives the desired aggregate one-sided formula, without any GRH assumption.
- Beurling and Malliavin, *On Fourier transforms of measures with compact support*, Acta Math. 107 (1962), 291–309: related classical multiplier problem, not an input to the proof. No exhaustive literature search or independent priority certification was performed.

## Proof-review checklist

1. Work with half-open bins to assign every repeated occurrence once. R_j is a bin boundary at its own level and the h_j are nested exactly.
2. The lower bin inequality is only used in saturation at heights beyond T_(i+1)/2, where the coefficient a-K/h_i is positive. It does not presume uniform near-lattice spacing of zeros.
3. The coverage proof saturates levels i <= j-2 only. The immediately preceding level may be unsaturated; its residual is exactly a positive part, not an equality with a potentially negative count.
4. Restricting to a finite input is legitimate by monotonicity of the scalar residual recurrence. All low-frequency factors are a fixed finite cost.
5. Each Fourier interpolation class contains at most one occurrence per phase bin; repeat multiplicities occupy distinct factors and are added by convolution. Both the conjugation symmetry and positivity of the density multiplier are checked.
6. The stopband measure is genuinely nonnegative via its Volterra expansion. Its attenuation cost is at most L/B+log(2)/B, uniformly in L.
7. Slit-plane Jensen lower bound charges both stopband and low zeros; zeros at the endpoint contribute zero. The asymptotic constant is unchanged by finitely many central zeros, which are excluded from cancellation.
8. Arithmetic correction signs: at s=0 the ramp kernel has coefficient -1/x times (1/s+1+log x); at negative integer -k the denominator k(k+1) is positive and log-derivative residue negative. For imprimitive factors the correction is E_infinity-E(x), not its negative.
9. Uniform moment proxy prevents the remainder estimate from losing a power of log X at the extremes of the averaging window. The remaining central frequency is explicitly retained.

The checklist is an authorial review, not independent peer review. Python outputs are regressions only.

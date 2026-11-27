# Source comparison and scope of the contribution

## Repository snapshot

The comparison uses ProveIt commit **`497c1844e71393df41914f5b783d5dc9a618eb61`**, dated 27 November 2026. Subsequent changes are outside this comparison.

| Source | Git blob | Role |
|---|---|---|
| `Article/sections/spn.tex` | `e5f321f49431156eeaad10ee72b2f7db4cfbbcde` | Exact compression laws, established asymptotic regimes, and the open question |
| `Article/sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` | Source theorem and transferable mechanisms |
| `Article/README.md` | `b510ecc98c1b86747c4b1736660891dceeb49a1b` | Scope and verification status of the merged article |

All paths are relative to `Analysis/GeneralizedRiemannHypothesis/`.

[Pinned mathematical source](https://github.com/VladimirReshetnikov/ProveIt/blob/497c1844e71393df41914f5b783d5dc9a618eb61/Analysis/GeneralizedRiemannHypothesis/Article/sections/spn.tex)

## What was already established

`spn:thm:complete-law` gives arbitrary finite compression laws. For complementary nondegenerate frames, `spn:thm:balanced` supplies the exact likelihood and optimal residual-singularity test. `spn:cor:balanced-lower` proves persistent dependence in every growing aspect ratio. `spn:thm:nondeg-blind` identifies the limiting full distance for increasingly tall blocks, and `spn:thm:square-block` supplies sharp square-block expansions. `spn:thm:defect-universality` treats square defect nullities. These are inputs and precedents, not new claims of this paper.

The question `spn:q:symplectic` explicitly leaves complementary nondegenerate frames with fixed positive dimension gap unresolved. It also asks much broader questions about radicals, complement dimensions and local rings. This paper resolves the complementary nondegenerate rectangular regime; those broader questions remain outside its scope.

## Further results proved here

For positive even dimensions $a\ge b$, put $d=a-b$. The paper obtains a signed rank-law expansion with an $O_q(q^{-a-b})$ error uniform in $d$. Consequently the rank distance has leading term

\[
\frac{\gamma_\infty}{(q-1)\gamma_d}q^{-a}.
\]

The full matrix distance tends to the same positive constant for every sequence $a,b\to\infty$, with an explicit symmetric first correction. The joint nullities $K=\dim\ker U$ and $L=\dim\ker(J_b-U^TJ_aU)$ satisfy

\[
\left\|P_{K,L}-P_K\otimes P_L
+q^{-b}(q^2-1)\xi_d\otimes\zeta\right\|_1
=O_q(q^{-a-b}).
\]

Their distance from independence therefore has leading coefficient

\[
\frac{2q\theta_\infty\gamma_\infty}{(q-1)\gamma_d}q^{-a}.
\]

The event that exactly one of $K=0$ and $L=0$ holds is asymptotically optimal for distinguishing the joint law from the product of its actual marginals. The paper defines all product constants and signed measures explicitly.

## Published antecedents and novelty limits

[De Boeck and Van de Voorde, Theorem 4.9](https://arxiv.org/html/2407.07486v3) already gives the exact probability that complementary nondegenerate subspaces are disjoint. Combining it with the repository's likelihood identity yields a scalar full-distance formula. Its uniform expansion provides an independent verification here; the underlying exact count is classical.

[Fulman and Goldstein](https://arxiv.org/html/1211.0504v4) establish classical uniform rectangular rank laws and sharp convergence estimates. [Pott, Schmidt and Zhou](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v23i2p8) count pairs of alternating forms with prescribed ranks. These results are relevant antecedents, with different ensembles or conclusions.

The proposed contribution is the uniform signed rectangular comparison and sharp joint dependence expansion. The reviewed sources did not contain these statements. This bounded comparison establishes an extension of the pinned repository; it does not certify worldwide priority.


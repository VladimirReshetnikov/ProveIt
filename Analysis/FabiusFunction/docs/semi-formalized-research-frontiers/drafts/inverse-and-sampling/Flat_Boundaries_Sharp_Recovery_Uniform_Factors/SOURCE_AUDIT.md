# Source and contribution audit

Date: 29 September 2026.

## Repository pin and retrieval

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned tree: `9b24a3a8d545af9624f6ac455f5b548be62818b6`.
Repository reads used the connected GitHub tool. The recursive tree and
research indexes were used to locate relevant existing work; selected source
sections were then read. This is a focused comparison, not a claim to have
read or verified every manuscript in the repository.

The principal predecessor is:

`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Sharp_Stability_Strata_Fabius_Rvachev_Deconvolution/`

Its README and `article.tex` source lines 1000–1238 were inspected. In
particular, the sampling proposition and following limitation at lines
1190–1234 state an upper bound but explicitly do not claim statistical
minimax optimality; they identify Hellinger or relative entropy control and
endpoint flatness as the missing issue.

Additional discovery/context reads included the Fabius package README,
draft manifest, inverse-and-sampling directory listing, research-report
catalogue, and incoming-report procedure. Those indexes were not treated as
proofs of all claims in the indexed manuscripts.

No repository files were modified. A natural intake destination, subject to
the maintainer's classification, is the Fabius frontier's inverse-and-sampling
group as a continuation of the finite uniform-factor recovery reports.
No upload or commit is implied by supplying this package.

## Earlier companion manuscript, read independently

Title: **Gaussian Confounding and Sharp Recovery of Uniform Convolution
Factors: Shifted power sums, minimax estimation, and detection above a
Fabius–Rvachev background**.

Research report prepared for Vladimir Reshetnikov, dated 29 September 2026,
19 pages. Read from the user's Library as
`article(20260929-161307).pdf`, version 1.

Pages 1–2, 5–8, and 17–18 were inspected through file retrieval. Its
Research Question 1 on page 17 asks for unsmoothed up-law sampling minimax
rates and specifically for control of the integrals of squared derivatives
divided by the density and of moving support. Its main model requires a
strictly positive Gaussian variance floor.

Theorem 4.1 and the moment-preserving tangent construction are reused with
explicit credit, with proofs reproduced for self-containment. The present
paper does NOT claim these algebraic results or the positive-floor rates as
new. The earlier report's own repository comparison uses the different pin
`c130dba623c420551d90db41dae7b3d9cff72dfd`.

This Library manuscript is not asserted to be a file in the pinned ProveIt
tree and is not redistributed in the package.

## Primary external literature checked

1. J. Arias de Reyna, *An infinitely differentiable function with compact
   support: Definition and properties*, arXiv:1702.05442 (2017 translation of
   the 1982 article). https://arxiv.org/abs/1702.05442
2. S. G. Bobkov, *Fisher-type information involving higher order derivatives*,
   arXiv:2412.10200v1 (2024). https://arxiv.org/html/2412.10200v1
   In particular, the higher-derivative information functional and
   convolution information inequalities are existing mathematics, not newly
   invented here. The article supplies its own elementary prefix proof.
3. P. Heinrich and J. Kahn, *Optimal rates for finite mixture estimation*,
   arXiv:1507.04313 (2015). https://arxiv.org/abs/1507.04313
4. Y. Wu and P. Yang, *Optimal estimation of Gaussian mixtures via denoised
   method of moments*, arXiv:1807.07237v2 (2019).
   https://arxiv.org/abs/1807.07237v2
5. C. Kleiber, *The generalized lognormal distribution and the Stieltjes
   moment problem*, arXiv:1301.1277 (2013).
   https://arxiv.org/abs/1301.1277

Mixture-estimation papers are cited as context, not applied as though a
mixture and a convolution of independent uniforms were the same model.
The moment-equivalent lognormal example is verified explicitly in the text;
its underlying construction is not claimed new.

## Exact scope of the contribution

Developed and proved here:

- Exact all-order Hellinger asymptotics for infinite summable positive-width
  uniform backgrounds and fixed perturbation laws with all absolute moments.
- Strong L2 square-root convergence, supported by finite-prefix information
  convergence and a finite-prefix boundary analysis.
- A finite-uniform endpoint trichotomy with explicit critical logarithmic
  coefficient, plus precise simple-testing consequences.
- Sharp known-zero-variance minimax lower bounds for finite uniform-factor
  recovery, matching the existing form of the sampling upper rate.
- Unknown-variance hard pairs tending to the zero-noise boundary with one
  variance exactly zero, and the associated matching estimation and detection
  statements.
- Beyond-all-powers Hellinger separation for distinct moment-equivalent
  perturbations, while convolution remains injective.

Not claimed:

- Worldwide priority after an exhaustive search.
- A new definition of higher-order Fisher information.
- New authorship of the companion manuscript's shifted-power-sum theorem.
- A theorem for every arbitrary smooth compactly supported background.
- Uniformity when capacity, prefix length, background, or perturbation laws
  change jointly with the small amplitude.
- A complete classification of mixed collision strata, local asymptotic
  normality, or an efficient globally certified optimizer.
- Formal verification, peer review, or a modification to the repository.

# Source audit and contribution map

## Pinned source

- Repository: https://github.com/VladimirReshetnikov/ProveIt
- Commit: cfab41369737c66ae520d179419509eb719367cd
- Directory: Analysis/GeneralizedRiemannHypothesis
- Article: *Beyond the Riemann hypothesis for Dirichlet L-functions: consequences, transfers and limits*
- User-facing preparation date: 27 November 2026, America/Los_Angeles.

The snapshot's Article/README.md describes a merger of 209 reports into a 982-page article. It expressly distinguishes unconditional results, results using Dirichlet GRH, and reductions whose target estimates remain open. The README also says the merger is not an independent mathematical review. Our new results are unconditional and their proofs are supplied in full; the upstream RH/GRH proof was not rebuilt or independently certified in this task.

Forty-four local article source and bibliography files were checked against their Git blob hashes. The only local transport difference was an added final newline in some files; removing that one added newline recovers the exact source blob. See provenance/article_source_manifest.json.

## Specific source mechanisms and new results

| New paper | Source material | New conclusion | Boundary of the claim |
|---|---|---|---|
| Gram determinants | Article/sections/src.tex, src:thm:gramasym, src:lem:gramcount, src:q:gram | Sharp minimum for n=o(z), z=o(n²), for both at-most and exact zero-minor constraints; explicit squared-potential constant; exact four-square repair | Does not determine the fixed-z sharp asymptotic, higher-rank sharp constants, or a certified unique maximizer of the new potential |
| Positive filters | Article/sections/fil.tex, fil:thm:reflect, fil:thm:perturb, fil:lem:strip, fil:thm:meanbound, fil:thm:hessian, fil:sec:open item 2 | Analytic coefficient-space continuation through collisions at every positive mirror base; positive transverse Hessian and exact local normal form; arbitrary-damping bound; explicit negative mixed curvature | Does not give effective neighborhood radii, uniformity in degree, or a global diagram across zero-mass boundaries |
| Bilinear detection | Article/sections/spn.tex, spn:prop:anchors, spn:thm:anchors, spn:q:dependence | Exact finite likelihood; fixed-codimension rank/Poisson experiment; plateau and corner formulas; Gaussian regime uniform in growing anchor number | Does not solve general overlapping-cycle observation graphs, finite local rings, or nonuniform sampling |

Pinned source links:

- https://github.com/VladimirReshetnikov/ProveIt/blob/cfab41369737c66ae520d179419509eb719367cd/Analysis/GeneralizedRiemannHypothesis/Article/sections/src.tex
- https://github.com/VladimirReshetnikov/ProveIt/blob/cfab41369737c66ae520d179419509eb719367cd/Analysis/GeneralizedRiemannHypothesis/Article/sections/fil.tex
- https://github.com/VladimirReshetnikov/ProveIt/blob/cfab41369737c66ae520d179419509eb719367cd/Analysis/GeneralizedRiemannHypothesis/Article/sections/spn.tex
- https://github.com/VladimirReshetnikov/ProveIt/blob/cfab41369737c66ae520d179419509eb719367cd/Analysis/GeneralizedRiemannHypothesis/Article/README.md

The article's nonabelian and degree-two strands were also examined as possible routes to a prominent conjecture. Their detector identities and analytic reductions still require arithmetic estimates not established here. This packet does not relabel such a reduction as a completed proof.

## Relevant incoming reports inspected

Text was inspected from 21 of the 23 incoming archives listed in the pinned docs tree. This was a duplication check, not an audit of every proof in those archives. The two large uninspected archives were erdelyi_ellipse_and_proveit_extensions.zip and cycle-complements-and-dirichlet-zero-matching.zip. No claim of exhaustive incoming coverage is made.

The closest inspected items were:

- **gram_column_number_2026-11-27.zip**: generic fixed-rank order of growth and bounds allowing at most a fixed number of zero minors. Its stated scope excludes a sharp exact-zero optimum. It does not cover the growing-degeneracy sharp law here.
- **critical_symplectic_experiment_2026-11-27.zip** and **grh_finite_observation_and_critical_recovery.zip**: hidden alternating-form inference from isotropic two-planes. Their model is different from our growing complete-bipartite observations of nonzero vectors.
- **grh_research_extensions_2026-11-27.zip**: finite-population parity and five-observation hidden-form recovery. These do not contain the anchor likelihood or the fixed-codimension Poisson experiment.
- The inspected positive-filter reports and the merged filter section include global phase results, special collision expansions, and a coalesced-frequency Hessian. The general coefficient-space normal form and its transverse nondegeneracy are not stated there.

The incoming reports are not redistributed. Their listed distinction is only as specific as the actual textual comparison.

## Primary literature checked

1. A. Eremenko and A. Fryntov, *Remarks on the Obrechkoff inequality*, Proc. Amer. Math. Soc. 144 (2016), 703–707. https://arxiv.org/abs/1409.4849 and https://www.math.purdue.edu/~eremenko/dvi/fryntov6.pdf.
   Context: angular zero restrictions for polynomials with nonnegative coefficients; the paper is not claimed to supply our collision-compatible filter normal form.

2. W. Singhose, E. Crain, and W. Seering, *Convolved and simultaneous two-mode input shapers*, IEE Proceedings—Control Theory and Applications 144 (1997), 515–520. https://doi.org/10.1049/ip-cta:19971439.
   Context: established cancellation and input-shaping applications. Our contribution is a mathematical local duration/stability theorem with arbitrary positive mirror bases.

3. J. Fulman and L. Goldstein, *Stein's method and the rank distribution of random matrices over finite fields*, Annals of Probability 43 (2015), 1274–1314. https://doi.org/10.1214/13-AOP889.
   Context: classical rectangular-nullity distributions. These are explicitly inherited in our first detection scale.

4. M. Brennan, G. Bresler, and B. Huang, *De Finetti-style results for Wishart matrices: combinatorial structure and phase transitions*, arXiv:2103.14011 (2021). https://arxiv.org/abs/2103.14011.
   Context: dependence induced by shared latent vectors and observation graphs. Their real Gaussian setting differs from our finite-field, nonzero-vector experiment.

5. I. Bárány and N. Tokushige, *The minimum area of convex lattice n-gons*, Combinatorica 24 (2004), 171–185. https://www.renyi.hu/~barany/cikkek/94.pdf.
   Context: sums of absolute determinants; our objective is the sum of squared normalized minors with a multiplicity constraint.

6. B. Kriepke and M. Schymura, *On generic Δ-modular integer matrices with two rows*, SIAM Journal on Discrete Mathematics 40(3) (2026), 1342–1368. https://arxiv.org/abs/2502.15394 and https://doi.org/10.1137/25M1745878.
   Context: a bound on the largest minor and generic column counts. The sharp squared-minor multiplicity law is a different extremal problem.

This review supports a scoped novelty claim relative to the inspected development and literature. It does not establish exhaustive historical priority.

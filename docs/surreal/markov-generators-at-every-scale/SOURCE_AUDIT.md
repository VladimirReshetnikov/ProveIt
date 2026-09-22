# Source and novelty audit

## Date and repository snapshot

Audit date: 22 September 2026.

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned revision: `4cf691c7d951e037739d32d9f5c387dcce724f3c`.

The live repository may change after this revision. The article makes no statement about later additions.

## Repository inspection actually performed

The GitHub connector was used to retrieve the repository tree and documentation, rather than infer their contents from the user's earlier work.

- `docs/README.md`: complete catalogue and its conventions read.
- `docs/surcomplex/spectral-theory/README.md`: substantial report inventory and novelty/limitation discussion read. The connector's long response was truncated near its end; no claim of a line-by-line audit of the underlying 52-page report is made.
- `docs/new`: the complete tree of 18 ZIP archive names was retrieved.
- Indexed GitHub source search for `Markov`, scoped to `VladimirReshetnikov/Surreal`: no results returned.
- The recursive repository tree was retrieved but its very long display was truncated. It was not treated as a full content audit.

The 18 ZIP archives in `docs/new` were NOT expanded. They were named:

```text
hahn_tate_uniformization.zip
surcomplex_exact_and_drifting_multipliers.zip
surcomplex_exact_jet_image.zip
surcomplex_hahn_hilbert_spectral_theory.zip
surcomplex_infinite_spectral.zip
surcomplex_interpolation_research.zip
surcomplex_regular_singular.zip
surcomplex_single_loss_article.zip
surcomplex_tate_uniformization.zip
surreal_autonomous_dynamics.zip
surreal_exponential_automorphism_rigidity.zip
surreal_exponential_rigidity.zip
surreal_holonomic_rigidity(1).zip
surreal_holonomic_rigidity.zip
surreal_localization_bundles.zip
surreal_symbolic_dynamics.zip
surreal_tail_span_research.zip
surreal_theta_research.zip
```

The source search does not establish absence from binary archives, unindexed files, synonyms, or related theorems under other names. Attempts to obtain a container copy of the repository archive were unsuccessful; no local full-text repository audit was performed. The warranted conclusion is that the present theorem package was not found in the inspected material.

## Closest existing repository material

The maintained spectral-theory report already covers finite spectral algebra, singular scales, determinantal methods, perturbation theory, spectral descent, and regularization as a scale filter. These ideas are not reclaimed as original here.

The proposed distinction is the simultaneous treatment of positive Markov resolvents, stochastic retracts with transient mixtures, arbitrary prescribed effective generators at all crossovers, intermediate positivity corrections invisible in the leading hierarchy, and uniform entrywise relative stability including rare entries.

## Primary literature checked

### Classical forest identity: direct mathematical input

Pavel Chebotarev and Rafig Agaev, *Forest matrices around the Laplacian matrix*, Linear Algebra and its Applications 356 (2002), 253–274.

- https://arxiv.org/abs/math/0508178
- https://arxiv.org/pdf/math/0508178
- https://doi.org/10.1016/S0024-3795(02)00388-9

The determinant/adjugate forest formulas and their orientation conventions were examined, including a rendered PDF page. The formula is credited as classical and used as a polynomial identity.

### Nearest metastability comparison

Tingyue Gan and Maria Cameron, *A Graph-Algorithmic Approach for the Study of Metastability in Markov Chains*, Journal of Nonlinear Science 27 (2017), 927–972.

- https://arxiv.org/abs/1607.00078
- https://doi.org/10.1007/s00332-016-9355-0

The abstract and publisher metadata were checked. Their stated scope includes reversible/nonreversible systems and symmetric/nonsymmetric cases, critical times, typical transition graphs, and eigenvalue asymptotics under hypotheses. Their entire paper was not subjected to a theorem-by-theorem comparison. Nonreversibility and optimal-forest eigenvalue exponents are explicitly not claimed as new in the present article.

George Yin and Hanqin Zhang, *Singularly perturbed Markov chains: Limit results and applications*, Annals of Applied Probability 17(1) (2007), 207–229.

- https://arxiv.org/abs/math/0703017
- https://doi.org/10.1214/105051606000000682

Abstract and bibliographic information checked; used as context for established singular-perturbation and aggregation theory, not as a newly proved result.

### Stochastic projection structure

Martin Dyer, Catherine Greenhill and Mario Ullrich, *Structure and eigenvalues of heat-bath Markov chains*, author-hosted manuscript dated 10 April 2014.

- https://web.maths.unsw.edu.au/~csg/papers/DGU-heatbath.pdf

Section 4 and its stochastic-idempotent normal form were inspected, including a rendered page. The present article credits and reproves the stochastic retract decomposition.

### Hierarchical and inverse-M-matrix comparison

Alexander Bendikov and Paweł Krupski, *On the spectrum of the hierarchical Laplacian*, Potential Analysis 41 (2014), 1247–1266.

- https://arxiv.org/abs/1308.4883
- https://doi.org/10.1007/s11118-014-9409-6

Abstract and publisher metadata checked. Its hierarchical, self-adjoint spectral construction is acknowledged as a close predecessor to the reversible special case.

Reinhard Nabben and Richard S. Varga, *Generalized ultrametric matrices—a class of inverse M-matrices*, Linear Algebra and its Applications 220 (1995), 365–390.

- https://doi.org/10.1016/0024-3795(94)00086-S
- https://www.math.kent.edu/~varga/pub/paper_212.pdf

Publisher/search metadata and descriptions checked. This is acknowledged as related matrix theory; no full non-overlap claim is based on this limited inspection.

### Higher-rank specialization context

Michael Joswig and Ben Smith, *Convergent Hahn series and tropical geometry of higher rank*, Journal of the London Mathematical Society 107(4) (2023), 1450–1481.

- https://arxiv.org/abs/1809.01457
- https://doi.org/10.1112/jlms.12716

Abstract and metadata checked. The paper supplies context for higher-rank Hahn specialization. The finite rational sign-separation lemma in the delivered article is not claimed as an original ordered-linear-algebra theorem.

Conway's *On Numbers and Games* and Gonshor's *An Introduction to the Theory of Surreal Numbers* are cited for standard surreal background; the article does not claim a new normal-form or real-closedness theorem.

## Search strategy and limits

Searches covered matrix forests, Markov metastability, singularly perturbed Markov chains, stochastic idempotents, nested projections, hierarchical Laplacians, generalized ultrametric inverse M-matrices, and higher-rank Hahn specialization. Irrelevant results were not used. Searches and selected primary-source readings are not a complete literature review.

No exact prior statement of the full prescribed-crossover realization criterion together with its positivity repair, all-parameter relative stability, and simultaneous marked-diagram specialization was located in this search. This supports presenting the package as candidate original research, not certifying priority for each individual consequence.

## Verification boundary

The general proofs are written mathematical arguments. The exact Python tests are supplementary finite evidence only. There is no proof-assistant verification. No claim is made about countably infinite state spaces, global surreal-valued path measures, or a globally defined surreal matrix exponential.

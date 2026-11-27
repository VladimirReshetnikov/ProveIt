# ProveIt inventory and novelty boundary

Prepared 26 November 2026 (Pacific time). This is an overlap audit and source comparison, not a verification of all predecessor proofs.

## Pinned source and coverage

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected main commit: **041d8032541746f2ac2e686fbe437f8092771670**.
Commit timestamp: 2026-11-27T00:16:22Z (26 November Pacific).
The latest commit adds `prime_observations_and_progression_free_sets.zip`.

The top index records 61 organized research packets (1,795 placed files). Their merged article is described as 499 pages with 558 theorem/proposition/lemma/corollary entries. The index explicitly states that placement was not independent checking and that these Lean files are not part of the root Lake package. These numbers and verification warnings are repository metadata, not conclusions independently recomputed here.

Current nested `Analysis/GeneralizedRiemannHypothesis/docs/incoming` contains **48 additional ZIP archives**, so there are 109 packets in the two inventories. Every one of those 48 ZIPs was located in existing workspace source caches and its complete bytes were checked against the current Git blob SHA before reading. Text members were extracted under `research/prior_packets/`. The checks use Git's SHA-1 of `blob <length>\\0<bytes>`; see `cache_integrity.json` and `proveit_incoming_tree.json`.

Coverage consists of:

- Reading the current top and merged-article READMEs.
- Reading the merged finite-field/spanning section `Article/sections/spn.tex`.
- Reading the primary finite-field predecessors listed below.
- Screening the READMEs and main text of the 48 incoming archives, with deeper reading of the closest finite-field and spectral inverse/covariance papers.
- Targeted primary-literature searches on arbitrary symplectic blocks, form-prescribed frames, subspace counts, and symplectic completions.

This is enough to identify a concrete increment over the supplied collection. It is not an exhaustive worldwide priority search.

## Direct finite-field predecessors

All repository paths below are relative to `Analysis/GeneralizedRiemannHypothesis/`, at the pinned commit.

| Source | What is already there | Consequence for the new claim |
|---|---|---|
| `Research/grh_sharp_torsion_and_symplectic_blocks/symplectic.tex` | Rank-sensitive Fourier bound for the full law of arbitrary rectangular compressions under positive-type weights; for symplectic groups a uniform TV estimate; exact boundary law for isotropic input/output. | Do not claim the passage from scalar Fourier bounds to full matrix distributions as new. |
| `Research/grh_beyond_dirichlet_2026-11-25/sections/rank_moments.tex` | Entire hierarchy of factorial kernel moments using frame stabilizers; rank-tail bounds that can outperform whole-law TV bounds. | Do not claim higher kernel moments, ordered-frame stabilization, or rank tails as new. |
| `Article/sections/spn.tex`, labels `spn:thm:symplectic` and `spn:thm:symplectic-exact` | Merges the generic upper bound and exact isotropic boundary distribution. | This is the clean consolidated predecessor. |
| `docs/incoming/symplectic_rank_blindness_2026-11-26.zip`, main `paper.tex`, Theorem `thm:likelihood` | Exact entrywise matrix law for arbitrary input alternating form and a Lagrangian projection, including radical corrections; exponentially close rank laws with persistently distinct full laws. | New theorem must allow the output restricted form to be arbitrary as well. |
| Same incoming packet, Theorem `thm:growing` | For input-form rank $2s$, rank-law TV is at most $\kappa_q q^{-2s}$, while full-law TV approaches the same positive constant when $s\to\infty$. | Broad rank blindness for growing symplectic part already exists. |
| `docs/incoming/orthogonal_nullity_and_prime_products.zip` | Typical largest principal-kernel threshold for binary orthogonal matrices and an independent prime-product paper. | Not a gap for a new generic extreme-kernel theorem. |
| `docs/incoming/large_kernels_and_dirichlet_zeros.zip` | Rare large-principal-kernel probabilities, conditional uniqueness, exceptional-support distribution, saturation, and progression precision bounds. | Both typical and rare kernel directions have recent predecessors. |

### Explicit prior open questions

The merged article ends its finite-field section with **Question `spn:q:symplectic`**, headed “General symplectic compressions”. It asks for the limiting discrepancy from uniform for arbitrary compressed subspaces, with dependence on their restricted alternating forms. The isotropic endpoint is the established case.

Pinned URL:
https://github.com/VladimirReshetnikov/ProveIt/blob/041d8032541746f2ac2e686fbe437f8092771670/Analysis/GeneralizedRiemannHypothesis/Article/sections/spn.tex

The later rank-blindness packet states:

> The problem with both compressed spaces arbitrary is not settled here.

This is in its section on the increment beyond predecessors. Its final mathematical-scope subsection repeats that only Lagrangian output has been classified.

Pinned archive:
https://github.com/VladimirReshetnikov/ProveIt/blob/041d8032541746f2ac2e686fbe437f8092771670/Analysis/GeneralizedRiemannHypothesis/docs/incoming/symplectic_rank_blindness_2026-11-26.zip

Git blob SHA: `ec19f1ebda1c32ab29b3bc00575962b411c73b7c`.

The proposed arbitrary-form joint law addresses the missing exact finite-dimensional classification. The older question asks about all limiting regimes; a finite law alone should not be described as completing every asymptotic regime.

## Earlier exact Lagrangian-output law

For a random injective $2n\times n$ frame of prescribed alternating Gram matrix $H$ of rank $2s$, let $A$ denote its first $n$ coordinates. Put $K=\ker M$, $k=\dim K$, $t=\dim(K\cap\operatorname{rad}H)$, and
$C_{n,s}=\prod_{j=s+1}^{n}(1-q^{-2j})$.
The predecessor proves the likelihood relative to uniform:
$$
q^{n^2}\Pr(A=M)
=\mathbf1_{H|_{K\times K}=0}\,
\frac{q^{\binom{k}{2}}}{C_{n,s}}
\prod_{j=k-t+1}^{k}(1-q^{-j}).
$$
This formula is not the new result. It should be recovered as a specialization or credited as the nearest existing exact-law case.

## Proposed contribution and permissible novelty wording

The proposed result treats **both source and target restricted alternating forms as arbitrary**, any rectangular dimensions, every finite-field characteristic, and keeps the overlap dimension of the two moving frames.

For combined prescribed Gram matrix
$$
\Gamma=\begin{pmatrix}H_1&M\\-M^{\mathsf T}&H_0\end{pmatrix},
\quad \operatorname{rank}\Gamma=2s,
\quad R=\operatorname{rad}\Gamma,
\quad t_i=\dim(R\cap E_i),
\quad c=\dim R-t_0-t_1,
$$
the explicit coefficient counting allowable relation spaces of dimension $\ell$ is
$$
T_\ell=\sum_k
{t_0\brack k}_q{t_1\brack k}_q
|\operatorname{GL}_k(q)|
{c\brack\ell-k}_q
q^{(\ell-k)(t_0+t_1-k)}.
$$
Multiplying $T_\ell$ by the classical injective-frame count of the quotient and normalizing by the two prescribed-frame orbit sizes gives the joint cross-matrix/overlap law. The elementary support corollary is the exact minimum ambient symplectic dimension
$$
2\bigl(s+\max(t_0,t_1)\bigr).
$$

The frame-count normalization also gives an explicit fixed-dimension first correction in $q^{-2n}$, with a positive leading TV coefficient for nonempty compressions. These are the concrete increments.

Suggested wording:

“The exact joint law, its explicit count of radical relation spaces transverse to both blocks, the minimum-dimension realization formula, and the first uniform-law correction are derived here. They are absent from the inspected ProveIt predecessors. The derivation uses classical form classification, Witt extension, kernel-and-Gram orbit data, and finite subspace counts. A targeted comparison did not locate this combined statement; worldwide publication priority has not been established.”

Avoid claiming:

- A new proof or extension of RH beyond Dirichlet GRH.
- A new kernel-and-Gram classification or a new Witt theorem.
- New generic positive-type full-law Fourier estimates or higher kernel moments.
- Resolution of every growing-dimension asymptotic regime.
- Machine-checked Lean status for these new results.

## Primary literature comparison

### Closest general orbit mechanism

**Robert M. Guralnick, Michael Larsen, Pham Huu Tiep.**
“Character levels and character bounds for finite classical groups.”
*Inventiones mathematicae* **235** (2024), 151–210.
Published online 29 September 2023.
DOI: https://doi.org/10.1007/s00222-023-01221-5

Lemma 2.6 and its proof explicitly classify tuples by their kernel and induced isometric data; Witt's lemma supplies the converse. This is the classical mechanism behind the quotient-by-relations step and must be credited. Their use is to bound orbit counts. The proposed theorem evaluates the transverse-kernel coefficient for two separately injective blocks and turns it into an exact probability and overlap distribution.

### Related exact finite-geometry counts

**Maarten De Boeck, Geertrui Van de Voorde.**
“Anzahl theorems for trivially intersecting subspaces generating a non-singular subspace I: Symplectic and hermitian forms.”
*Linear Algebra and its Applications* **699** (2024), 367–402.
DOI: https://doi.org/10.1016/j.laa.2024.07.004
Author preprint: https://arxiv.org/abs/2407.07486
Full text inspected: https://arxiv.org/html/2407.07486v3

The paper counts nondegenerate subspaces meeting a prescribed subspace trivially and spanning a nondegenerate sum; the prescribed subspace can have arbitrary radical. This is close classical counting work, with a coarser observable than the full cross-Gram matrix of two frames. Its Lemma 1.1 credits the standard count $q^{kj}{n-k\brack j}_q$ for subspaces avoiding a fixed subspace.

**Jun Guo, Fenggao Li, Kaishun Wang.**
“Anzahl formulas of subspaces in symplectic spaces and their applications.”
*Linear Algebra and its Applications* **438**, no. 8 (2013), 3321–3335.
DOI: https://doi.org/10.1016/j.laa.2012.12.008
Primary article page: https://www.sciencedirect.com/science/article/pii/S0024379512008476

Counts of form-constrained subspaces are established literature, not a new ingredient here. The available primary abstract and metadata were inspected; this audit does not claim a full-text comparison of every theorem in that article.

**Zhe-xian Wan.**
“Anzahl theorems in finite singular symplectic, unitary and orthogonal geometries.”
*Discrete Mathematics* (1993).
DOI: https://doi.org/10.1016/0012-365X(93)90013-J
Primary article page: https://www.sciencedirect.com/science/article/pii/0012365X9390013J

The primary abstract describes orbit classification and cardinalities for subspaces in singular classical geometries, including contained-subspace counts. This is a broad source of existing counting machinery. Full-text exclusion of an equivalent formula has not been established.

### Exact sampling

**Keita Ishizuka.**
“Uniform Sampling of Linear Codes with Prescribed Hull Dimension.”
arXiv:2611.03578v2, 25 November 2026.
https://arxiv.org/abs/2611.03578
Full text inspected: https://arxiv.org/html/2611.03578v2

The paper gives exact samplers for prescribed hull dimension in Euclidean, Hermitian, and symplectic settings, in all characteristics, through isometry orbits. Such orbit sampling and frame constructions should be treated as existing tools.

### Matrix completions

**Froilán M. Dopico, Charles R. Johnson.**
“Parametrization of the Matrix Symplectic Group and Applications.”
*SIAM Journal on Matrix Analysis and Applications* **31**, no. 2 (2009), 650–673.
DOI: https://doi.org/10.1137/060678221
Author PDF: https://gauss.uc3m.es/fdopico/papers/SIMAX2009-symplectic.pdf

The author PDF defines the real and complex settings and studies certain prescribed submatrices and completions. Thus symplectic completion questions are not new in general. Its specified blocks and field setting differ from the arbitrary finite-field cross-Gram probability problem here.

## Spectral directions already occupied

The following recent packets were also considered when choosing the finite-field direction:

| Incoming packet | Established claim in its manuscript |
|---|---|
| `robust_dirichlet_spectra_2026-11-26` | Uniform conductor-bounded identification of arbitrary primitive complex characters from signed zero lists, with partial matching, erasures, insertions, and jitter; height $O(\log^2 Q\log\log Q)$. |
| `dirichlet_zero_recovery` | Frequent bounded multiplicity-vector bases in high dyadic zero bands; recovery under positive-density corruption and erasure; separately identifies omitted Euler primes from spacing laws. |
| `grh_spectral_rigidity` | Polynomial zero-divisor rigidity and positive-definite covariance after deleting finite zero bands, including derivatives. |
| `grh_multiscale_covariance` | Positive-definite finite-scale covariance, positive residual variance, uniform directional excursions. |
| `multiscale_prime_fluctuations` | Quantitative finite-band Gram lower bounds for arbitrary fixed scales. |
| `dirichlet_zero_packet_homometry` | Classification of balanced pooled-zero Fourier data, explicit conductor-32045 ambiguity, cubic recovery for odd-order local histograms. |
| `graph_coupled_zeros_2026-11-26` | Forest determinant construction, symmetric matrix model, effective-resistance mean displacement, entire-function extension and collision multiplicities. |
| `li_ritz_zero_recovery` | Moment pencils recovering individual zeros, sharp logarithmic convergence rate, finite simplicity certificates. |
| `zeta_zero_moment_bounds` | Multiplicity-sensitive extreme-atom estimation and exact incomplete-moment optimization. |
| `prime_observations_and_progression_free_sets` | Sparse split-prime Mellin reconstruction for Galois fields, aliased dyadic character-labelled zero reconstruction, and strict progression-free density gains for every length. |

These are statements made and proved in the archived manuscripts, not independently validated conclusions of this inventory.

## Independent check supplied here

`check_radical_transversality.py` implements reduced-row-echelon enumeration of actual subspaces, independently of the main formula-checking program.

The run checks:

- All dimensions through 6 over $\mathbb F_2$, through 4 over $\mathbb F_3$, and through 3 over $\mathbb F_5$.
- 3,614 actual subspaces and 667 parameter comparisons.
- The exact formula for $T_\ell$.
- The sharp positivity condition $T_\ell>0\iff\ell\le\dim R-\max(t_0,t_1)$.

All passed. Recorded output: `check_radical_transversality.json`. The finite checks support the implementation and the delicate combinatorial factor; the general statement follows from the graph-of-an-isomorphism argument, not from these enumerations.


## Constructive realization artifact

`minimal_realization.py` accepts JSON containing q, H1, H0, M, and optionally n. It returns exact matrices F1, F0, J, a relation-space basis, and rank certificates. It builds the maximal relation space explicitly and performs symplectic Gram--Schmidt reduction. It supports prime fields and actual GF(4) arithmetic; the GF(4) representation is documented in the source. It is deterministic and does not claim uniform sampling.

Its exact self-test checks all 805 cross matrices in nine small parameter families over GF(2), GF(3), and GF(4), plus 12 edge cases, including a nonstandard GF(4) form with coefficients x and x+1. The checks verify all three prescribed Gram identities, separate injectivity, the claimed relation dimension, rejection below the proven minimum, and operation in a larger ambient space. Output is in `minimal_realization_checks.json`. The paired example input/output JSON files give a concrete 4-dimensional GF(4) realization of a 3-dimensional block and a 2-dimensional block.

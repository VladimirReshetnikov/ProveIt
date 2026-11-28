# Audit of existing GRH proof-simplification proposals

**Repository:** VladimirReshetnikov/ProveIt  
**Pinned revision:** `89d12dd40424f1217fd818d84877b3da52396a3b`  
**Scope:** `Analysis/GeneralizedRiemannHypothesis/docs/proposals/`  
**Audit date:** 27 November 2026, America/Los_Angeles.

## Completeness and method

All five proposal directories were enumerated through the GitHub connector, recursively, with every tree response reporting `truncated: false`. The resulting collection has **47 files: 42 text files and five PDFs**. Every main LaTeX source, every included LaTeX section, every README and both formalization plans were read in full. The supplied Python, Lean, verification logs and source tables were also inventoried. The PDF content was reviewed through its complete LaTeX sources, not through abstract-only inspection. This is an overlap audit, not a fresh proof audit or kernel replay of the existing proposals.

The same pinned revision was subsequently available as a local sparse checkout. All 47 checked-out Git blobs were verified against their `git ls-tree` SHA-1s. The complete path, Git-blob and byte-size inventory is included as `existing_proposals_manifest.json`. The original proposal files are identified by immutable links and are not redistributed in this archive.

The user's instruction to assume these proposals will likely be implemented means that **a renamed version, a combination of their improvements, or a generic repetition of an explicitly listed research direction is not a new proposal**. A concrete theorem resolving one of their open implementation targets can still be a mathematical advance, but it must be presented as completing that earlier target, rather than as a previously unproposed direction.

Immutable source root for all paths below:

https://github.com/VladimirReshetnikov/ProveIt/tree/89d12dd40424f1217fd818d84877b3da52396a3b/Analysis/GeneralizedRiemannHypothesis/docs/proposals

## Complete proposal inventory

| Directory | Main source(s) | Mathematical contributions already present |
| --- | --- | --- |
| `centered_theta_lift_simplification` | `centered_theta_lifts.tex`; `FORMALIZATION.md` | Centered orbit covariance; direct rank increment on the ramified source; rank tolerance chosen from actual basis-completion cost; smaller translate budget; explicit fourth-logarithm main inequality; optional random contraction-product selection. |
| `proof_simplifications` | `proof_simplifications.tex`, `fourier.tex`, `perron.tex`, `spanning.tex` | Good auxiliary twist from two short Dirichlet polynomials and a quadratic large sieve; elementary Fourier-completion alternative; direct smoothed Perron inversion at the distant cutoff; direct affine rank recurrence on the ramified source. |
| `rh-simplifications` | `rh-simplifications.tex`, `spanning.tex`, `torsion.tex`, `sieve.tex`, `endpoint.tex` | Sharp fourth-order rank deficit from the two moments, with asymptotically sharp constant 19; degree- and test-count-independent torsion specialization by cyclotomic-grid interpolation; finite mollifier/large-sieve prime selection; endpoint assembly. |
| `rh_sparse_theta_proof` | `sparse_theta_proof.tex`; `LEAN_PLAN.md` | Reciprocal-cutoff convexity; fourth-power and dyadic grids; local average cutoff criterion; logarithmic Gaussian second moment; direct averaged good-twist selection; improved exceptional-prime exponent; divergent-prime-subfamily sufficient criterion. |
| `shorter-theta-lift-proof` | `shorter_theta_proof.tex` | Short quadratic correlations, Poisson completion of long smooth blocks, mollification and disk mean-value zero detection; optional large-sieve version; centered rank recurrence; classical PNT for distant cutoff and auxiliary-prime window; ceiling-monotonicity interpolation. |

## Exclusion matrix by mechanism

Line coordinates below refer to the pinned source, and labels are the exact LaTeX labels.

### A. Spanning and rank–covolume interface

| Already covered mechanism | Exact location | Result/interface |
| --- | --- | --- |
| Work inside the ramified source from the beginning, avoiding a separate accumulated codimension loss | `proof_simplifications/spanning.tex`, lines 1–118; `rh-simplifications/spanning.tex`, lines 1–122 | Affine recurrence with limiting deficit `19 b^(-4) + 2 b^(-8)`; total deficit below `20 b^(-4)` on original translate budget. |
| Preserve the original `5 b^(-4)` near-isometry and `9 b^(-4)` second-moment errors | Same sources | Avoid prematurely weakening errors to order `b^(-2)`. This precision retention is already a main proposal. |
| Prove sharpness of constant 19 using a cyclic orbit with invariant complement | `rh-simplifications/spanning.tex`, lines 82–116 | `q_* = 1-(1-alpha-gamma)^2/(1+beta)`; explicit example approaching `19 b^(-4)`. |
| Explain necessity of logarithmic translate budget | `proof_simplifications/spanning.tex`, lines 121–145 | Incidence action on `k`-subsets; uncovered fraction asymptotic to `exp(-L)` after `L D/h` translates. |
| Center orbit covariance and pair with the unfilled projection | `centered_theta_lift_simplification/centered_theta_lifts.tex`, §3, labels `lem:cov`, `thm:increment`, `cor:span`; `shorter-theta-lift-proof/shorter_theta_proof.tex`, §8, `th:span` | Rank gain with leading term `h u`, instead of `h u/2`; error proportional to `sqrt(u)` or `sqrt(u(1-u))`. |
| Adaptive completion using actual cost per missing dimension | `centered_theta_lift_simplification/centered_theta_lifts.tex`, §4, label `thm:C` | Replace fixed rank fraction by `(D-n)(2 x1^2 b^2+b) <= D b`; tolerance `theta = 1/(1+2 x1^2 b)`. |
| Smaller translate budget and retaining explicit logarithm powers | Same paper, §5, equations `eq:Bnew`, `eq:starnew`, `eq:starsharp` | `|J| h_r <= 3 D log b`, sharper asymptotic coefficient; `m R <= 17 f a log(b)^4`; endpoint loss changes from `6 epsilon` to `5 epsilon`. The paper explicitly says the logarithm improvement alone is not a novelty claim. |
| Nonadaptive random choice of translates via products of positive contractions | Same paper, §8, label `thm:random` | Clip singular values, compress to a good spectral subspace, bound expected Frobenius norm of products, recover nearly full span. |

**Additional explicitly proposed research directions:** the centered paper's §9, lines 323–326, already proposes (1) a single rank–height optimization balancing raw completion cost against index; (2) weaker orbital estimates at the chosen tolerance; (3) charging index by newly selected rank, using a refined local lattice or averaged Smith normal form; and (4) a direct exterior-power lower bound controlling partial-volume heights, to eliminate completion. The `rh-simplifications/endpoint.tex` final research paragraph already asks whether special automorphic structure can beat the abstract constant 19. Merely suggesting these again violates the exclusion request.

### B. Local torsion specialization

| Already covered mechanism | Exact location | Result/interface |
| --- | --- | --- |
| Replace Newton polygons/root factorization with finite Lagrange interpolation | `rh-simplifications/torsion.tex`, §3, label `thm:torsion` | Uniform level bound independent of polynomial degrees and number of tests. |
| Sparse cyclotomic grid with bounded interpolation-denominator cost and divergent weight | Same file, lines 15–59, label `lem:capacity` | Weighted bad-node capacity at most reference valuation; add product polynomial to control total valuation after each coordinate move. |
| One character whose first `m` powers all work | Same file, lines 61–70 | Apply the same theorem to `P_i((1+Y)^k-1)`, using radius `r/m` and total budget `m B`; proves the interface of `New/Congruences/Selmer/RootsOfUnity` and `GeneralTheorem`. |

**Already proposed future refinement:** increasing the weight of a cyclotomic grid at fixed maximum order while preserving all Lagrange denominator bounds, in `rh-simplifications/endpoint.tex`, line 67. A new grid optimization must be materially different and concretely proved to count as progress beyond this suggestion.

### C. Good quadratic twists and zero detection

| Already covered mechanism | Exact location | Result/interface |
| --- | --- | --- |
| Large-sieve selection by finite Möbius polynomial with square-pair accounting | `rh-simplifications/sieve.tex` | Saving `c=(beta-1/2)^2/8`; works for complex fixed Dirichlet characters. |
| Two polynomials of length approximately `sqrt(X)` and first absolute moment | `proof_simplifications/proof_simplifications.tex`, §2, label `th:selector`; `shorter-theta-lift-proof/shorter_theta_proof.tex`, §5 | Exceptional count `O(X^(1-(beta-1/2)/2+epsilon))`; same good-twist interface. |
| Elementary quadratic correlations plus Fourier/Poisson completion | `proof_simplifications/fourier.tex`; `shorter-theta-lift-proof/shorter_theta_proof.tex`, §§2–4, labels `lem:short`, `lem:block`, `thm:tw` | Use smooth dual blocks; length `X^(1/4)` mollifier; exceptional count `O(X^(1-(beta-1/2)/4+epsilon))`. |
| Convert a zero at varying complex location into fixed positive disk area | Both preceding routes | Holomorphic submean inequality for `|L M-1|` or its square; avoids pretending zero locations are fixed across twists. |
| Gaussian second moment and direct average prime selection | `rh_sparse_theta_proof/sparse_theta_proof.tex`, §5, labels `lem:gaussian`, `cor:moment`, `thm:density` | `sum J_d^2 = O(T^2 log(T)^3)`; pick a prime minimizing total tail cost; optional density saving every `gamma < (beta-1/2)/2`. |
| Arbitrarily large fixed right edge in three-lines to improve the density exponent | Same paper, §5.4 | Right line `B>1`, threshold exponent tending to `beta-1/2`; already part of the density refinement. |
| Landau with sign-sensitive real residues | Endgame sections of every paper | Existing criterion retained: fix the good twist before sending the cutoff to infinity; ensure no twisted zeros in the entire box so real residues have the required sign. |

None of the existing proposals removes the need for quadratic-twist nonvanishing, replaces Landau by a different Tauberian/pole argument, or proves a weaker finite-pole selection criterion. Such a change could be distinct, provided it actually handles real-axis poles and cancellation and does not simply restate the existing proof. The sparse paper explicitly rejects choosing one arbitrary fixed twist without controlling real residues.

### D. Cutoff, data existence and classical prime estimates

| Already covered mechanism | Exact location | Result/interface |
| --- | --- | --- |
| Direct smoothed Perron inversion | `proof_simplifications/perron.tex`, §4 | Use kernel `1/(s(s-1))`, narrow zero-free region and contour shift; obtain stretched exponential `exp(-log(x)^(1/27)/3)`, bypassing gamma-kernel localization at far cutoff. |
| Fixed-modulus PNT plus tail integration | `shorter-theta-lift-proof/shorter_theta_proof.tex`, §9 | `R(x) = - integral_x^infinity (V(t)-t/phi(q))/t^2 dt`; gives every inverse logarithmic power with correct centering. |
| Siegel–Walfisz for moving auxiliary-prime windows | Same section | Prime in `[exp(U),exp(U+W)]` under the source's modulus/window constraints. |
| Monotone ceiling interpolation | Same section | `R(y) <= R(ceil y)+1/y`, avoiding a local prime-count/Lipschitz estimate. |
| Reciprocal-cutoff convexity with quadratic mesh loss | `rh_sparse_theta_proof/sparse_theta_proof.tex`, §3, label `thm:interp` | `R(x) <= max(R(a),R(b)) + alpha ((b-a)/a)^2/8`. |
| Fourth powers and dyadic grids with fixed chain length per block | Same paper, §3, labels `cor:mesh`, `cor:fourth` | Only `O(X^(1/4))` cutoffs through `X`; do not incorrectly replace power-of-two `m` by an arbitrary square. |
| Local reciprocal-window averages instead of point values | Same paper, §4, equation `eq:average` | Jensen gives upper bound with quadratic variance penalty at window radius `t^(5/4)/4`. |
| Arithmetic only for a divergent prime subfamily | Same paper, §6, label `thm:criterion` | Divergence of `sum (log d)/d` plus sparse cutoff data suffices; choose fixed `d` from family after the hypothetical zero. |

**Already proposed future refinements:** the sparse paper's §7 already asks for fixed-chain-length data construction shared across a dyadic block; an easier arithmetic field/type construction on a favorable extra-congruence prime family; and a direct averaged log-volume estimate. These are excluded as unproved suggestions as well as proved reductions.

## What remains genuinely different at the level of the proposal collection

The following subjects are not targeted by any of these five proposals. They are **audit observations, not claims that the replacements work**.

1. **Congruence-denominator structure before the final torsion-point selection.** The existing interpolation proposal changes how finitely many polynomial tests are specialized. It does not reorganize the Hecke annihilator, local relation module, Fitting ideal, or simultaneous integral operator used to create those tests. A concrete algebraic replacement there would survive all the existing spanning, interpolation and analytic changes. Avoid claiming novelty merely for selecting fewer vectors or for exterior-power completion, which are already suggested.

2. **Finite good-type projectors and their local representation-theoretic filters.** No existing proposal changes the good-type condition, projector construction, coefficient estimates, or the local irreducible-label counting underlying the two moment bounds. A genuine simplification here must prove the arithmetic/type hypotheses needed downstream; weakening the abstract moment tolerances alone is already proposed.

3. **Chain determinant and one-lift normalization identities.** None replaces the special-value/period cancellation, seesaw factorization or exact leading coefficient needed in the determinant lower bound. A telescoping determinant or a less redundant scalar normalization could be distinct if it preserves the signed main term and local index costs. Generic partial exterior-power determinants are already covered as future research.

4. **The transform/pole criterion itself.** All five collections keep the same Landau/real-residue logic and full-box good twist. A genuinely weaker selection target or an alternative nonnegative transform would be distinct, as long as it does not assume the desired zero-free region or lose control of real poles. No claim of an easier proof follows merely from changing the formulation.

5. **Exact specializations of the original geometry that eliminate genuinely unused machinery.** No proposal supplies an RH-only replacement of the finite automorphic type setup. Simply setting the external Dirichlet modulus to one does not do this: the source still uses `Q=18480`, and orthogonality involves all 3840 characters modulo that auxiliary modulus.

## Practical novelty test for the new report

A new report should name the exact input and output declaration(s), state its replacement theorem, prove the key new implication, and explain why the already-planned changes do not subsume it. It should compare against the *combined post-proposal baseline*, rather than against the old raw source alone. Do not count an improved numerical constant, a rephrasing of the centered recurrence, a stronger sparse grid, or a different sieve citation as a distinct main proposal unless the mathematical mechanism and retained dependency burden change substantially.

The present audit establishes nonduplication only within the requested pinned proposal collection. It is not a literature priority search and does not certify global originality.

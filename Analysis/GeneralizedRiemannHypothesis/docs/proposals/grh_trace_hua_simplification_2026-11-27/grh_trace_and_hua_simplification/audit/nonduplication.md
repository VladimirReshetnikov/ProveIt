# Nonduplication audit of the GRH simplification proposals

## Late update

This is the baseline 28-bundle audit. The later three-bundle addendum is in `latest_proposal_addendum.md`; together they exclude 31 distinct bundles across both snapshots.

## Snapshot and scope

The comparison uses ProveIt commit `f2d6ab6c4b70ea73b2deac9e33ad966bc92ea36f`, specifically `Analysis/GeneralizedRiemannHypothesis/docs/proposals`. There are **28 proposal directories, 43 TeX files, and 136 `.tex`, `.md`, and `.txt` files**. The companion manifest records byte lengths, SHA-256 digests and Git blob SHA-1 identities for these text files. The primary text screening comprises **92 papers, README summaries and implementation plans**.

Every primary README summary was read. TeX headings and named future directions were screened, relevant statements and future directions were read directly, and the complete primary text was searched for the candidate mechanisms below. The closest existing proposals were compared at the mathematical mechanism level. This is a targeted semantic audit of the requested repository corpus, not a line-by-line verification of every proposal and not a historical priority claim.

## Ideas already occupied

The 28-row `proposal_matrix.tsv` records each bundle's target, established mechanism, and relevant optional or future directions. Broadly, the occupied territory is:

1. **Twist selection and the analytic endpoint.** Finite Dirichlet polynomials, quadratic large sieves, elementary Fourier/Poisson completion, Gaussian second moments, sparse cutoff interpolation, averaged cutoff bounds, real-only transforms, finite differences, radial Taylor majorization and nearest-pole Landau arguments. The localized real-axis/fixed-point selector and finite averaged twist residues have already been posed as further questions.
2. **Almost-spanning and completion.** Direct rank recurrences, centered moments on the ramified source, adaptive rank-height completion budgets, random products, improvements from `b^-2` to `b^-4`, rank-weighted colength, and exterior-power lower bounds without completion. The last several are explicit future directions and should not be presented as newly proposed questions.
3. **Torsion specialization and labels.** Weighted Lagrange grids, one-shell Newton interpolation, common primitive order, nonprimitive finite-field labels using norm/order tests, and digit/paraboloid sparse-place constructions.
4. **Theta derivative arithmetic.** CM norm cancellation with four copies and finite Frobenius/null-moment/gradient certificates replacing the full coupling normal form.
5. **Theta exchange and determinant metadata.** Orbital matching sections, canonical diagonal sweeps, exact diagonal growth budgets, normalized triangular Gram laws, direct exchange height certificates, exact power descent, and the compact edition's determinant-first architecture.
6. **Local Hecke and Ribet algebra.** Signed integer-lattice enumeration for Pieri cones, integral orbit averaging, exceptional Smith-factor rank tests, integral pivot/flag rows, finite evaluation duality, lattice lengths, Fitting costs and direct Cayley-Hamilton.
7. **Integral fields, adjoints and class counting.** Integral CM presentations and trace duals, explicit different-generator phase, finite quotient unitary class counts, Weyl-Fock Gram inverse adjoints, and calibrated branching adjoints using Schur's lemma and a highest vector.
8. **False-lift descent.** Whole-function averaging at the bottom of the tower, support annihilation by stabilizers, and its generic compact-support formulation.

## Candidate A: line-parahoric trace recovery

The proposed target in `Lib/Adelic/TraceFormula` concerns recovery of the cuspidal trace from auxiliary line-parahoric Hecke operators. The inspected corpus does not contain a proposal about `CuspidalComparison`, `LineDeterminant`, `LevelCut`, or the spectral kernel of that operator family.

The complete primary-text search used:

`TraceFormula|trace formula|CuspidalComparison|LineParahoric|line.parahoric|LineDeterminant|LevelCut|normal operator|spectral kernel|kernel equal`

It returned only two irrelevant hits:

- `projective_incidence_grh/LEAN_PLAN.md:19` says the scalar-character kernel equals a vector stabilizer. This belongs to finite-field point-hyperplane incidence, not parahoric trace recovery.
- `rh_two_order_tests_proposal/two_order_tests/two_order_tests.tex:972` states that the trace formula is unchanged by the proposed label replacement.

The nearest named Hecke proposals are different: `discrete_hecke_simplification` replaces Pieri-cone volume and local saturation proofs in `New/UpperBound/ElementaryDivisors`; `edge_hecke_simplification` replaces integral averaging and exceptional-factor counting there. Neither reconstructs the cuspidal trace from line-parahoric operators. A new theorem about the common kernel, operator symmetry, or positive spectral polynomial in this auxiliary-place comparison would therefore be distinct from the inspected corpus, provided the report establishes the actual source contract and does not merely rename an existing determinant argument.

## Candidate B: the archimedean Bessel/remaining-terms geometry

The proposed target in `New/Spanning/RemainingTerms/OneRealPlace` concerns negative subspaces, positive majorants, coordinate changes and Bessel bounds. The complete primary-text search used:

`OneRealPlace|RemainingTerms|Bessel|negative basis|volumeRatio|isotropic quotient|Schur complement|majorant|reproducing kernel|Gram.Schmidt|positive graph|Sobolev`

There were **zero hits**. The nearest adjacent proposals are:

- `gram_adjoint_simplification`, which uses the rational integral Weyl-Fock Gram inverse in the one-lift comparison operator;
- `grh_simplification`, whose branching theorem uses a Gram adjoint and Schur commutant theorem;
- `projective_incidence_grh`, which shortens the finite-field part of the second moment;
- `centered_theta_lift_simplification`, which changes the abstract rank recurrence after the moment estimates have already been established.

None provides a coordinate-free Schur-complement normalization of the negative-space Bessel calculation. Such a result would be a distinct local mechanism. It must preserve the determinant/volume factor and all norm conventions in the actual real-place estimate. A generic rephrasing of Gram-Schmidt without a concrete shorter proof would not by itself demonstrate significance.

## Candidate C: qualitative parameter selection

A broad asymptotic parameter-selection refactor is not a stated main proposal in this corpus. However `rh_sparse_theta_proof` already proposes a fixed-length block construction, weakening `eventually_exists_data` to a sparse cofinal family, and reusing data uniformly across such a block. `theta-lift-simplifications` already changes the sparse-place constructor in `Data/Existence.lean`. Any parameter proposal must isolate a different mechanism and account for these exclusions. Its significance cannot be assessed from the absence of matching keywords alone.

## How to report novelty

A defensible formulation is: "The new local replacement was compared with the 28 proposal bundles at the pinned snapshot. The closest related proposals act on different source contracts; no matching mechanism was found." Avoid claiming exhaustive novelty in all mathematical literature, or claiming that an already posed research direction becomes a new proposal merely because it has not yet been implemented.

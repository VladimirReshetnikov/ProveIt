# Claim and verification boundary

## Proved in the article

- Exact all-iterate degree recurrence and first dynamical degree of the baseline.
- Every positive weighted degree, the downward-completed Newton polyhedron,
  and the whole initial form at the positive-weight wall.
- A support-robustness theorem and a general weighted-eigenvector lemma.
- Exact degree laws and the first-dynamical-degree spectrum for every
  polynomial source shear `F o T_h`.
- Complete baseline/shear degree laws in characteristic three.
- A monomial escape theorem under a simple expanding eigenvalue, positive
  right eigenvector, nonnegative left eigenfunctional, and strictly contracting
  remaining spectrum; verification of those hypotheses for the displayed maps.
- Maximal arithmetic degree for all integral points in the escape region,
  and Zariski density of the collection of such initial points.

Known baseline identities and generic field degrees are rederived separately.

## Computational evidence

The exact verifier passed all thirteen groups with SymPy 1.14.0.
It checks polynomial identities, complete baseline support, finite matrix
identities, and finitely many exact monomial-curve compositions over finite
fields. Its univariate restriction tests are not exhaustive multivariate
expansions. The all-iterate and all-parameter conclusions depend on the written
proofs, not on finite sampling. The analytic escape theorem is proved on paper,
not established by a simulation.

The calculator is tested independently against the matrix recurrence and
characteristic-three formulas. It evaluates these proved formulas; it is not
an independent symbolic degree detector for arbitrary maps.

## Formal verification

The pinned original Lean source was inspected for the map, determinant,
and collision declarations. The repository's compiled Lean/Rocq proofs were
not rerun. None of the new article's results has been kernel-checked here.
No uncompiled Lean or Rocq file is included or advertised as a proof.

## Not claimed

- Discovery of the original map or of its shear construction.
- First historical proof of any result; a complete priority search.
- Classification of unrestricted Keller maps or global degree-seven minimality.
- The second dynamical degree or an algebraically stable compactification.
- A topological-entropy formula, global Green function, or global canonical height.
- That each orbit in the escape region is Zariski dense.
- Arithmetic/dynamical degree equality for every Zariski-dense rational orbit.
- The full Newton polytope or all lower coefficients.
- Finite-set cycle statistics from polynomial-degree formulas.
- A Keller condition in characteristic two.

This is an independently derived, AI-assisted research draft and should undergo
expert proof review before publication or incorporation into a trusted library.

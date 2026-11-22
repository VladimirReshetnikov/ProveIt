# Repository audit: reusable iPRA foundations and the norm frontier

## Snapshot and scope

Repository: `VladimirReshetnikov/ProveIt`.
Pinned main commit: `3ee850b4c2d650cf01263823fd5415963747c5d0`.
The branch API recorded commit time 2026-11-19 19:31:01 UTC.
The audit read the source files listed in `source_manifest.json`; it did not rebuild the repository.

The top-level README and the proof-packet index have stale aggregate counts. Use exact theorem/module boundaries rather than repeating their headline packet counts. Archived packets are filed as delivered and were not rechecked at intake. The current `Derivations/README.md` and `Derivations/FINITE-DEMAND-CLAIMS.md` substantially supersede the old packets' formalization-status paragraphs.

The ordinary object endpoint is `Prf PRAAx [] sentence`, or a finite-context variant. The separate Foundation bridge transports this endpoint. A theorem about standard Lean naturals, a compiled definition of a target proposition, and a derivation in that object theory are different deliverables.

## What already exists and should be reused

The following status is reported by the current source audit and backed by inspected theorem declarations where noted. It is not a fresh whole-repository verification.

| Component | Current source boundary | Consequence for a new report |
| --- | --- | --- |
| Fixed bounded syntax | `Foundations/BoundedSyntax.lean`: arity-indexed `BFm n`, capture-avoiding `formula_subst`, actual `bitF`, `compile_correct`, arbitrary-context/term `bounded_reflection`, closed exports | Do not describe bounded Booleanization itself as a missing generic framework. |
| Induction over bounded syntax | `Foundations/BoundedSyntaxInduction.lean` compiles bounded formulas to a bit and uses ordinary QF induction | State concrete finite invariants and connect them to this existing compiler. |
| Backward demand and changed parameters | `BackwardDemand`, `ParameterChangingRecursion`, `FiniteQueryDemand` have actual PR constructors and embedded endpoints | Demand DAGs, finite-horizon scheduling, and predetermined changed-parameter recursion are inherited. |
| Rational aggregates | `AggregateChain`, `AggregateOptimization`, nearest-point and finite-Hausdorff modules have actual names and exact budgets | Shrinking witnesses, nearest-neighbor coherence, and approximate optimizer names are inherited. Exact minimizers are not silently supplied. |
| Root supports | Concrete monic descent, approximate factorization, root support and completed root adequacy are assembled with actual PR programs | A new branch-free root-support proposal would mostly repeat completed work. |
| Framework composition | Numerous archived frameworks and current `FiberCompiler`, `Realizer...` modules already implement cut, scope sealing, bounded trace/strategy machinery | Prefer a mathematical producer theorem and a concrete connection to the object library. |

The current finite-demand audit explicitly marks the polynomial-norm family as a remaining frontier. That is a better focus than another renamed contract formalism.

## Norm results already proved in the human reports

### The finite-demand paper

Exact original source:
`docs/proofs/foundations/ipra_finite_demand/sections/05_norm_certificates.tex`.

For a monic equation `F(X,Y)` of Y-degree m, it constructs the multiplication matrix of the reduced G and its determinant `N_G(X)`. Its theorem `thm:general-norm` proves:

- If `N_G != 0`, any supplied finite list of distinct common zeros has length at most `deg N_G`.
- A fiber over a fixed x-coordinate with t distinct y-coordinates contributes `(X-a)^t`, not just one factor.
- The proof completes the evaluation rows to a Vandermonde block, factors the first t rows of the transformed matrix, and combines coprime linear factors.
- Singular curves and ramified fibers are allowed.
- A coarse degree bound is `m(a+(m-1)c)` under coefficient-degree bounds a,c.

For `F=Y^m-f(X)`, `deg f=d>=1`, and `gcd(m,d)=1`, `thm:norm-degree` proves exact degree
`W(G)=max_i (m deg A_i+d i)`
and automatic nonvanishing by the unique maximal weighted cyclic determinant term. The proper-subspace corollary `cor:norm-subspace` uses a finite Gaussian-elimination annihilator and gives the fiber cap L for the weighted monomial map.

This paper does not give a finite-place nonvanishing criterion and does not prove general Siegel or Faltings. Its noncoprime treatment only retains the computed nonzero-norm hypothesis.

### The coherent-methods paper: an important earlier generalization

Exact original source:
`docs/proofs/foundations/ipra_coherent_methods_2026-11-15/paper/sections/05_norms.tex`.

It already treats weighted mixed-term curves
`F=Y^m-cX^d + lower-weight terms`
and gives a rescaling proof of the exact degree theorem. More importantly, its subsection **A broader finite certificate when coprimality fails** already forms
`C(F,G)=det(mult by G_0 on Q[Z]/(F_0))`
after weighted rescaling, and proves `C(F,G)!=0 => deg N_G=W(G)` without coprimality. Therefore a generic initial-form determinant certificate is inherited, not a new discovery.

The source also derives a domain property from nonzero norms, and the weighted proper-subspace/finite-cover endpoint. It does not contain the compressed gcd-sized leading coefficient computation or the finite-place simple-root argument proposed in the new report.

## Exact current Lean frontier

Read `Derivations/FINITE-DEMAND-CLAIMS.md`, especially its theorem table and the sections on the actual original-row norm and completed fiber matrices.

| Current module | Actual established construction or law | Remaining dependency |
| --- | --- | --- |
| `Analysis/GaussianPolynomialMultiplicationMatrix` | Numerical polynomial matrix from original reduced coefficient rows; actual evaluation action | General high-Y reduction adapter, when needed |
| `Analysis/GaussianPolynomialDeterminant` | Actual numerical permutation scan and signed polynomial fold; coefficient and evaluation Leibniz formulas | Full numerical determinant algebra and exact nonzero degree |
| `Analysis/GaussianPolynomialMonicNorm` | Actual PR5 norm program, canonical output, all returned fields, width bound, literal curve action | Matrix kernel to norm zero, nonvanishing, sharp degree, fiber multiplicity |
| `Analysis/GaussianRationalCurveFibers` | Original field-x grouping, distinct y lists, specialized F/G roots, fiber size <=m, original partition count | Sharp contribution of each fiber to determinant order |
| `Analysis/GaussianRationalFiberVandermonde` | Actual completed matrix W and W*M; first t polynomial rows vanish at selected x | Determinant transport and row-factor extraction |
| `Analysis/GaussianRationalLagrangeCardinals` and `GaussianRationalFiberRightInverse` | Actual inverse data; the whole completed matrix W has a constructed right inverse Z; original source point hypotheses discharge all local validity premises | From WZ=I to det W !=0 for the same numerical determinant, then multiplicity |
| `Analysis/GaussianPolynomialColumnAlternation` | Negation of actual evaluated determinants under adjacent column exchange, with the same numerical word/rank transport | Stored coefficient alternation, row alternation, multiplicativity |
| `Analysis/GaussianRationalPolynomialProductDegree` | Actual convolution leading coefficient and computed-degree additivity for nonzero inputs | Unique extremal determinant term and norm endpoint |
| `Foundations/WeightedMonomials` | Coprime uniqueness of weights; a finite cover counting schema | Leading coefficient/norm degree/fiber bound |
| `Foundations/CofactorAnnihilator` | Fixed Lean-size cofactor vector orthogonal to rows and their span | Nonzero vector for arbitrary rank-deficient runtime matrices; pivot/free-column producer |
| `Foundations/NullVectorDeterminant` | Fixed Lean-size adjugate/null-vector determinant implications | Runtime numerical-dimension determinant bridge |

The inspected current declarations include:
- `GaussianPolynomialMonicNorm.actual_monic_norm_closed`,
  `returned_norm_evaluation_closed`, and `returned_zero_action_closed`;
- `GaussianRationalFiberRightInverse.whole_matrix_right_inverse_closed`,
  `original_fiber_inverse_closed`, and `returned_source_inverse_closed`;
- `GaussianPolynomialColumnAlternation.actual_column_evaluation_neg_closed`.

These endpoints are useful existing ingredients. Their types do not claim the full zero-count or weighted norm theorem. A report should not label the whole norm pipeline kernel-checked because these ingredients have been implemented.

A useful implementation simplification is to use the already constructed WZ=I to establish det W !=0, rather than first implementing the literal Vandermonde product formula. The product identity remains an independent source obligation if the report promises it, but the multiplicity theorem itself only needs invertibility.

## Mathematical extension worth retaining

The new finite-place criterion is a substantive extension of the inspected sources:

Given explicit a and e with
`f(a+T)=T^e u(T)`, `u(0)!=0`, and `gcd(m,e)=1`,
every nonzero reduced G has nonzero norm. For the translated coefficients A_j, the least weight
`min_j (m ord_T A_j(a+T)+e j)`
has a unique minimizing index. The corresponding cyclic determinant term is the unique lowest-order term.

This uses finite polynomial coefficient scans and determinant arithmetic; it needs neither a factorization producer nor an irreducibility oracle. It combines with the global upper bound `deg N_G<=W(G)`, valid without global coprimality, to extend the proper-subspace fiber cap.

In particular `f=X^d+X` has a simple root at zero for every d>=2. Thus the same cap works for `Y^m=X^d+X` for all m,d>=2, including gcd(m,d)>1. Example: m=2,d=4,G=Y-X^2 has norm -X. The global top terms cancel, but the local certificate proves nonvanishing; the norm degree is 1 rather than the upper weight 4.

A second refinement is compression of the already inherited leading determinant. With g=gcd(m,d), h=m/g, maximal-weight indices lie in one residue class r modulo h, so the top polynomial is `Z^r A(Z^h)`. Its norm in `K[Z]/(Z^m-c)` is
`((-1)^(m-1)c)^r * Res(U^g-c,A(U))^h`.
This reduces the test to dimension g and is explicit finite arithmetic. State it as a refinement of the coherent-methods initial determinant, not as the first noncoprime certificate.

Neither refinement supplies a quantitative Subspace Theorem, an exceptional-subspace cover for arbitrary Diophantine inputs, a height cutoff, or a complete point list.

## Deep barriers that remain mathematical

The original Siegel route, `siegel_ipra/paper/05_general_route.tex`, already separates the easy final count from the hard cover producer. For a finite list of t vectors and a putative M-subspace cover, candidate covers can be chosen among spans of input sublists; there are at most `(2^t+1)^M` padded candidate lists. Bounded search for one is PR. Proving that it always succeeds is a finite-tuple quantitative approximation theorem and is not supplied by the existence of the search.

The Faltings report explicitly does not prove the general theorem, and makes no unprovability or independence claim. The count/height distinction is essential: a bound on the number of points is not a stopping rule that locates them. Complete lists and height bounds are constructively equivalent for its canonical point predicate, but cardinality bounds alone are weaker.

For Mordell-Weil, the height descent and bounded division arithmetic remain conditional on an actual finite covering list modulo multiplication and the relevant complete enumeration data; renaming these as interface fields does not construct them.

## Source and delivery conventions

- Pin links to the commit above. The source manifest records exact paths and Git blob identifiers.
- Credit generic finite-observation, bounded syntax, rescaling/initial-form norm, and finite cover machinery to existing reports.
- Describe new human proofs separately from actual compiled modules and remaining object-level theorem targets.
- The proof-packet README records Vladimir's instruction, “We don't need any checksum manifests.” Do not add a list of checksums for the delivery. Source provenance records are retained by the repository and are appropriate.


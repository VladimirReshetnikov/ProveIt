# Analytic and topology source audit

Pinned ProveIt revision: `5f3be02388442f16487d2dc5c2529961dd783d2b`.

All repository paths below are relative to `Logic/PrimitiveRecursiveArithmetic/`. They were fetched through the GitHub connector at that exact revision. The source states its own Lean verification status; this session did not rebuild the repository.

## Relevant existing source inspected

1. `docs/proofs/topology/ipra_topology_framework_2026-11-15/paper/sections/04_observation_towers.tex`: finite complexes, strong carriers, observation towers, ambiguity-preserving map composition. Explicitly treats a theorem as a schema for fixed PR evaluators or a finite-prefix certificate; semantic reconstruction remains an application obligation.
2. `docs/proofs/topology/ipra_topology_framework_2026-11-15/paper/sections/07_topological_library.tex`: finite compactness contracts, moduli, apartness, effective atlases, need for compatible approximate fixed points. Its statement that stronger exact fixed point extraction needs additional information is retained.
3. `docs/proofs/topology/ipra_topology_framework_2026-11-15/paper/sections/08_case_studies.tex`: Jordan, dimension, nerves, surface examples; several theorem-specific invariants remain obligations.
4. `docs/proofs/topology/ipra_topology_framework_2026-11-15/paper/sections/12_limits.tex`: explicit limits, including no uniform PR universal evaluator, no apartness from mere negated equality, no missing modulus from finite verification, no coherent point from unrelated approximate witnesses.
5. `Derivations/Lean/IPRADerivations/Analysis/RationalArgmin.lean`: actual least rational argmin scan, independently positive denominators; `selected_minimal_closed`, `selected_least_closed`, `selected_program_closed`. Hence a finite rational minimum selector is existing infrastructure and is not a new result of this report.
6. `Derivations/Lean/IPRADerivations/Analysis/DyadicCauchy.lean`: `dyadic_cauchy`, `dyadic_endpoints`, and `certificates_coherent` produce object derivations from adjacent-motion contracts.
7. `Derivations/Lean/IPRADerivations/Foundations/CoherentMinimizer.lean`: gap and uniqueness contracts imply regularity of an explicit selected sequence (`cauchy`). Its header says canonical evaluation at the resulting point and uniqueness of the point name are not derived there.
8. `Derivations/Lean/IPRADerivations/Foundations/StrongMinimizer.lean`: actual finite-net selected points, quantified strong convexity residual certificate, object `selected_pair_closed`. Identifying residual with objective gap is explicit.
9. `Derivations/Lean/IPRADerivations/Foundations/DiscreteGronwall.lean`: finite recurrence `gronwall`; rational integer growth `growth`; `gronwall_three` with factor `3^A`.
10. `Derivations/Lean/IPRADerivations/Foundations/OdeRefinement.lean`: `node_bound` and `geometric_cauchy`. Its header explicitly retains the geometric recurrence of actual Euler polygons as a hypothesis. This is a precise target for the new polygon adapter.
11. `Derivations/Lean/IPRADerivations/Foundations/OdeUniqueness.lean`: `unique_step`, `recurrence`, `uniqueness_nodes`, `uniqueness_const`. The source explicitly leaves choice of precision N,p and equality of two original name families outside this file. The new chapter supplies those constructions and proof obligations.
12. `Derivations/Lean/IPRADerivations/Foundations/ContractionIterates.lean`: abstract coded invariant ball and finite Picard iterates; `iter_contract` and `cauchy_iterates`. Coefficient names and majorant arithmetic are not derived there.
13. `Derivations/Lean/IPRADerivations/Foundations/ContractionTrace.lean`: arbitrary rational contraction factor, `contraction_iter`, `contraction_unique`, and finite sufficient step count `steps_suffice`; coefficient error DAG remains outside.
14. `Derivations/Lean/IPRADerivations/Analysis/OdeCertificates.lean`: Wronskian and Jacobi substitution polynomial identities. Its header says derivatives of named functions and chain rule are not formalized. Do not describe this module as proving analytic ODE existence.
15. `Derivations/Lean/IPRADerivations/Analysis/RationalHausdorff.lean`: positive denominator normalization, original-coordinate finite Hausdorff comparison, `original_code_cover_iff`, checker reflection.
16. `Derivations/Lean/IPRADerivations/Analysis/RationalHausdorffImage.lean`: local finite Lipschitz transport for actual rational lists, independent source/target normalizations, `rational_image_closed`, `checked_image_closed`. This is existing infrastructure, not novelty in the new chapter.

## New chapter contribution and status

The chapter `sections/analysis_topology.tex` supplies full human proofs of the following, conditional on explicit evaluator contracts already proved in iPRA:

- Rational Lipschitz quadrature and derivative/integral interpretation with explicit precision schedule.
- An actual rational Euler iteration with an invariant tube; the recurrence is proved from the evaluator contract rather than assumed.
- Uniform comparison of any two constructed Euler polygons using a common finite refinement and the existing rational Gronwall factor.
- A primitive recursive schedule N_n=2^(n+c), p_n=n+c producing a regular solution name, then an integral-equation and differentiability adequacy proof.
- Equality of original solution names and perturbation stability, with an explicit finite sample schedule and no hidden rounding constant.
- A genuine holomorphic Cauchy transform of boundary data on a rational polygon, with exact rational clearance certificate, quadrature, derivative evaluators, Taylor coefficients, and geometric tail bound.

The Cauchy operation is on the positively separated open complement, defined by a positive clearance. It does not identify mere negated membership with apartness. It does not assert the general Cauchy integral formula or residue theorem, which require additional interior/topological hypotheses.

The new human proofs have not been converted into compiled `Prf PRAAx` derivations. The chapter gives precise object targets and a dependency-ordered Lean plan. Its status must remain distinct from existing source declarations.

## Constants used by the exact demonstrations

For Euler: B=M+1, K=Lt+Lx B, A=ceil(Lx T), G=3^A, C=G T(1+K T), c=ceil(log2(8 max(1,C))) by bounded search. For F=x, x0=1, R=1, M=2, T=1/4, Lt=0, Lx=1, this gives B=3, K=3, G=3, C=21/16 and c=4.

For Cauchy: polygon l1-length upper bound ell, clearance delta, boundary bound M, boundary Lipschitz constant K. N subdivisions per edge and evaluation error eta give `(K/delta+M/delta^2)*ell^2/N + ell*eta/delta`. The r-th coefficient integrand has Lipschitz constant `K*delta^(-r-1)+M*(r+1)*delta^(-r-2)`. The Taylor remainder for |h|<=delta/2 is at most `2*ell*M/delta*(|h|/delta)^m`.

## Review notes

- The ODE construction never assumes a solution to prove Cauchy convergence; comparison is directly between two finite tables.
- The tube condition `T*(M+1)<=R` justifies every evaluator call, including finite-precision slope error.
- All-precision statements are first-order formulas for fixed PR families. Numerical precision variables do not justify higher-order induction.
- The uniqueness comparison uses rational distances of approximate node values: if each state approximation has error eps_p, the added total error is bounded by `G*(4*N+2*Lx*T+4)*eps_p`.
- Higher Cauchy derivatives use a finite binomial identity: with z=h/u and v=z/(1-z), |v|<=1, |v-z|<=2|z|^2, and `(1-z)^(-b)=(1+v)^b`. The second-order remainder is at most `2^(b+2)*delta^(-b-2)*|h|^2`; no unjustified infinite differentiation is invoked.
- Independent review added domain-safe named-time evaluation: rational time approximants are clipped into [0,T]. Evaluation of F(s,y(s)) uses the in-tube Euler polygon point P_m(s), not arbitrary rounded states.
- Uniqueness explicitly assumes a common comparison domain for both fields and fixed PR name evaluators or supplied finite node batches. Identification of semantic higher derivatives is external; the uniform internal theorem is the rational kernel increment/remainder estimate.

# Theorem and verification ledger

All 25 theorem, lemma, and proposition statements have human proofs in the report. Three additional numbered entries are definitions. “Compiled” below means host Lean verification of the stated finite kernel, not a new object-iPRA derivation. None of the new infinite analytic endpoints has been reified as `Prf PRAAx` in this package.

| Report | Result | Required data / scope | Evidence | Formalization route |
|---|---|---|---|---|
| 2.1 | Regularization with an explicit rate | PR Cauchy rate; prefix maximum for monotonicity | Human proof | Measure and CategoryTopology blueprints: name constructors |
| 2.2 | Stable-observation lifting | Finite Lipschitz bound in the chosen observation norms | Human proof | CategoryTopology blueprint: extend_rapid / extend_sameName |
| 2.3 | Bounded replay rule | Proved quantifier-free initial and step invariants; PR bounded iteration | Human proof of the object-theory rule | OBJECT_LANGUAGE_PLAN.md and inspected PRA.qfInd interface |
| 3.2 | Finite integral estimates | Rational dyadic arrays and positive finite weights | Human proof; selected finite energy kernels checked in Lean | Measure blueprint: refinement, sums, and finite Cauchy–Schwarz |
| 3.4 | Effective unions | Named sets plus an explicit tail modulus | Human proof | Measure blueprint: Boolean names and finite union bounds |
| 3.5 | Fubini as an operator on names | Rectangle L1 names; contractive partial averaging | Human proof | Measure blueprint: partial averages and Fubini |
| 3.6 | Conditional averages with a derived rate | Strong L1 name and levels of its approximants | Human proof | Measure blueprint: conditional averaging and tower |
| 3.7 | Clipping kernel | K >= 1; arbitrary finite nonnegative weights | Human proof and compiled finite rational Lean inequalities | Truncation.lean: truncation_rho_pointwise / truncation_rho_integrated |
| 3.8 | Vitali without a pre-supplied limit | Bounded-metric Cauchy rate and uniform excess-tail cutoff | Human proof; clipping kernel compiled | Measure blueprint: VitaliData and explicit name producer |
| 3.9 | Two producers for uniform integrability | Uniform L2 cap, or an L1 dominating name with certified order | Human proof; scalar L2 bound compiled | Truncation.lean: excess_l2; Measure blueprint: tail producers |
| 3.11 | Orthogonal energy identity | Coherent nonnegative dyadic masses | Human proof; finite algebraic kernels compiled | Energy.lean: dyadic_energy_finite / finite_orthogonal_energy |
| 3.12 | Effective Radon–Nikodym fragment | Coherent masses and a PR energy-tail modulus | Human proof | Measure blueprint: DensityData, conditional averages, uniqueness |
| 3.13 | Local producer for the energy modulus | Sibling density difference <= L * 2^(-n) | Human proof | Measure blueprint: sibling estimate and finite geometric energy bound |
| 3.14 | Finite energy metastability | Energy cap; fixed PR challenge function; rational tolerance | Human proof; bounded small-increment search compiled | Energy.lean: smallWindow / smallWindow_sound / energy_window |
| 3.15 | No uniform full rate from the cap | Uniform effective extraction from codes for all stated mass presentations | Human halting-reduction proof | Measure blueprint and exact delayed-jump demonstrations |
| 4.1 | Quantitative bounded-operator extension | Finite linear map and explicit rational norm bound | Human proof | CategoryTopology blueprint: BoundedQLinear and name extension |
| 4.2 | Bilinear extension on bounded inputs | Finite bilinear bound and input norm bounds | Human proof | CategoryTopology blueprint: BilinearBounded and common-bound comparison |
| 5.1 | Compositional L1 sensitivity | Context-aware atoms, Lipschitz connectives, integration, certified pullbacks | Human proof | CategoryTopology blueprint: syntax, evaluation, sensitivity induction |
| 5.2 | Diagonal and supremum obstruction | Arbitrary L1 predicate classes | Human counterexample proof | CategoryTopology blueprint and exact diagonal-square examples |
| 5.3 | L1-to-uniform upgrade | Common Lipschitz bound on a finite-dimensional cube | Human proof | CategoryTopology blueprint: quantitative regularity upgrade |
| 6.1 | Explicit homotopy for contiguous maps | Finite simplicial data and F2 chains | Human proof; extensive finite identities tested | CategoryTopology blueprint: chain encoding and prism cancellation |
| 6.2 | Finite distortion certificate | Finite labelled correspondence and certified distortion | Human proof; finite examples tested | CategoryTopology blueprint: Rips maps, composites, and homotopies |
| 7.1 | Contractive integral equation | Column-norm kernel name; input L1 name; explicit contraction gap | Human proof; exact examples tested | Analytic blueprint: operator bounds, Neumann sums, residual, perturbation |
| 7.2 | Analytic observation of an L1 name | L1 input and rational disk/denominator guard | Human proof; exact finite identities tested | Analytic blueprint: complex guards, quadrature, derivative, moment tails |
| 8.1 | Shared error budget | Finite acyclic dependency graph with local rational sensitivities | Human proof; exact example tested | Analytic blueprint: reverse sensitivities and local budgets |

Additional developed constructions include the concrete L1 tensor identity, probability-kernel composition, compression bounds, interval-distance Rips inclusions, and finite-rank factorization through an epsilon-net. Their full arguments and implementation targets are in Sections 4–6 and the category/topology blueprint.

The independent mathematical reviews and the resolution record are in `validation/`.

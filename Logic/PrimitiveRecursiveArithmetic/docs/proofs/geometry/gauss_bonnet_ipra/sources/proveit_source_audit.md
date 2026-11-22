# ProveIt source audit for constructive Gauss–Bonnet

Inspected snapshot: `d36b35eed5bd01af4ade66bf539622495813ccc8` (main head returned by GitHub on this run; commit author timestamp 2026-11-22 01:33:01 UTC). User-facing local date is 2026-11-21. This is a source inspection, not an independent rebuild of ProveIt.

All following paths are relative to `VladimirReshetnikov/ProveIt` and were read through the selected GitHub connector. Pin source links as `https://github.com/VladimirReshetnikov/ProveIt/blob/d36b35eed5bd01af4ade66bf539622495813ccc8/<path>`.

## Foundation and verification boundary

- `Logic/PrimitiveRecursiveArithmetic/README.md`, blob `a998cff2fb389272cfe1052eeedb0f2a6b826198`: identifies iPRA as first-order intuitionistic natural deduction with PR defining equations, successor axioms and quantifier-free induction. Distinguishes checked `ConciseIPRA`, `Derivations`, `Bridge` from research packets under `docs/proofs`, which are filed as delivered and must not be treated as collectively verified. Its packet count is old; no quantitative census is used in our report.
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`, blob `3251631592070d9ed3687cc0bf7dbd5eb452e46f`: defines `PR`, `PTm`, `PRAAx` and `PRA.qfInd`. `PR` has constructors zero, succ, proj, comp, prec. `PRAAx.ind` requires a proof of `φ.QF`. The desired deep endpoint is `Γ ⊢[PRAAx] φ`; an ordinary Lean theorem about reals or rationals is not that endpoint.
- `lean-toolchain`, blob `94b9f495baff80fd9cb44aad8f4762cb3b2066fe`: `leanprover/lean4:v4.32.0`.

## Directly relevant checked source modules

1. `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Analysis/TaggedFTC.lean`, blob `70e156ecf0cebad12e26bdc8404002b97163bd38`. `tagged_upper`, `tagged_lower` are genuine object-calculus derivations obtained by `PRA.qfInd` on a guarded finite-sum invariant. From cell estimates they give `|G(N)-G(0)-sum(F+ - F-)| <= L eps_k+(4N+L) eps_p`. The source explicitly leaves the derivative-to-cell estimate and passage to regular names outside this module.
2. `.../Analysis/RiemannSumRules.lean`, blob `694d0aeb0f3dbaf5407f21bdde294e79c639592c`. `rs_additive`, `rs_add`, `rs_scale`, `rs_bound`, `rs_close`, `rs_close_const` derive finite rational-sum identities/bounds after clearing common positive denominators. Appropriate backend for integration error accounting and edge cancellation.
3. `.../Analysis/RiemannRefinement.lean`, blob `b5c45b0dcf3a66d409d43f24df978afbe688e810`. `refine_upper/lower` derive the finite refined-grid estimate from neighboring sample bounds. Interpreted with mesh `h/r=d/(Nr)` and sample difference bound `D=B h/r`, it gives `|S_N-S_Nr| <= B d^2 (r-1)/(2Nr) <= B d^2/(2N)`.
4. `.../Analysis/GridIntegral.lean`, blob `6487786ac131df651294257474bf82190e15997d`. `grid_upper/lower` prove one-dimensional coarse/fine sum comparison from supplied cell bounds, with PR guard and finite sums. Header explicitly excludes higher-dimensional grids, production of the modulus/evaluation contracts, and passage to a regular name.
5. `.../Topology/EulerCharacteristic.lean`, blob `c58f319a87b3a11ebf3ab52b1824b22cc181f8cc`. `euler_poincare` is a genuine iPRA derivation of a sign-free finite alternating-sum identity from supplied rank decompositions. `alt_telescope`, `euler_poincare_ring`, `euler_additivity`, `euler_collapse` are ambient Lean algebra/Finset theorems. This module does not provide the Gauss–Bonnet triangulated-surface incidence identities or smooth curvature theorem.
6. `.../Topology/BoundarySquare.lean`, blob `c6cced8bb36940c7bd9870b4a7a104bd3a943e53`. Gives a checked ambient finite involution proof of simplicial boundary squared equals zero, with opposite signs. Useful design pattern for edge cancellation, but not a new object-level Gauss–Bonnet proof.

## Research packets read for methodology

- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/calculus_ipra/README.md`, blob `7b17538616fc7a29913f510c9e85981f97855720`: explicitly uses fixed PR rational-evaluator schemas and supplied PR moduli; no universal PR evaluator, no extraction of effective partitions from qualitative compactness. Its source was originally an uncompiled candidate and distinguishes ambient prototypes from `Prf PRAAx` derivations. Its mathematical content motivates rebuilding elementary FTC with explicit contracts.
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/ipra_constructive_analysis_2026-11-20/framework.tex`, blob `4f80660ea6def5d5ae77a7c2a42ba9cda8dc62f2`: regular rational names, pointwise numerical contracts, fixed programs or fuelled machines, finite observation replay. Conditions on analytic inputs may contain number quantifiers, while all induction invariants remain quantifier-free or Boolean-compiled bounded tests.
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_continuous_framework_2026-11-20/sections/foundations.tex`: distinguishes executable PR-family theorems, internally represented program codes with explicit totality promises, and semantic adequacy. Explicitly warns that an interface field asking for a proof is not a proof of that field. Relevant requirements: existence, coherence, extensionality, adequacy must all be discharged.
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_finite_presentations_2026-11-20/README.md`: finite atlas margins and cyclic proof replay are available as research implementations; the README claims a checked fixed-table replay endpoint, but full application chapters remain open. No automatic compactness/triangulation producer should be assumed.

## Discovery limits

The recursive `docs` tree (6046 entries) and `Derivations` tree were inspected for names, and GitHub code search for Gauss Bonnet returned no results. No filename containing Gauss–Bonnet, Stokes or implicit-function was found in those inspected trees. This supports saying no existing module was found, not an exhaustive proof of absence from all binary archives or the whole repository. GitHub search results used a stale indexed commit, so source reads above were pinned to the live main head instead.

## Public primary-author educational sources

Useful classical references returned by web search:

- Chuu-Lian Terng, *Math 162B: Curves and Surfaces in R3, Part II*, UC Irvine, sections 16–19: https://www.math.uci.edu/~cterng/162B_Notes.pdf . Section 19 gives a classical geodesic-triangulation proof. Do not import its unquantified triangulation existence into iPRA.
- Steven New, *Chapter 3. Geodesic Curvature and the Gauss–Bonnet Theorem*, University of Waterloo: https://www.math.uwaterloo.ca/~snew/PMATH365/Chap3GaussBonnet.pdf . Theorem 3.24 uses local triangle formulas, cancellation of shared-edge geodesic curvature, angle sums and `3F=2E`. This is closely aligned with our classical interpretation.
- Oliver Knill, *Math 136, Lecture 17: Global Gauss–Bonnet*, Harvard: https://people.math.harvard.edu/~knill/teaching/math136_2025/handouts/lecture17.pdf . Gives the local-to-global finite triangulation strategy. Our quantitative iPRA realization must be proved independently.

These web references were found/read in this subagent. The parent must open/search them itself before citing their browser reference IDs in the final answer. Plain bibliographic URLs in the report are available without such UI reference IDs.

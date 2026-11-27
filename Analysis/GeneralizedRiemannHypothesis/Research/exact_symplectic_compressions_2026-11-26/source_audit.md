# Source audit and dependency statement

Inspected November 26, 2026 (Pacific). Repository versions are fixed below; `sources.json` records file hashes and bibliographic metadata.

## 1. The Lean development

Repository: [lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit `72fead102f663d5c7a407964a13dc0cf9d977207`.

The inspected readable edition uses Lean `4.35.0` and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. Its [Statements.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Statements.lean) imports only Mathlib and formulates its conclusions using Mathlib's analytic zeta function, Dirichlet characters, and analytically continued Dirichlet L-functions. Its [Main.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean) exports these five declarations:

| Declaration | Mathematical scope |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis`. |
| `riemannZeta_eq_zero_re` | Every zeta zero other than a negative even integer has real part one half; the total function's value at the pole is excluded separately. |
| `LFunction_ne_zero_of_half_lt_re` | For every modulus at least one and every Dirichlet character, the L-function is nonzero in real part greater than one half, except that the principal character is not evaluated at its pole. |
| `LFunction_eq_zero_re` | Every Dirichlet L-function zero in the open critical strip lies on the critical line. |
| `LFunction_eq_zero_re_of_isPrimitive` | The preceding zero-location statement for primitive characters. |

The quantifiers include imprimitive Dirichlet characters. They do not include arbitrary Artin or automorphic L-functions, or Hecke characters over arbitrary number fields. No assertion of simplicity of zeros is made. These distinctions follow from the statements themselves, independently of how many other arithmetic objects occur inside the proof.

### Verification boundary

The [upstream README](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/README.md) reports compilation without `sorry`, dependence only on `propext`, `Classical.choice`, and `Quot.sound`, and successful independent checker runs. Those are **upstream-reported validation claims**. This audit inspected selected declarations and proof files; it did not rebuild the complete development, replay an exported kernel proof, or provide an independent line-by-line mathematical verification. The inspected `Lib/Speed.lean` contains elaboration and simplification settings and an `IsEmpty` synonym; it does not introduce a new axiom. That observation does not replace a whole-development axiom audit.

### The proof mechanism inspected

The arithmetic portion compares upper and lower estimates for the same corrected logarithmic covolume. Short integral forms and index control, an almost-full spanning family, and a product-formula lower bound combine to give `New.star_inequality` in [MainInequality.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/MainInequality.lean):

\[
\texttt{D.m}\,\texttt{D.totalRemainder}
\leq \texttt{D.f}\,\texttt{D.a}\,\texttt{D.logB}^{5}.
\]

Choosing the scales yields an eventual upper bound of order \(x^{-1/2+\varepsilon}\) for a smoothed, quadratically twisted prime remainder; see [OneSidedBound.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/OneSidedBound.lean). The [analytic criterion](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/Criterion.lean) chooses a twist avoiding zeros in a specified region and applies a Landau positivity argument to the meromorphic transform of the remainder. Residues containing sums of zero multiplicities must vanish, which excludes zeros to the right of one half.

The determinant inequality `New.TwistedLattice.covolume_add_index_nonneg`, in [TwistedLattice.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Lattices/TwistedLattice.lean), is a reusable part of this architecture. Its local twists must satisfy the specified common height bound and integrality conditions, including conjugate embeddings. None of the inspected steps automatically extends the analytic conclusion beyond Dirichlet L-functions.

## 2. The supplied Article

Repository: [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt), commit `fc9889c80312959aee9893ab21bfc9e741719e88`.

The relevant files are:

- [sections/src.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/fc9889c80312959aee9893ab21bfc9e741719e88/Analysis/GeneralizedRiemannHypothesis/Article/sections/src.tex), blob `f69668b2f95261630bb1282c2cc1f9c172b7e530`: source scope, proof architecture, and the Article's own verification boundary.
- [sections/spn.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/fc9889c80312959aee9893ab21bfc9e741719e88/Analysis/GeneralizedRiemannHypothesis/Article/sections/spn.tex), blob `d8e0f69e713254e77cc82c15fc42fc9006e4a804`: finite symplectic compression results and the extension question.

The source section pins the same Lean commit, explicitly treats its claims as input, and says that its reported builds and kernel checks were not repeated. The symplectic section contains an exact limiting result for an isotropic family (`spn:thm:symplectic-exact`), the pointwise likelihood for a Lagrangian target and arbitrary source form (`spn:thm:lagrangian`), and a rank-versus-full-distribution separation with a Lagrangian target and nonsingular source (`spn:thm:rank-blind`). The latter phenomenon therefore already appears in the supplied Article.

Question `spn:q:symplectic` asks for the compression law, or its limiting discrepancy from a uniform matrix, when both compressed subspaces are arbitrary and neither is required to be Lagrangian. This is the specific question addressed by the accompanying paper. Our formula permits arbitrary restricted alternating forms, including degenerate ones. The paper also derives a sharp fixed-dimension asymptotic and a balanced rectangular regime with **both restricted forms nonsingular**, extending the Article's rank-blindness analysis to that setting.

## 3. Logical dependence of this package

The new results are **unconditional finite-field theorems**. Their proof uses finite-dimensional alternating-form linear algebra and exact counting; it does not assume RH or Dirichlet GRH. Their connection to the supplied work is the explicit extension question and its compression methods. Thus the finite-field conclusions do not depend on the outcome of a future independent audit of the analytic Lean development.

The mathematical proof, exhaustive finite examples, and literature-priority limitations are distinct forms of evidence. The proof establishes the claims; finite checks corroborate the implementation; the literature comparison identifies related work without certifying worldwide originality. See `literature_review.md` for that comparison.

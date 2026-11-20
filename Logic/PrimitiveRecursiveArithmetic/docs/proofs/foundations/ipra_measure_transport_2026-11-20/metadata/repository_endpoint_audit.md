# Repository endpoint audit and checked kernel

The audit is pinned to ProveIt commit
`b2341af5370cd8a43f72ebb2341c0d7d7395b634` (20 November 2026).
GitHub plugin reads independently confirmed the README and endpoint inventory.
An exact-revision local Git object database supplied the selected source files.
The object database was sparse; its working-tree absence was not treated as
absence from the repository. `work/lean/source_manifest.json` records exact
paths, Git blob IDs, SHA-256 digests and immutable URLs.

## Findings that materially affect the new report

The top-level README distinguishes the checked `ConciseIPRA`, `Derivations`
and `Bridge` libraries from research packets filed under `docs/proofs`.
The latter are not uniformly verified simply because they are present in the
repository. Conversely, the current `Derivations` library already contains
substantial finite analytic and probabilistic object proofs. A new report
must not repeat the old statement that all mathematical applications remain
unformalized.

The ordinary target is `LeanProofs.ConciseIPRA.Prf PRAAx Γ φ`, with scoped
`PTm` terms and `Fm PTm n` formulas. `PRAAx` contains PR defining equations,
successor axioms, and quantifier-free induction. Actual structural functions
are `Prf.subst`, `Prf.weaken`, and `Prf.trans`. The actual induction wrapper is
`PRA.qfInd`, whose successor premise is over `φ :: Γ.map Fm.shift`.

### Existing usable endpoints

All paths below are under `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/`.

| Module | Verified source boundary observed in audit | Use in this package |
|---|---|---|
| `IPRADerivations.Probability.Expectation` | Explicit `Prf PRAAx` finite weighted linearity, monotonicity, Markov/Chebyshev, Cauchy–Schwarz and second-moment inequalities | Lift pointwise clipping and square bounds through variable-length weighted sums |
| `IPRADerivations.Probability.SignedParts` | Natural-pair signed values, positive/negative parts, absolute expectation, finite linearity | Encode signed rational samples without completed-real sign tests |
| `IPRADerivations.Probability.TruncationEstimate` | Correct common-envelope inequality under `d≤2G`, with finite sum proof by QF induction | Existing valid truncation backend; distinct from the invalid independent-tail shortcut identified in the delivered packet |
| `IPRADerivations.Probability.TowerCommonDen` | Product common-denominator certificate and regrouping for refining cell maps | Rational presentations and conditional-average tower identity |
| `IPRADerivations.Probability.FiniteKernel` | Cross-multiplied expectations are QF; natural-weight presentation of rational probability vectors | First-order finite integration interface |
| `IPRADerivations.Probability.WeightedLagrange` | Weighted Lagrange identity and equality conditions | Finite energy and orthogonality certificate infrastructure |
| `IPRADerivations.Probability.FiniteCauchySchwarz` | QF prefix invariant and finite Cauchy–Schwarz derivation | L2-to-L1 error conversion |
| `IPRADerivations.Analysis.ErrorBudgets` | Variable-length finite sum/product and inverse error budgets | Compose finite approximation errors |
| `IPRADerivations.Foundations.BlockPartitionSum` | Variable endpoint block partition sum identity | Finite refinement and regrouping |
| `IPRADerivations.Foundations.CoherentPresentations` | `coherence`, `coherence_closed` from producer, restriction and uniqueness proofs | Reuse actual producer contracts, keeping those contracts explicit |
| `IPRADerivations.Foundations.BoundedDecision` | A fixed numeral-bound exhaustive case split gives an object derivation | Suitable only for small fixed truth tables; not a substitute for the variable-length QF loop proof |

These source declarations were inspected. The repository's previous build
receipts were read; they were **not rerun here**, and no fresh repository-wide
build is asserted.

### Truncation correction must be stated precisely

The independently truncated-tail inequality can fail on one atom:
`x=2, y=-1, K=1`; on the union of large-value events, the full distance is 3
while the independently retained tails sum to 2. The new standalone Lean
example proves this counterexample. The repository's *common-envelope*
`TruncationEstimate.truncation` is nevertheless valid and explicitly uses
`|x-y|≤2G` and `2G 1(G>K)`. The report should repair the particular unsafe
shortcut, not disparage this existing correct theorem.

## Actual new Lean check completed

The available standalone Lean distribution reports version 4.32.0, compiler
commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
The package `work/lean` builds successfully with no Mathlib dependency:
35 named theorem declarations plus 8 checked examples in 416 lines of Lean
across four files. No admitted proof or new axiom declaration occurs.

The meaningful checked results include:

* exact clipping residual and 1-Lipschitz clipping;
* `rho(x,y)=min(1,|x-y|)` bounds, symmetry and triangle inequality;
* excess-tail 1-Lipschitz continuity;
* `|x-y|≤2K rho(x,y)+(|x|-K)^++(|y|-K)^+`, for `K≥1`;
* its arbitrary finite nonnegative weighted integral form;
* `4K (|x|-K)^+≤x²`;
* binary conditional-average energy and residual identities;
* simultaneous finite binary energy identity;
* arbitrary finite weighted square expansion and conditional orthogonal-energy identity;
* energy telescoping;
* executable bounded search for a small energy increment, with soundness,
  failure-growth invariant and the energy-budget existence theorem;
* the independent-tail counterexample.

All these are **host Lean theorems**, not new `Prf PRAAx` derivations.
The audit reports `propext`, `Classical.choice`, and `Quot.sound`, inherited
from the standard rational theory and tactics. They must not be advertised
as an axiom-free or already intuitionistic formalization.

The arbitrary host functions `Nat → Rat` in the finite sum theorems express
mathematical generality in Lean. The object-iPRA translation specializes each
to one fixed primitive recursive term or uses a bounded supplied table.
No unrestricted universal primitive recursive evaluator is assumed.

## Completion route

`OBJECT_LANGUAGE_PLAN.md` spells out the signed rational coding, the cleared
pointwise inequality, prefix-sum QF invariant, modulus composition, dyadic
energy certificate, and bounded-window search invariant. It specifies what
must still become an object derivation and which exact existing module
supplies each prerequisite. `ObjectAdapter.lean.txt` shows the exact three
structural interfaces as uncompiled integration candidates, explicitly
excluded from the standalone Lake targets. We did not install or rebuild the
canonical Mathlib dependency merely to check these routine wrappers.

Package all regular files in `work/lean` except `.lake/` and the temporary
top-level `.olean` files. The compiler binary/archive is not a deliverable.

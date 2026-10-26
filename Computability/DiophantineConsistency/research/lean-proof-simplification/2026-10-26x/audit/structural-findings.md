# Two additional structural simplifications

Reviewed repository commit: `1e2a853935a6155cbcf2aa199aaca51946c4fff9`.
Source paths below are relative to `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

## A. The Boolean-root argument needs cancellation, not discreteness

Targets: `ObjectNaturalOrderedSemiring.mul_strict_left`, its ordered-ring instance, and `ObjectNaturalDiscrete.mul_self_eq_self_iff`.

The original strictness proof decomposes a positive factor as `a=t+1` and a strict comparison as `c=b+s+1`, then exhibits a positive additive gap. That makes the ordered-semiring layer depend on discrete successor arithmetic. The Boolean-root theorem is therefore proved before multiplication cancellation is available, expanding a zero-or-successor decomposition followed by distributivity and the no-zero-divisors law.

A smaller logical dependency suffices. In a linearly ordered commutative semiring with canonical order, cancellative addition and no zero divisors:

1. `b<c` supplies `c=b+d` by the canonical additive order.
2. `d` is nonzero, because `d=0` would imply `b=c`.
3. For `0<a`, the product `a*d` is nonzero, hence positive in the canonical order.
4. Distributivity gives `a*c=a*b+a*d>a*b`.

This establishes strict multiplication monotonicity without any successor decomposition. With the resulting cancellation instance, `x*x=x` rewrites to `x*x=x*1`, so for `x≠0` cancellation gives `x=1`. Mathlib's `IsIdempotentElem.iff_eq_zero_or_one` already packages that final argument.

The two-file candidate changes only imports, the private strictness proof, the Boolean-root proof, and its comment. Existing public theorem statements and instance names are unchanged. Total physical lines change from 103 to 90 (OrderedSemiring 30→30; Discrete 73→60). These are source counts, not timing claims.

The original comment correctly warns that an arbitrary semiring may have nontrivial idempotents. It does not follow that successor discreteness is needed in this setting: multiplicative cancellation suffices, and follows from the earlier canonical-order and no-zero-divisor properties. The generic certificate is valid, for example, in nonnegative rationals; it is not specific to a discrete natural-number carrier.

### Non-repetition boundary

Packet c, `report.tex`, section “Build on the algebraic interfaces already present,” already identifies the OrderedSemiring/Discrete dependency cycle and suggests lower-assumption lemmas or reordering. **Module reordering is not counted as the fresh idea.** The additional result is the precise non-discrete positive-difference proof and direct replacement of the Boolean-root theorem. Generic definable-induction transport, no-zero-divisor induction cleanup, semiring evaluator abstraction and sum-of-squares sharing are not claimed anew.

### Artifacts and validation

- `OrderedCancellation.lean`: the generic mathematical theorem and Boolean-root corollary; checked with Lean 4.32.0.
- `canonical-order.patch`: repository-root-relative two-file patch.
- `modified/DiophantineConsistency/ObjectNaturalOrderedSemiring.lean` and `ObjectNaturalDiscrete.lean`: full replacements.
- `generic-build.log`: standalone compiler result, standard axioms only.
- RAM `order-validation.json`: successful full actual OrderedSemiring compile with exact source/output hashes.
- RAM `full-validation.json`: integration validation against the entire current dependency closure and representative unchanged downstream clients; all 73 module records now report exit 0. This includes the three replacements and unchanged ObjectNatPairing, ObjectPairingSyntax, ObjectPairingGraph, ObjectPairingSurjective and ObjectPairingInjective clients.

The standalone certificate uses `propext`, `Classical.choice` and `Quot.sound`. A dependency audit finds that the only maintained direct importers of OrderedSemiring are the umbrella and ObjectPairingInjective; the latter also imports PairingSurjective, which brings in Discrete through the pairing graph chain. Removing the old transitive Discrete import therefore does not silently break these maintained users. Third-party users who relied solely on that transitive import may need an explicit Discrete import.

## B. Formula-code lower bounds need only the outer constructor

Target: `AnnotatedClosure.formCode_ge` and its private inequality support.

The maintained proof establishes the lower bound 44 by structural induction on formulas. It develops custom square-pairing and nested-fork bounds, invokes nonlinear arithmetic and uses `first` alternatives to split binary constructors. This numerical threshold needs no induction hypothesis about subformulas.

Square pairing is strictly increasing in each argument. Therefore fork coding is monotone in each argument, and every atom code is at least one. Two finite certificates cover all non-bottom constructors:

- Every variable-style code is at least `forkCode 1 (forkCode 1 1)=67`.
- Every connective tag at least three gives a code at least `forkCode (atomCode 3) 0=133`.

The bottom constructor has code 44. Thus case analysis on the outer constructor establishes the bound. The candidate removes nonlinear arithmetic from the threshold proof while keeping exactly the existing square pairing and frozen constructor tags. The subformula code is used only as a natural-number payload.

The complete file changes from 148 to 129 physical lines. The public bound remains 44, preserving the argument in `code_all_quadratic`; all closure-program definitions and node counts stay literally unchanged. No encoded expression, validator, code representation or computational cost changes.

### Non-repetition boundary

Earlier packet e proposes typed/numeric iteration fusion in this same module. That concerns closure iteration, not the minimum formula-code argument. The a-r manuscript and supplementary corpus does not propose `formCode_ge`, its nonlinear square helpers or outer-constructor minimum certificates. Generic coefficient envelopes, decoder fusion and list encoding cleanup do not supply this specific remaining argument. The novelty claim is this concrete source improvement, not invention of monotonicity as a mathematical principle.

### Artifacts and validation

- `FormulaMinimumCore.lean`: exact pairing and numerical-bound certificates; checked with Lean 4.32.0.
- `formula-minimum.patch`: repository-root-relative complete candidate patch.
- `modified/DiophantineConsistency/AnnotatedClosure.lean`: replacement source.
- `formula-minimum-full.log`: full replacement module compiles against freshly rebuilt current AnnotatedRenameArithmetic and dependencies.
- `formula-minimum-validation.json`: complete original and candidate source hashes, physical-line counts, commands and successful exit statuses.
- `formula-minimum-before-axioms.log` and `formula-minimum-after-axioms.log`: the threshold theorem and `code_all_quadratic` use the same standard axiom set before and after (`propext`, `Classical.choice`, `Quot.sound`).

This is a checked binding to the actual formula constructors, constructor codes, closing-program definitions and exact supplied-program node counts, not merely a standalone copied arithmetic model.

## Final validation outcome

Both complete source proposals passed. The 73-module integration closure uses only repository modules freshly compiled during this task, or outputs from those builds reused after exact source, direct-dependency and output-hash verification. All nine external package commits match the current repository manifest. No old repository output objects were imported. Before/after checks of the full Discrete source preserve the exact standard axiom set as well. Successful complete-module validation is stronger evidence than the standalone generic prototypes; both forms are included.

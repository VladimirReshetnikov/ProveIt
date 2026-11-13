# iPRA endpoint for the nine-variable equation: plan and status

**Status (2 November 2026): closed.** `Lean/DiophantineConsistency/IPRAExplicitZFCFinal.lean`
proves, with no hypotheses, native, standard and equality-only iPRA
equivalences between the no-zero sentence of `ExplicitZFCSyntax.expression`
(the nine-variable equation, `= ExplicitZFC.expression` by
`ExplicitZFC.expression_eq_syntax`) and the selected Foundation ZFC
consistency predicate. Its `#print axioms` report lists only `propext`,
`Classical.choice` and `Quot.sound` (Lean metatheory). Both model
obligations of the reduction are theorems: `ModelJonesNine.jonesModel` and
`IPRAExplicitZFCFinal.sourceModel` (from `ModelRepFinal.precCase` and
`ModelProgramLink.programLink`). A second nine-unknown equation,
`IPRANineCurrent.expression` (Jones applied to the maintained CURRENT2011
gate system), has its own unconditional endpoints and audit
(`IPRANineChecks`). Both endpoints have since passed a [104-stage author-side
replay](../../reviews/nine-variable-ipra-complete-author-ledger/README.md) on
a historical provider. This is not a paired replay or a fully authenticated
transitive closure. The sections below record the plan as executed.

Target: native, standard and equality-only iPRA proofs that the no-zero
sentence of `ExplicitZFC.expression` (nine unknowns, Jones 1982 coding of
the literal C222 refutation enumerator) is equivalent to the selected
Foundation ZFC consistency predicate. This is the only "simplest" equation
of the catalogue without an iPRA endpoint; its external (Lean metatheory)
equivalence is `ExplicitZFC.noSyntaxZero_iff_conZFC`.

Sizes below are proposed-work estimates in Lean lines, not commitments.

## Reduction (done, conditional)

`Lean/DiophantineConsistency/IPRAExplicitZFCReduction.lean` derives all
three iPRA endpoints for `ExplicitZFCSyntax.expression` from two explicit
`Prop` hypotheses about every model `V` of `𝗜𝚺₁`:

* `JonesModel` — uniformly in a quartic gate system `p = q`, the
  nine-variable syntax `ExecutableJones.expression (QuarticSyntax.expression p q) 0`
  has an internal zero iff the quartic gate syntax does;
* `SourceModel` — the compacted source equation of the enumerator program
  has an internal solution iff the internal C222 enumerator
  (`ArithmeticEnumRunPerm222.run`) halts from `liveValue 0 4 0`.

The rest of the chain is already internal: `IPRAQuarticModelBridge.exists_quartic_iff`
(quartic gates ↔ source equation), `ArithmeticEnumSoundnessPerm222.refutation_iff_zero_work_halts`
and `ArithmeticCheckerMachine215.refutation_iff_blank_halts` (C222 ↔ decimal
215 machine, the `PolynomialBridge` target). No ZFC calibration is needed:
`haltingTest` runs that same enumerator from the same state.

## Import plumbing (done)

Foundation's `Vorspiel/Matrix.lean` and Mathlib's
`LinearAlgebra/Matrix/Defs.lean` both define `Matrix.map`, so no module may
import Foundation together with Mathlib's matrices. The Jones proofs import
`Mathlib.Tactic`, which reaches `Matrix.Defs`. The data definitions were
therefore moved, with unchanged names, into Matrix-free modules:
`JonesSyntaxCore`, `ExecutableJonesCore` (with `rfl` copies `codingStar`,
`codingExpo`, `codingLexp`, `codingL4` of the Paper1982 constants),
`CompactedJonesSyntax` and `ExplicitZFCSyntax`. `ExplicitZFC.expression_eq_syntax`
identifies the published equation with the Matrix-free one through the
generic `CompactedJones.expression_ofIff`, so no concrete syntax is ever
evaluated (the expression contains `(b^5)^(5^(ν+1))` as repeated products
and cannot be built).

## `JonesModel`: internal Jones 1982 (≈ 6.5–9k lines)

Mirror `Jones1982.Nine.wset_iff_nine`, replaying ℤ arguments in the model
ring of differences `DiffRing V` and replacing analytic steps:

| stage | external | internal module(s) | status |
|---|---|---|---|
| relation combining, 2 radicands | `RefinedRelationCombining.relationCombining_iff` (ℂ, Galois) | `ModelRelationCombining` (elementary: signed factors + square divisibility), `ModelNineConds` | compiled |
| syntax evaluation | `JonesSyntax`/`ExecutableJones` eval lemmas | `ModelJonesSyntax`: `evalRing` of the nine-variable syntax in any commutative ring | compiled |
| Lemma 2.22(iii), 2.27, 2.25 | Exponential, ProductPell (+Psi), Ratio (ℝ bounds), Paper1976/78 | `ModelExponentialCongruence` (exact divisibility from `projection_quotient`), `ModelProductPell` (Lemma 2.28 avoided via `doubled_step_down`), `ModelRatioBounds` + `ModelRatio` (integer sandwich bounds from Bernoulli's inequality in place of ℝ) | compiled |
| ratio stage (`ratio_sound`/`ratio_complete`) | NineRatio | `ModelNineRatio` | compiled |
| reduction stage | NineReduce, Master2/3, Carries, Digits, Coding, Packing | `ModelCarries`, `ModelDigitTransfer`, `ModelPacking` (compiled); `ModelCoding`, `ModelMaster`, `ModelNineReduce` at input `x = 1` | compiled |
| quartic side facts | `QuarticCompiler.quartic_degree`, `quartic_normalized` | `QuarticSyntaxFacts` (Matrix-free re-proofs on the syntax) | compiled |
| assembly | `wset_iff_nine` | `ModelJonesNine` (`nine_iff`, `jonesModel`); `ModelMaster`'s size lemmas generalised from `b = 2^k` to any `b > y`, so the converse follows Jones's order | compiled |

Uniformity requirement: every statement is uniform in the quartic, so the
exponent `L = 5^(ν+1)` and the star sums are standard but never unfolded.

## A second nine-variable equation needing only `JonesModel`

`JonesModel` is uniform in the quartic, so it also applies to the quartic
gate system of the maintained CURRENT2011 equation, whose all-model bridge
`HACurrentEquation2011.polynomialBridge` is already proved. Composing
`exists_quartic_iff` (on the natural split of `ObjectCurrentEquation2011.naturalExpression`)
with that bridge gives a nine-unknown equation with native, standard and
equality-only iPRA endpoints and no `SourceModel` obligation. Its quartic
has far fewer gates than the compiled enumerator's (which adds more than
20 000 witnesses per primitive recursion), so its Jones exponent is much
smaller. It is a different equation from `ExplicitZFC.expression`, which
still needs `SourceModel`.

## `SourceModel`: internal MRDP for the compiled program (compiled)

| piece | module(s) |
|---|---|
| interface `Holds`/`GraphHolds` | `ModelRepCore` |
| internal semantics `evalV` of scalar PR codes (Foundation's `pair` is `Nat.pair`) | `ModelScalarPR` |
| simple combinators, `graphRep_holds` from `PrecCase` | `ModelRepBasic`, `ModelRepArith` |
| Gödel β-function and internal CRT | `ModelBetaFunction`, `ModelRepPrec` |
| Matiyasevich's Pell criterion, power, binomial, factorial | `ModelRepPell`, `ModelRepPower`, `ModelRepBinomial`, `ModelRepFactorial` |
| Davis–Putnam–Robinson bounded ∀ (prime-free: least divisor > 1 + gcd certificates) | `ModelBoundedForallArith`, `ModelBoundedForall`, `ModelRepFinal` (`precCase`) |
| simplify/compaction in any semiring, optimizer | `ModelSyntaxPipeline`, `ModelOptimizer` |
| enumerator program ↔ internal C222 run | `ModelDirectScalar`, `ModelEnumeratorCantor`, `ModelEnumeratorRows`, `ModelEnumeratorStep`, `ModelProgramLink` |
| assembly | `ModelSourceModel` (`sourceModel_of_link`), `IPRAExplicitZFCFinal` |

import PA194ModelSimTruthNeg
import ConPADerivationValidity
import PA194ModelFairness

/-!
# From a compiled internal refutation to a halt of the modeled scheduler

This file is the step after the derivation compiler, in a candidate-PRA model `M` whose
arithmetic reduct satisfies `𝗜𝚺₁`. It takes a simulation as a hypothesis and constructs none.

Let `T` be a theory in the relational source language and let `S` be a simulation
(`ConPA.Sequent.CutValidity.Sim`) of the internal derivations of `T` in the numerical
calculus (`numericalQuant`, `numericalTranslation` of `pa194-model-logic`) whose falsum code is
`1`. Then:

* `refutation_targetProvable`: an internal proof `d` of `⊥` from `T`, with an environment
  that is admissible for `d` and below the bound, gives `TargetProvable 1`. The compiler
  yields a target proof of `tr e ⊥ → 1`; the translation of `⊥` is the code `1`, so `tr e ⊥`
  is `1 → 1`, which is a theorem of the calculus.
* `refutation_halts`: the modeled scheduler then halts at some model time, by
  `PA194ModelFairness.provable_halts`.
* `provable_falsum_halts`, `not_provable_falsum_of_nonhalting`: the same for a family of
  simulations indexed by the derivation, which is the form needed when the bound and the
  admissibility relation are chosen from `d` (as the seed environments of `pa194-model-logic`
  are). If no model time is a halting time, then `T` has no internal proof of `⊥` in `M`.
* `refutation_targetProvable_of_original`: the first statement for the original interface
  `ConPA.Sequent.Sim`.

Nothing here concerns the physical machine, a theory other than the parameter `T`, or `𝗣𝗔`.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable PA194SchedulerHaltCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance endpointZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance endpointOne : One M := ⟨F oneCode Fin.elim0⟩
local instance endpointAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance endpointMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance endpointLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance endpointIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Theory M6.PA.RelationalSource.language} [T.Δ₁]

/-- The negated translation of `⊥` is the implication `1 → 1`, under every environment. -/
theorem negatedTranslation_falsum (e : M) :
    negatedTranslation e (^⊥ : M) = impValue 1 1 := by
  rw [negatedTranslation_any, fixedFormulaTranslation_falsum]
  rfl

/-- **An internal refutation that a simulation compiles gives a target proof of the
contradiction code.** -/
theorem refutation_targetProvable
    (S : ConPA.Sequent.CutValidity.Sim (numericalQuant (M := M)) numericalTranslation T)
    (hbot : S.bot = 1) {d e : M} (h : Proof T d (^⊥ : M)) (he : e ≤ S.bound)
    (ha : S.Adm e d) : TargetProvable (1 : M) := by
  have h1 : TargetProvable (impValue (negatedTranslation e (^⊥ : M)) S.bot) := S.proof h he ha
  rw [hbot, negatedTranslation_falsum] at h1
  exact tp_mp (imp_refl (1 : M)) h1

/-- The same for the original interface, whose cut field does not receive validity. -/
theorem refutation_targetProvable_of_original
    (S : ConPA.Sequent.Sim (numericalQuant (M := M)) numericalTranslation T)
    (hbot : S.bot = 1) {d e : M} (h : Proof T d (^⊥ : M)) (he : e ≤ S.bound)
    (ha : S.Adm e d) : TargetProvable (1 : M) :=
  refutation_targetProvable (ConPA.Sequent.CutValidity.Sim.ofOriginal S) hbot h he ha

/-- **An internal refutation that a simulation compiles makes the modeled scheduler halt.** -/
theorem refutation_halts
    (S : ConPA.Sequent.CutValidity.Sim (numericalQuant (M := M)) numericalTranslation T)
    (hbot : S.bot = 1) {d e : M} (h : Proof T d (^⊥ : M)) (he : e ≤ S.bound)
    (ha : S.Adm e d) : ∃ k : M, F haltAfter ![k] = 1 :=
  PA194ModelFairness.provable_halts (refutation_targetProvable S hbot h he ha)

/-- A family of simulations, one for each internal derivation, each with an admissible
environment for its derivation: internal provability of `⊥` makes the modeled scheduler
halt. -/
theorem provable_falsum_halts
    (S : M → ConPA.Sequent.CutValidity.Sim (numericalQuant (M := M)) numericalTranslation T)
    (hbot : ∀ d, (S d).bot = 1)
    (hadm : ∀ d, Proof T d (^⊥ : M) → ∃ e ≤ (S d).bound, (S d).Adm e d)
    (h : Provable T (^⊥ : M)) : ∃ k : M, F haltAfter ![k] = 1 := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨e, he, ha⟩ := hadm d hd
  exact refutation_halts (S d) (hbot d) hd he ha

/-- **If the modeled scheduler never halts in `M`, then `T` is consistent in `M`**, given a
family of simulations as in `provable_falsum_halts`. -/
theorem not_provable_falsum_of_nonhalting
    (S : M → ConPA.Sequent.CutValidity.Sim (numericalQuant (M := M)) numericalTranslation T)
    (hbot : ∀ d, (S d).bot = 1)
    (hadm : ∀ d, Proof T d (^⊥ : M) → ∃ e ≤ (S d).bound, (S d).Adm e d)
    (hnh : ∀ k : M, F haltAfter ![k] ≠ 1) : ¬ Provable T (^⊥ : M) := fun h => by
  obtain ⟨k, hk⟩ := provable_falsum_halts S hbot hadm h
  exact hnh k hk

#print axioms negatedTranslation_falsum
#print axioms refutation_targetProvable
#print axioms refutation_targetProvable_of_original
#print axioms refutation_halts
#print axioms provable_falsum_halts
#print axioms not_provable_falsum_of_nonhalting
end models
end PA194ModelLogic

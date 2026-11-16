import PA194FullSourceRefutationReduction
import PA194PAeqFiniteSupplier
import PA194AdjunctiveFullSep

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace PA194PARefutationScheduler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
open PA194BindSource PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage
  PRATheory PRAAddOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance ordinalFixedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance ordinalFixedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance ordinalFixedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance ordinalFixedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance ordinalFixedLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance ordinalFixedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194GuardedCompiler PA194Schematic PA194SchedulerHaltCode
attribute [local instance] adjunctiveFullSepTheoryDelta PA194PAeqBind.ordinaryPAeq_delta

/-- A Foundation PA refutation gives a halting time for the modeled command scheduler,
conditional on the fixed source arithmetic facts and recursion clauses. -/
theorem scheduler_halts_of_pa_refutation
    (S : SourceFacts (V := M) adjunctiveFullSepTheory)
    (hA3 : adjunctiveFullSepTheory.internalize M ⊢ tHyp sA3)
    (hM3 : adjunctiveFullSepTheory.internalize M ⊢ tHyp sM3)
    (hp : Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M)) :
    ∃ k : M, F haltAfter ![k] = 1 := by
  obtain ⟨d, hd⟩ := PA194PAeq.InductionReopen.pa_refutation_to_ordinary hp
  exact PA194BindSource.adjunctiveFullSep_provable_halts
    (PA194FullSourceRefutationReduction.refutation_of_source_facts S hA3 hM3 hd)

#print axioms scheduler_halts_of_pa_refutation
end models
end PA194PARefutationScheduler

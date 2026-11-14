import PA194SourceFreshClose
import PA194SourceHead1Syntax
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace PA194RelativeFalseAll
open PA194SourceFreshClose PA194SourceHead5Preservation PA194SourceHead1Syntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194ReplacementOpening
open PA194SourceOutputWF PA194SourceRho8Preservation PA194SourceEqualityPreservation PA194SourceHead6Preservation PA194SourceHead5Preservation
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]




lemma internal_relative_false_all (label : M) :
    let D : Bootstrapping.Formula M ℒₒᵣ := ⟨translated 1,(fixed_all_wf 1).1⟩
    let E : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close label 0 D.val, by
      simpa using PA194InternalFormulaClose.close_wellformed label 0 D.val D.isSemiformula⟩
    (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ∀⁰ ∼E := by
  let D : Bootstrapping.Formula M ℒₒᵣ := ⟨translated 1,(fixed_all_wf 1).1⟩
  let E : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close label 0 D.val, by
    simpa using PA194InternalFormulaClose.close_wellformed label 0 D.val D.isSemiformula⟩
  change (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ∀⁰ ∼E
  have hD : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ∼D := by
    have hD' : D = bitFormula 0 0 := by
      apply Bootstrapping.Semiformula.ext
      exact one_code
    rw [hD']
    simpa [bitFormula] using (PA194InternalBitDiagonal.internal_PA_proves_bit_diag_neg (0 : M))
  have hn : Provable (𝗣𝗔 : ArithmeticTheory) (neg ℒₒᵣ D.val) := (tprovable_iff_provable).mp hD
  have hfree := PA194SourceUniversalPreservation.reopen_provable label (neg ℒₒᵣ D.val) D.isSemiformula.neg hn
  rw [PA194CloseNegation.close_neg label 0 D.val D.isSemiformula] at hfree
  have hsub : subst ℒₒᵣ ?[^&0] (neg ℒₒᵣ (shift ℒₒᵣ E.val)) = neg ℒₒᵣ (subst ℒₒᵣ ?[^&0] (shift ℒₒᵣ E.val)) := by
    apply substs_neg (m := (0:M)) E.isSemiformula.shift
    simp
  have htyped : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ (∼E).free := by
    apply (tprovable_iff_provable).mpr
    simpa [E,Bootstrapping.Semiformula.free,Bootstrapping.free,substs1,
      shift_neg E.isSemiformula,
      hsub] using hfree
  exact TProof.all! htyped
#print axioms internal_relative_false_all
end models
end PA194RelativeFalseAll

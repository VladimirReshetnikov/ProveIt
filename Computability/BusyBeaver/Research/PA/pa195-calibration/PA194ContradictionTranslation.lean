import PA194BitTranslation
import PA194TemplateRew
import PA194SourceOutputWF
/-! The distinguished numerical source contradiction and its fixed
arithmetic translation. This does not translate proofs or relate them to
PA194 machine executions. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
namespace PA194ContradictionTranslation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PA194BitTranslation PA194SourceOutputWF PA194CanonicalDualForall
  PA194DualRecursion PA194DualQuantRecursion PA194DualAtomCode PA194BitTemplate PA194TemplateRew
  PA194TagDecoder PA194ChildCodes PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

/-- The ordinary arithmetic formula translated from source contradiction 1. -/
noncomputable def contradiction : ArithmeticFormula Nat := bitTranslation 0 0

theorem ISigma1_proves_not_contradiction : (𝗜𝚺₁ : ArithmeticTheory) ⊢ (∼contradiction).univCl := by
  apply Arithmetic.complete.{0}
  intro M _ _
  simp only [models_iff,Semiformula.eval_univCl]
  intro e
  simp only [Semiformula.Evalf, LogicalConnective.HomClass.map_neg]
  change ¬ (bitTranslation 0 0).Eval Fin.elim0 e
  rw [bitTranslation_eval]
  have hbit : bitDef.val.Evalb ![e 0,e 0] ↔ e 0 ∈ e 0 := by
    exact bit_defined.defined ![e 0,e 0]
  rw [hbit]
  intro h
  exact Arithmetic.lt_irrefl _ (lt_of_mem h)

theorem PA_proves_not_contradiction : (𝗣𝗔 : ArithmeticTheory) ⊢ (∼contradiction).univCl := by
  exact Entailment.WeakerThan.pbl ISigma1_proves_not_contradiction

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_code_one : π₁ (F fixedTranslation (fun _ => (1 : M))) = (⌜contradiction⌝ : M) := by
  have hm := modelDualMembership fixedTag
    PA194TermWellFormedUnconditional.canonicalFirst PA194TermWellFormedUnconditional.canonicalSecond
    fixedFirst fixedSecond PA194CanonicalDualForall.canonical (Classical.choose_spec PRA_has_tagCode).2
    (Classical.choose_spec PRA_has_firstChildCode).2 (Classical.choose_spec PRA_has_secondChildCode).2
    (0 : M) (0 : M)
  change F fixedTranslation (fun _ => 4*cantor 0 0+1) = F dualBitCode ![0,0] at hm
  simp [cantor,triangle] at hm
  rw [hm,dualBitCode,modelBin,modelPairCode,pi₁_pair]
  have hq := modelBitTemplateCode_quote (M := M) 0 0
  change F bitTemplateCode ![(0 : M),0] = (⌜outerRew 0 0 ▹ bitDef.val⌝ : M) at hq
  rw [hq]
  unfold contradiction bitTranslation
  rw [bitMatrix_eq]
  rfl
end models
#print axioms positive_code_one
#print axioms PA_proves_not_contradiction
#print axioms ISigma1_proves_not_contradiction
end PA194ContradictionTranslation

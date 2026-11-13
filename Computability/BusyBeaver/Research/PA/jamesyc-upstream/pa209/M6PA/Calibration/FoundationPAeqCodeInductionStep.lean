module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeEqualityFormula
public import M6PA.Calibration.PAPresentationStepTheorem
@[expose] public section
/-! The fixed arithmetic +1=S proof is quoted through the actual coded proof
bridge and specialized to arbitrary model-valued target terms. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "U" => Presentation.ordinaryPAeq
local prefix:max "#'" => Semiterm.bvar (V:=V) (L:=Presentation.language)
local infix:50 " ≐ₚ " => typedEq

theorem additive_successor (t : Term V Presentation.language) :
    (U).internalize V ⊢ typedAdd t (typedSucc typedZero) ≐ₚ typedSucc t := by
  have h := internal_provable_of_outer_provable (V:=V) Presentation.paeq_proves_addOneSuccessor
  have hc : (FFL.FirstOrder.Semiformula.all Presentation.stepProperty).freeVariables=∅ := by
    simp [Presentation.stepProperty,Presentation.eq,Presentation.add,Presentation.succ,Presentation.zero,
      FFL.FirstOrder.Semiformula.freeVariables,FFL.FirstOrder.Semiterm.freeVariables,Fin.univ_succ]
  have hq : (⌜(FFL.FirstOrder.Semiformula.all Presentation.stepProperty).univCl⌝ : Bootstrapping.Formula V Presentation.language)=
      ⌜FFL.FirstOrder.Semiformula.all Presentation.stepProperty⌝ := by
    rw [Sentence.typed_quote_def,Presentation.embed_close_eq _ hc]
  rw [hq] at h
  have h' : (U).internalize V ⊢ ∀¹ (typedAdd #'0 (typedSucc typedZero) ≐ₚ typedSucc #'0) := by
    simpa [Presentation.stepProperty] using h
  simpa using TProof.specialize! h' t

#print axioms additive_successor
end M6.PA.FoundationPAeqCode

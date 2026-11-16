module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaLogicalCertificate
@[expose] public section
namespace M6.PA.NumericPAeqFormulaLogical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary RelationalSource.Numeric ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def instanceForward (F D B P:SF (V:=V) 0):
    ND.Proof (T:=(∅:Theory L).internalize V) ∅
      (((F ⋏ D) 🡒 bi B P) 🡒 ((F ⋏ B) 🡒 (D 🡒 P))) := by
  apply ND.impIntro
  apply ND.impIntro
  apply ND.impIntro
  let C:ND.Seq (V:=V) := insert (∼D) (insert (∼(F ⋏ B)) (insert (∼((F ⋏ D) 🡒 bi B P)) ∅))
  have hFB:ND.Proof (T:=(∅:Theory L).internalize V) C (F ⋏ B) := ND.assumption _ (by simp [C])
  have hD:ND.Proof (T:=(∅:Theory L).internalize V) C D := ND.assumption _ (by simp [C])
  have hI:ND.Proof (T:=(∅:Theory L).internalize V) C ((F ⋏ D) 🡒 bi B P) := ND.assumption _ (by simp [C])
  exact ND.mp (ND.andRight hFB) (ND.andLeft (ND.mp (ND.andIntro (ND.andLeft hFB) hD) hI))
variable [V↓[ℒₒᵣ] ⊧* theory]
theorem instanceForward_requested_certificate (F D B P native lo z:V)
    (hF:IsFormula L F) (hD:IsFormula L D) (hB:IsFormula L B) (hP:IsFormula L P)
    (hc:FormulaCovered 0 native lo z (imp L (imp L (qqAnd F D) (biCode B P)) (imp L (qqAnd F B) (imp L D P)))):
    ∃code,verifyValue code=translate (parameters 0 native lo z)
      (imp L (imp L (qqAnd F D) (biCode B P)) (imp L (qqAnd F B) (imp L D P)))+1 :=
  empty_requested_certificate _ (instanceForward ⟨F,hF⟩ ⟨D,hD⟩ ⟨B,hB⟩ ⟨P,hP⟩) native lo z hc
#print axioms instanceForward
#print axioms instanceForward_requested_certificate
end M6.PA.NumericPAeqFormulaLogical


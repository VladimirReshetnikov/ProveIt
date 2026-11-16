module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqInductionStepTemplateProof
public import M6PA.Calibration.NumericPAeqInductionStepTemplateCode
public import M6PA.Calibration.RelationalPredicateBinaryEmptyRequested
@[expose] public section
namespace M6.PA.NumericPAeqInductionStepTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence ActualCheckerBlueprint RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem uniformMatrixCode_valid {F P R:V} (hF:IsFormula L F)
    (hP:IsSemiformula L 1 P) (hR:IsSemiformula L 1 R):IsSemiformula L 2 (uniformMatrixCode F P R) := by
  let f:SF (V:=V) 0 := ⟨F,by simpa using hF⟩
  let p:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  let r:SF (V:=V) 1 := ⟨R,by simpa using hR⟩
  have h := (uniformMatrix f p r).isSemiformula
  rw [uniformMatrix_val] at h
  simpa using h

theorem targetStepMatrixCode_valid {P:V} (hP:IsSemiformula L 1 P):
    IsSemiformula L 2 (targetStepMatrixCode P) := by
  let p:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  have h := (targetMatrix p).isSemiformula
  rw [targetMatrix_val] at h
  simpa using h

theorem stepCode_valid {F P R:V} (hF:IsFormula L F)
    (hP:IsSemiformula L 1 P) (hR:IsSemiformula L 1 R):IsFormula L (stepCode F P R) := by
  let f:SF (V:=V) 0 := ⟨F,by simpa using hF⟩
  let p:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  let r:SF (V:=V) 1 := ⟨R,by simpa using hR⟩
  have h := (uniform f domain p r successorPredicate 🡒 ((f ⋏ sourceStep domain p r) 🡒 targetStep domain p successorPredicate)).isSemiformula
  rw [step_val] at h
  simpa using h

theorem step_requested_certificate (F P R g lo z:V) (hF:IsFormula L F)
    (hP:IsSemiformula L 1 P) (hR:IsSemiformula L 1 R)
    (hc:FormulaCovered 0 g lo z (stepCode F P R)):
    ∃code,verifyValue code=translate (parameters 0 g lo z) (stepCode F P R)+1 := by
  let f:SF (V:=V) 0 := ⟨F,by simpa using hF⟩
  let p:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  let r:SF (V:=V) 1 := ⟨R,by simpa using hR⟩
  have he := step_val f p r
  change (uniform f domain p r successorPredicate 🡒 ((f ⋏ sourceStep domain p r) 🡒 targetStep domain p successorPredicate)).val=stepCode F P R at he
  rw [←he] at hc ⊢
  exact empty_requested_certificate _ (stepProof f domain p r successorPredicate) g lo z hc
#print axioms uniformMatrixCode_valid
#print axioms targetStepMatrixCode_valid
#print axioms stepCode_valid
#print axioms step_requested_certificate
end M6.PA.NumericPAeqInductionStepTemplate


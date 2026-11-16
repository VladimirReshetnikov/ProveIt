module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaQuantifierTemplatesProof
public import M6PA.Calibration.NumericPAeqFormulaQuantifierTemplatesCode
@[expose] public section
namespace M6.PA.NumericPAeqFormulaQuantifierTemplates
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary RelationalSource.Numeric ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
theorem allTemplateCode_isFormula {H D P Q:V} (hH:IsFormula L H)
    (hD:IsSemiformula L 1 D) (hP:IsSemiformula L 1 P) (hQ:IsSemiformula L 1 Q):
    IsFormula L (allTemplateCode H D P Q) := by
  let HH:SF (V:=V) 0 := ⟨H,hH⟩
  let DD:SF (V:=V) 1 := ⟨D,by simpa using hD⟩
  let PP:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  let QQ:SF (V:=V) 1 := ⟨Q,by simpa using hQ⟩
  rw [←allTemplate_val HH DD PP QQ]
  simpa using (uniformPremise HH DD PP QQ 🡒 (HH 🡒 NumericPAeqFormulaLogical.bi (guardedAll DD PP) (guardedAll DD QQ))).isSemiformula
theorem exsTemplateCode_isFormula {H D P Q:V} (hH:IsFormula L H)
    (hD:IsSemiformula L 1 D) (hP:IsSemiformula L 1 P) (hQ:IsSemiformula L 1 Q):
    IsFormula L (exsTemplateCode H D P Q) := by
  let HH:SF (V:=V) 0 := ⟨H,hH⟩
  let DD:SF (V:=V) 1 := ⟨D,by simpa using hD⟩
  let PP:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  let QQ:SF (V:=V) 1 := ⟨Q,by simpa using hQ⟩
  rw [←exsTemplate_val HH DD PP QQ]
  simpa using (uniformPremise HH DD PP QQ 🡒 (HH 🡒 NumericPAeqFormulaLogical.bi (guardedExs DD PP) (guardedExs DD QQ))).isSemiformula
theorem allTemplate_requested_certificate (H D P Q native lo z:V) (hH:IsFormula L H)
    (hD:IsSemiformula L 1 D) (hP:IsSemiformula L 1 P) (hQ:IsSemiformula L 1 Q)
    (hc:FormulaCovered 0 native lo z (allTemplateCode H D P Q)):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (allTemplateCode H D P Q)+1 := by
  let HH:SF (V:=V) 0 := ⟨H,hH⟩
  let DD:SF (V:=V) 1 := ⟨D,by simpa using hD⟩
  let PP:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  let QQ:SF (V:=V) 1 := ⟨Q,by simpa using hQ⟩
  have he := allTemplate_val HH DD PP QQ
  have hout := empty_requested_certificate _ (allTemplate HH DD PP QQ) native lo z (by simpa only [he] using hc)
  simpa only [he] using hout

theorem exsTemplate_requested_certificate (H D P Q native lo z:V) (hH:IsFormula L H)
    (hD:IsSemiformula L 1 D) (hP:IsSemiformula L 1 P) (hQ:IsSemiformula L 1 Q)
    (hc:FormulaCovered 0 native lo z (exsTemplateCode H D P Q)):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (exsTemplateCode H D P Q)+1 := by
  let HH:SF (V:=V) 0 := ⟨H,hH⟩
  let DD:SF (V:=V) 1 := ⟨D,by simpa using hD⟩
  let PP:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  let QQ:SF (V:=V) 1 := ⟨Q,by simpa using hQ⟩
  have he := exsTemplate_val HH DD PP QQ
  have hout := empty_requested_certificate _ (exsTemplate HH DD PP QQ) native lo z (by simpa only [he] using hc)
  simpa only [he] using hout
#print axioms allTemplateCode_isFormula
#print axioms exsTemplateCode_isFormula
#print axioms allTemplate_requested_certificate
#print axioms exsTemplate_requested_certificate
end M6.PA.NumericPAeqFormulaQuantifierTemplates


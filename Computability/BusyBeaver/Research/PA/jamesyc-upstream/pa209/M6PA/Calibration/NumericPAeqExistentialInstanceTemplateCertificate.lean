module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqExistentialInstanceTemplateCode
public import M6PA.Calibration.RelationalPredicateBinaryEmptyRequested
@[expose] public section
namespace M6.PA.NumericPAeqExistentialInstanceTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary RelationalSource.Numeric ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
theorem instance_requested_certificate (H B D Q P native lo z:V)
    (hH:IsFormula L H) (hB:IsFormula L B) (hD:IsSemiformula L 1 D)
    (hQ:IsSemiformula L 1 Q) (hP:IsSemiformula L 1 P)
    (hc:FormulaCovered 0 native lo z (instanceCode H B D Q P)):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (instanceCode H B D Q P)+1 := by
  let h:SF (V:=V) 0 := ⟨H,by simpa using hH⟩
  let b:SF (V:=V) 0 := ⟨B,by simpa using hB⟩
  let d:SF (V:=V) 1 := ⟨D,by simpa using hD⟩
  let q:SF (V:=V) 1 := ⟨Q,by simpa using hQ⟩
  let p:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  have he := instance_val h b d q p
  change (uniform h b d q p 🡒 ((h ⋏ (∃¹ (d ⋏ q))) 🡒 (b 🡒 (∃¹ (d ⋏ p))))).val=instanceCode H B D Q P at he
  rw [←he] at hc ⊢
  exact empty_requested_certificate _ (instanceProof h b d q p) native lo z hc
#print axioms instance_requested_certificate
end M6.PA.NumericPAeqExistentialInstanceTemplate


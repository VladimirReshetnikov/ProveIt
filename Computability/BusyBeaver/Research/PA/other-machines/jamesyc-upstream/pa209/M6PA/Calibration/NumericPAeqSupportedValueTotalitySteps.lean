module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedValueTotalityLeaves
public import M6PA.Calibration.NumericPAeqSupportedValueTotalitySuccessor
public import M6PA.Calibration.NumericPAeqSupportedValueTotalityBinary
public import M6PA.Calibration.NumericPAeqValueCertificatePair
@[expose] public section

namespace M6.PA.NumericPAeqSupportedValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

def ValueSupply (t:V) : Prop := ∀s b f : V, SupportedValueEnvironment s b f t → ∀g lo z : V,
  RelationalSource.Numeric.FormulaCovered 0 g lo z (guardedTotalityCode s b f t) →
  ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
    (guardedTotalityCode s b f t)+1

theorem guarded_successor_step {u:V} (ihu:ValueSupply (V:=V) u) : ValueSupply (V:=V) (qqFunc 1 1 (u∷0)) := by
  intro s b f h g lo z hc
  have hu : IsSemiterm Presentation.language s u := IsSemitermVec.singleton.mp (IsSemiterm.func.mp h.2.2.1).2
  have hchildren := (freeSupported_func (IsSemiterm.func.mp h.2.2.1).1
    (IsSemiterm.func.mp h.2.2.1).2.isUTermVec).mp h.2.2.2
  have hs : FreeSupported (len f) u := by simpa using hchildren 0 (by simp)
  have he := supportedValueEnvironment_child h hu hs
  apply source_implication_compose (inputDomain s b f) (valueTotalityCode b f u)
    (valueTotalityCode b f (qqFunc 1 1 (u∷0))) g lo z (inputDomain_valid h)
    (valueTotality_isSemiformula he.1 he.2.1 he.2.2.1 he.2.2.2)
    (valueTotality_isSemiformula h.1 h.2.1 h.2.2.1 h.2.2.2) hc
  · intro g lo z hc; exact ihu s b f he g lo z hc
  · intro g lo z hc; exact successor_requested_certificate g lo z h.1 h.2.1 hu he.2.2.2 hc

private theorem guarded_binary_step {tag u v:V} (htag:tag=2∨tag=3)
    (ihu:ValueSupply (V:=V) u) (ihv:ValueSupply (V:=V) v) : ValueSupply (V:=V) (qqFunc 2 tag (u∷(v∷0))) := by
  intro s b f h g lo z hc
  have huv := IsSemitermVec.doubleton.mp (IsSemiterm.func.mp h.2.2.1).2
  have hchildren := (freeSupported_func (IsSemiterm.func.mp h.2.2.1).1
    (IsSemiterm.func.mp h.2.2.1).2.isUTermVec).mp h.2.2.2
  have hsu : FreeSupported (len f) u := by simpa using hchildren 0 (by simp)
  have hsv : FreeSupported (len f) v := by simpa using hchildren 1 (by simp)
  have heu := supportedValueEnvironment_child h huv.1 hsu
  have hev := supportedValueEnvironment_child h huv.2 hsv
  have vu := valueTotality_isSemiformula heu.1 heu.2.1 heu.2.2.1 heu.2.2.2
  have vv := valueTotality_isSemiformula hev.1 hev.2.1 hev.2.2.1 hev.2.2.2
  apply source_implication_compose (inputDomain s b f)
    (qqAnd (valueTotalityCode b f u) (valueTotalityCode b f v))
    (valueTotalityCode b f (qqFunc 2 tag (u∷(v∷0)))) g lo z (inputDomain_valid h)
    (IsSemiformula.and.mpr ⟨vu,vv⟩) (valueTotality_isSemiformula h.1 h.2.1 h.2.2.1 h.2.2.2) hc
  · intro g lo z hc
    exact source_implication_pair _ _ _ g lo z (inputDomain_valid h) vu vv hc
      (fun g lo z hc => ihu s b f heu g lo z hc)
      (fun g lo z hc => ihv s b f hev g lo z hc)
  · intro g lo z hc
    rcases htag with rfl|rfl
    · exact addition_requested_certificate h.1 h.2.1 huv.1 huv.2 heu.2.2.2 hev.2.2.2 g lo z hc
    · exact multiplication_requested_certificate h.1 h.2.1 huv.1 huv.2 heu.2.2.2 hev.2.2.2 g lo z hc

theorem guarded_addition_step {u v:V} (ihu:ValueSupply (V:=V) u) (ihv:ValueSupply (V:=V) v) :
    ValueSupply (V:=V) (qqFunc 2 2 (u∷(v∷0))) := guarded_binary_step (Or.inl rfl) ihu ihv
theorem guarded_multiplication_step {u v:V} (ihu:ValueSupply (V:=V) u) (ihv:ValueSupply (V:=V) v) :
    ValueSupply (V:=V) (qqFunc 2 3 (u∷(v∷0))) := guarded_binary_step (Or.inr rfl) ihu ihv

#print axioms guarded_successor_step
#print axioms guarded_addition_step
#print axioms guarded_multiplication_step
end M6.PA.NumericPAeqSupportedValueTotality


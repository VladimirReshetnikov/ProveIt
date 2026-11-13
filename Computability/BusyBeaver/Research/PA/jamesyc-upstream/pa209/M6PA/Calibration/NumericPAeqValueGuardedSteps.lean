module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueGuardedLeaves
public import M6PA.Calibration.NumericPAeqValueSuccessorCertificate
public import M6PA.Calibration.NumericPAeqValueBinaryCertificate
public import M6PA.Calibration.NumericPAeqValueCertificatePair
@[expose] public section

namespace M6.PA.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

def ValueSupply (t:V) : Prop := ∀s b f : V, ValueEnvironment s b f t → ∀g lo z : V,
  RelationalSource.Numeric.FormulaCovered 0 g lo z (guardedTotalityCode s b f t) →
  ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
    (guardedTotalityCode s b f t)+1

theorem valueEnvironment_child {s b f t u:V} (h:ValueEnvironment s b f t)
    (hu:IsSemiterm Presentation.language s u) (hr:u<t) : ValueEnvironment s b f u :=
  ⟨h.1,h.2.1,hu,hr.le.trans h.2.2.2⟩

theorem guarded_successor_step {u:V} (ihu:ValueSupply (V:=V) u) : ValueSupply (V:=V) (qqFunc 1 1 (u∷0)) := by
  intro s b f h g lo z hc
  have hu : IsSemiterm Presentation.language s u := IsSemitermVec.singleton.mp (IsSemiterm.func.mp h.2.2.1).2
  have he := valueEnvironment_child h hu (unary_child_rank u)
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
  have heu := valueEnvironment_child h huv.1 (binary_left_rank tag u v)
  have hev := valueEnvironment_child h huv.2 (binary_right_rank tag u v)
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

#print axioms valueEnvironment_child
#print axioms guarded_successor_step
#print axioms guarded_addition_step
#print axioms guarded_multiplication_step
end M6.PA.NumericPAeqValueTotality

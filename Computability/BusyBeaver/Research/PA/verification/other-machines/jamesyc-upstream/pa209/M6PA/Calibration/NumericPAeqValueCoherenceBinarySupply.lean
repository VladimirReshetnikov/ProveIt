module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceBinaryStep
public import M6PA.Calibration.NumericPAeqValueCertificatePair
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
private theorem coherence_binary_step {tag u v:V} (htag:tag=2∨tag=3)
    (ihu:CoherenceSupply (V:=V) u) (ihv:CoherenceSupply (V:=V) v):
    CoherenceSupply (V:=V) (qqFunc 2 tag (u∷(v∷0))) := by
  intro s b c f g h native lo z hc
  have huv := IsSemitermVec.doubleton.mp (IsSemiterm.func.mp h.1.2.2.1).2
  have hu := coherenceEnvironment_child h huv.1 (binary_left_rank tag u v)
  have hv := coherenceEnvironment_child h huv.2 (binary_right_rank tag u v)
  have vu := comparisonCode_valid hu
  have vv := comparisonCode_valid hv
  apply source_implication_compose (coherenceInput s b c f g)
    (qqAnd (comparisonCode b c f g u) (comparisonCode b c f g v))
    (comparisonCode b c f g (qqFunc 2 tag (u∷(v∷0)))) native lo z (coherenceInput_valid h)
    (IsSemiformula.and.mpr ⟨vu,vv⟩) (comparisonCode_valid h) hc
  · intro native lo z hc
    exact source_implication_pair _ _ _ native lo z (coherenceInput_valid h) vu vv hc
      (fun native lo z hc => ihu s b c f g hu native lo z hc)
      (fun native lo z hc => ihv s b c f g hv native lo z hc)
  · intro native lo z hc
    rcases htag with rfl|rfl
    · exact addition_comparison_certificate h native lo z hc
    · exact multiplication_comparison_certificate h native lo z hc

theorem coherence_addition_step {u v:V} (ihu:CoherenceSupply (V:=V) u) (ihv:CoherenceSupply (V:=V) v):
    CoherenceSupply (V:=V) (qqFunc 2 2 (u∷(v∷0))) := coherence_binary_step (Or.inl rfl) ihu ihv
theorem coherence_multiplication_step {u v:V} (ihu:CoherenceSupply (V:=V) u) (ihv:CoherenceSupply (V:=V) v):
    CoherenceSupply (V:=V) (qqFunc 2 3 (u∷(v∷0))) := coherence_binary_step (Or.inr rfl) ihu ihv
#print axioms coherence_binary_step
#print axioms coherence_addition_step
#print axioms coherence_multiplication_step
end M6.PA.NumericPAeqValueCoherence

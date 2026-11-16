module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedVectorRealizationLeaves
public import M6PA.Calibration.NumericPAeqSupportedVectorRealizationSteps
@[expose] public section
namespace M6.PA.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence NumericPAeqValueVectorRealization ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
def VectorSupply (t:V):Prop :=
  ∀s r b f a w,SupportedVectorEnvironment s r b f a w t→∀native lo z,
    RelationalSource.Numeric.FormulaCovered 0 native lo z (vectorCode s r b f a w t)→
      ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
        (vectorCode s r b f a w t)+1

theorem vector_bvar_supply (i:V) : VectorSupply (V:=V) (qqBvar i) := by
  intro s r b f a w h native lo z hc; exact vector_bvar_certificate h native lo z hc
theorem vector_fvar_supply (i:V):VectorSupply (V:=V) (qqFvar i) := by
  intro s r b f a w h native lo z hc; exact vector_fvar_certificate h native lo z hc
theorem vector_zero_supply : VectorSupply (V:=V) (qqFunc 0 0 0) := by
  intro s r b f a w h native lo z hc; exact vector_zero_certificate h native lo z hc

theorem vector_successor_step {t:V} (ih:VectorSupply (V:=V) t):
    VectorSupply (V:=V) (qqFunc 1 1 (t∷0)) := by
  intro s r b f a w h native lo z hc
  have he : SupportedVectorEnvironment s r b f a w t := by simpa using vectorEnvironment_at h (show (0:V)<1 by simp)
  apply source_implication_compose (vectorInput s r b f a w) (vectorComparison b f a w t)
    (vectorComparison b f a w (qqFunc 1 1 (t∷0))) native lo z
    (vectorInput_valid h) (vectorComparison_valid he) (vectorComparison_valid h) hc
  · intro native lo z hc; exact ih s r b f a w he native lo z hc
  · intro native lo z hc; exact vector_successor_comparison_certificate h native lo z hc

theorem vector_binary_step {t v tag:V} (ih:VectorSupply (V:=V) t) (iv:VectorSupply (V:=V) v)
    (htag:tag=2∨tag=3):VectorSupply (V:=V) (qqFunc 2 tag (t∷(v∷0))) := by
  intro s r b f a w h native lo z hc
  have ht : SupportedVectorEnvironment s r b f a w t := by simpa using vectorEnvironment_at h (show (0:V)<2 by simp)
  have hv : SupportedVectorEnvironment s r b f a w v := by simpa using vectorEnvironment_at h (show (1:V)<2 by simp)
  apply source_implication_compose (vectorInput s r b f a w)
    (qqAnd (vectorComparison b f a w t) (vectorComparison b f a w v))
    (vectorComparison b f a w (qqFunc 2 tag (t∷(v∷0)))) native lo z
    (vectorInput_valid h) (IsSemiformula.and.mpr ⟨vectorComparison_valid ht,vectorComparison_valid hv⟩)
    (vectorComparison_valid h) hc
  · intro native lo z hc
    apply source_implication_pair _ _ _ native lo z (vectorInput_valid h)
      (vectorComparison_valid ht) (vectorComparison_valid hv) hc
    · intro native lo z hc; exact ih s r b f a w ht native lo z hc
    · intro native lo z hc; exact iv s r b f a w hv native lo z hc
  · intro native lo z hc; exact vector_binary_comparison_certificate h htag native lo z hc
#print axioms vector_bvar_supply
#print axioms vector_successor_step
#print axioms vector_binary_step
end M6.PA.NumericPAeqSupportedVectorRealization

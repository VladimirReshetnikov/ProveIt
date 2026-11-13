import DiophantineConsistency.CompactBitRotation
import DiophantineConsistency.BandCarryInputs
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ActualTemporalBand
open DiophantineConsistency CompactBitRotation ArithmeticWindowDigits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_temporal_word (n q u v C R w A F : V)
    (hn : 0<n) (hM : 0<Exp.exp (67*n)-1)
    (hq : q=Exp.exp (67*n)) (hu : 0<u) (hC : C=q-u-v)
    (hw : w=Exp.exp (R-67*n))
    (hgraph : (A+w*C)%(Exp.exp (67*n)-1)=F) :
    (A+temporalWord n (R-67*n) C)%(Exp.exp (67*n)-1)=F ∧
      temporalWord n (R-67*n) C<Exp.exp (67*n) ∧
      ∀ k : V, dig 67 (temporalWord n (R-67*n) C) k ≤ Exp.exp 67-1 := by
  have hbound : C<Exp.exp (67*n) := by
    rw [hC]
    exact BandCarryInputs.source_word_bound q n u v hq hu
  refine ⟨?_, temporal_word_lt n (R-67*n) C hn hbound, ?_⟩
  · apply replace_temporal n (R-67*n) C A F hn hM
    rw [← hw]
    exact hgraph
  · intro k
    exact temporal_digit_le n (R-67*n) C k
#print axioms ActualTemporalBand.graph_temporal_word
end ActualTemporalBand

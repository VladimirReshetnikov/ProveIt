import PA196PAQVecGrowth

/-! A model-internal invariant for two coded traces: if one iterates qVec
and the other iterates its numeric majorant, the latter bounds the former.
The trace length and indices are arbitrary model elements. Existence of the
coded traces and any connection to the candidate-PRA tower are separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PAQVecTraceInvariant
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem trace_bound (limit qTrace boundTrace : V)
    (hbase : qTrace.[0] ≤ boundTrace.[0])
    (hstep : ∀ i < limit,
      qTrace.[i+1] = qVec ℒₒᵣ qTrace.[i] ∧
      boundTrace.[i+1] = PRAWitnessCodeGrowth.tau (boundTrace.[i]+8) (22*boundTrace.[i]+22)) :
    ∀ i ≤ limit, qTrace.[i] ≤ boundTrace.[i] := by
  intro i
  induction i using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro _
    exact hbase
  case succ i ih =>
    intro hi
    have hlt : i < limit := lt_iff_succ_le.mpr hi
    have hprev : qTrace.[i] ≤ boundTrace.[i] := ih (le_trans le_self_add hi)
    obtain ⟨hq, hb⟩ := hstep i hlt
    rw [hq, hb]
    exact le_trans (PA196PAQVecGrowth.qVec_le qTrace.[i])
      (PRAWitnessCodeGrowth.tau_mono (add_le_add hprev le_rfl)
        (add_le_add (mul_le_mul' le_rfl hprev) le_rfl))

#print axioms trace_bound
end PA196PAQVecTraceInvariant

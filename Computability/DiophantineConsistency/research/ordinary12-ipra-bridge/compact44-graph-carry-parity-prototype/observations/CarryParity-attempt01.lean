import DiophantineConsistency.ParityPhase
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CarryParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
variable {V ι : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [Fintype ι]

theorem raw_plus_incoming_even (n F : V) (D a X : ι→V)
    (h : CarryInput 67 n F 1 D a X) (t : V) (ht : t<n)
    (heven : dig 67 F t%2=0) :
    carry 67 n a X (cyc n t 1)≤1 ∧
    (raw 67 a X t + carry 67 n a X (cyc n t 1))%2=0 := by
  constructor
  · exact h.carry_le (cyc_lt h.n_pos _ _)
  · have hc := (h.end_around_carry t ht).2.2.1
    rw [hc]
    have he : Exp.exp (67:V)=Exp.exp 66*2 := by
      rw [show (67:V)=66+1 by norm_num,exp_succ]
    rw [he,show Exp.exp (66:V)*2*carry 67 n a X t =
      (Exp.exp (66:V)*carry 67 n a X t)*2 by ring,
      mod_add_mul _ _ (by norm_num : (0:V)<2)]
    exact heven
#print axioms CarryParity.raw_plus_incoming_even
end CarryParity

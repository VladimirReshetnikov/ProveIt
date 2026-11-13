import DiophantineConsistency.ArithmeticPellFirstIndex

/-! Model-level transport extracted from the maintained carrier's first
factor, conditional on the scalar gap, rank multiplier bound and transport
equation. This does not yet obtain them from the actual fixed-port zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Model69Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Positive, b-divisible transport from the exact additive carrier equation.
The chosen `G` equals `(K+w)*C-F` with no hidden signed subtraction. -/
theorem positive_divisible_transport (b q K w F alpha C z : V)
    (hq : q=b+1) (hz : 0<z) (hC : 0<C)
    (hsum : F+alpha+C=q) (hF : F<q) (hw : q≤w)
    (ht : (K+w)*q+q=(K+w)*(F+alpha)+F+z*(q-1)+1) :
    let G := b*(z-1)
    0<G ∧ b∣G ∧ (K+w)*C=F+G := by
  have hq1 : q-1+1=q := by rw [hq]; simp
  have hqsub : q-1=b := by rw [hq]; simp
  have hz1 : z-1+1=z := tsub_add_cancel_of_le (pos_iff_one_le.mp hz)
  have he : (K+w)*C=F+(z-1)*(q-1) := by
    have h1 : (K+w)*(F+alpha)+((K+w)*C+(q-1)+1) =
        (K+w)*(F+alpha)+(F+(z-1)*(q-1)+(q-1)+1) := by
      calc
        _=(K+w)*(F+alpha+C)+(q-1+1) := by ring
        _=(K+w)*q+q := by rw [hsum,hq1]
        _=(K+w)*(F+alpha)+F+z*(q-1)+1 := ht
        _=_ := by
          conv_lhs => rw [←hz1]
          ring
    exact add_right_cancel (add_right_cancel (add_left_cancel h1))
  rw [hqsub] at he
  have hqA : q≤(K+w)*C := by
    calc q≤w := hw
      _≤K+w := le_add_of_nonneg_left (Arithmetic.zero_le K)
      _≤(K+w)*C := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hC)
  have hFG : F < F+(z-1)*b := by
    rw [←he]
    exact lt_of_lt_of_le hF hqA
  have hpos : 0<(z-1)*b := by
    have hh : F+0<F+(z-1)*b := by simpa only [add_zero] using hFG
    exact (add_lt_add_iff_left F).mp hh
  refine ⟨?_,⟨z-1,rfl⟩,?_⟩
  · simpa only [mul_comm] using hpos
  · simpa only [mul_comm] using he
end Model69Transport
#print axioms Model69Transport.positive_divisible_transport

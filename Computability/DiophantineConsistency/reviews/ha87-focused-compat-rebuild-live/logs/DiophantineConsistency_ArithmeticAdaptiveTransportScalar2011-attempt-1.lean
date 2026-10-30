import DiophantineConsistency.ArithmeticAdaptiveRadix2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveTransportScalar2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticGcdNormalization ArithmeticPellStrongDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Euclidean cancellation of the actual transport difference. -/
theorem normalize_transport (q X K F alpha w j : V) (hqgt : 1<q) (hj : 0<j)
    (hX : X=q*w)
    (hjt : q*(X+K*q)=(F+alpha)*(X+K*q)+F*q+(q-1)*j) :
    ∃ z : V, 0<z ∧ j=q*z ∧ q*(K+w)=(F+alpha)*(K+w)+F+(q-1)*z := by
  let A : V := X+K*q
  have hq : 0<q := lt_trans (by simp : (0:V)<1) hqgt
  have hq1 : q-1+1=q := tsub_add_cancel_of_le (le_of_lt hqgt)
  have hA : A=q*(K+w) := by dsimp [A]; rw [hX]; ring
  have hd1 : q∣(F+alpha)*A+F*q := by
    refine ⟨(F+alpha)*(K+w)+F,?_⟩
    rw [hA]; ring
  have hd2 : q∣((q-1)*j)+((F+alpha)*A+F*q) := by
    refine ⟨A,?_⟩
    rw [hjt]; ring
  have hd : q∣(q-1)*j := dvd_remove hd2 hd1
  have hbez : Bez (q-1) q 1 := by
    refine ⟨1,0,0,1,?_⟩
    simp only [mul_one,mul_zero,add_zero,zero_add]
    rw [add_comm,hq1]
  have hjdiv : q∣j := unit_certificate_cancel hbez hd
  obtain ⟨z,hjz⟩ := hjdiv
  have hzpos : 0<z := pos_of_mul_pos_right (by rw [←hjz]; exact hj) (by simp)
  have ht : q*(K+w)=(F+alpha)*(K+w)+F+(q-1)*z := by
    apply mul_left_cancel₀ (ne_of_gt hq)
    calc
      q*(q*(K+w))=q*A := by rw [hA]
      _=(F+alpha)*A+F*q+(q-1)*j := hjt
      _=q*((F+alpha)*(K+w)+F+(q-1)*z) := by rw [hA,hjz]; ring
  exact ⟨z,hzpos,hjz,ht⟩

end DiophantineConsistency.ArithmeticAdaptiveTransportScalar2011

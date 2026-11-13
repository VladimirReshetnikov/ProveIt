import Direct80Parity
import DiophantineConsistency.ArithmeticGcdNormalization

/-! An explicit unit certificate for b and (q²+1)² when q=b+1 is even. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80Coprime
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticGcdNormalization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem square_unit_certificate (b q mu : V) (hq : q=b+1)
    (hmu : mu=q*q+1) (heven : ∃w : V, q=2*w) : Bez b (mu*mu) 1 := by
  obtain ⟨w,hw⟩ := heven
  have hqpos : 0<q := by rw [hq]; simp
  have hwpos : 0<w := pos_of_mul_pos_right (by rw [←hw]; exact hqpos) (by simp)
  rcases zero_or_succ w with hzero | ⟨t,ht⟩
  · rw [hzero] at hwpos
    exact False.elim ((lt_irrefl (0:V)) hwpos)
  · have hb : b=2*t+1 := by
      apply add_right_cancel (b:=(1:V))
      calc
        b+1=q := hq.symm
        _=2*w := hw
        _=2*(t+1) := by rw [ht]
        _=(2*t+1)+1 := by ring
    let d : V := t*t+t
    let coeff : V := (b*(b+2)*(b+2)+4*(b+2))*d+b
    refine ⟨0,d,coeff,0,?_⟩
    simp only [mul_zero,add_zero]
    dsimp [coeff,d]
    rw [hmu,hq,hb]
    ring

theorem square_cancel (b q mu e : V) (hq : q=b+1)
    (hmu : mu=q*q+1) (heven : ∃w : V, q=2*w)
    (hdiv : mu*mu∣b*e) : mu*mu∣e :=
  unit_certificate_cancel (square_unit_certificate b q mu hq hmu heven) hdiv

#print axioms Direct80Coprime.square_unit_certificate
#print axioms Direct80Coprime.square_cancel
end Direct80Coprime

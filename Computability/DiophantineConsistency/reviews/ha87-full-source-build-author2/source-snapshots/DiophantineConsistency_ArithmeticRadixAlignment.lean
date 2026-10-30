import Foundation.FirstOrder.Arithmetic.Exponential.Log
import Mathlib.Tactic.Ring

/-! Internal exponent alignment for a factor congruent to one modulo 2^d-1.
All indices are elements of an arbitrary IΣ1 model. The concrete current
polynomial premises and its native encoding are separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticRadixAlignment
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma radix_add_one (d : V) : (Exp.exp d-1)+1=Exp.exp d :=
  sub_add_self_of_le (one_le_exp d)

lemma radix_gt_one {d : V} (hd : 2≤d) : 1<Exp.exp d-1 := by
  have hx : 2<Exp.exp d := by
    simpa using (exp_monotone.mpr (lt_of_lt_of_le one_lt_two hd) :
      Exp.exp (1:V)<Exp.exp d)
  exact one_lt_iff_two_le.mpr (le_sub_one_of_lt hx)

/-- A genuine Σ1 induction supplies the nonnegative block quotient. -/
theorem block_quotient (d n : V) :
    ∃ z : V, Exp.exp (d*n)=1+(Exp.exp d-1)*z := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0,by simp⟩
  case succ n ih =>
    obtain ⟨z,hz⟩ := ih
    refine ⟨1+Exp.exp d*z,?_⟩
    rw [show d*(n+1)=d*n+d by ring,exp_add,hz]
    rw [show Exp.exp d=(Exp.exp d-1)+1 from (radix_add_one d).symm]
    simp only [add_tsub_cancel_right]
    ring

/-- Reduction of an arbitrary internal exponent, with a nonzero modulus. -/
theorem exp_mod_radix (d u : V) (hd : 2≤d) :
    Exp.exp u % (Exp.exp d-1)=Exp.exp (u%d) % (Exp.exp d-1) := by
  have hb : 0<Exp.exp d-1 := lt_trans (by simp) (radix_gt_one hd)
  obtain ⟨z,hz⟩ := block_quotient d (u/d)
  have he : Exp.exp u=(1+(Exp.exp d-1)*z)*Exp.exp (u%d) := by
    conv_lhs => rw [←div_add_mod u d]
    rw [exp_add,hz]
  rw [he,show (1+(Exp.exp d-1)*z)*Exp.exp (u%d)=
    (Exp.exp d-1)*(z*Exp.exp (u%d))+Exp.exp (u%d) by ring]
  exact mod_mul_add' _ _ hb

/-- The boundary power equal to the modulus has residue zero, not one. -/
theorem aligned_remainder (d u J : V) (hd : 2≤d)
    (he : Exp.exp u=(Exp.exp d-1)*J+1) : u%d=0 := by
  have hb1 : 1<Exp.exp d-1 := radix_gt_one hd
  have hmod : Exp.exp (u%d) % (Exp.exp d-1)=1 := by
    rw [←exp_mod_radix d u hd,he]
    simpa only [mul_comm J (Exp.exp d-1)] using
      mod_mul_add_of_lt J (Exp.exp d-1) hb1
  have hr : u%d<d := mod_lt u (lt_of_lt_of_le (by simp) hd)
  have hsmall : Exp.exp (u%d)≤Exp.exp d-1 :=
    le_sub_one_of_lt (exp_monotone.mpr hr)
  have hstrict : Exp.exp (u%d)<Exp.exp d-1 := by
    rcases lt_or_eq_of_le hsmall with hlt | heq
    · exact hlt
    · rw [heq,mod_self] at hmod
      exact False.elim (zero_ne_one hmod)
  have hone : Exp.exp (u%d)=1 := by
    simpa only [mod_eq_self_of_lt hstrict] using hmod
  exact exp_inj (by simpa using hone)

/-- A positive coefficient forces a positive internal block count. -/
theorem aligned_exponent (d u J : V) (hd : 2≤d) (hJ : 0<J)
    (he : Exp.exp u=(Exp.exp d-1)*J+1) :
    ∃ N : V, 0<N ∧ u=d*N := by
  have hrem := aligned_remainder d u J hd he
  have hu : u=d*(u/d) := by
    simpa only [hrem,add_zero] using (div_add_mod u d).symm
  have hgt : (1:V)<Exp.exp u := by
    rw [he]
    exact lt_add_of_pos_left 1 (mul_pos (lt_trans (by simp) (radix_gt_one hd)) hJ)
  have hup : 0<u := exp_monotone.mp (by simpa only [exp_zero] using hgt)
  have hN : 0<u/d := pos_of_mul_pos_right (by rw [←hu]; exact hup) (by simp)
  exact ⟨u/d,hN,hu⟩

/-- Every divisor here is an actual internal exponential, without an
external prime-factorization or exponent oracle. -/
theorem exponential_factor (R q : V) (hq : q∣Exp.exp R) :
    q=Exp.exp (log q) :=
  (exp_of_exponential (exponential_of_pow2 (Pow2.of_dvd hq (exp_pow2 R)))).symm

/-- The full factor theorem derives positivity, radix alignment and the
exact residual exponential. Subtraction is used only after its bound. -/
theorem factor_alignment (d J R w : V) (hd : 2≤d) (hJ : 0<J)
    (he : Exp.exp R=w*((Exp.exp d-1)*J+1)) :
    0<w ∧ ∃ N : V, 0<N ∧
      (Exp.exp d-1)*J+1=Exp.exp (d*N) ∧
      d*N≤R ∧ w=Exp.exp (R-d*N) := by
  let q:V := (Exp.exp d-1)*J+1
  have hq : 0<q := by dsimp [q]; simp
  have hw : 0<w := pos_of_mul_pos_left (by rw [←he]; exact exp_pos R) (by simp)
  have hdvd : q∣Exp.exp R := ⟨w,by simpa [q,mul_comm] using he⟩
  have hpower : q=Exp.exp (log q) := exponential_factor R q hdvd
  obtain ⟨N,hN,hu⟩ := aligned_exponent d (log q) J hd hJ hpower.symm
  have hqN : q=Exp.exp (d*N) := by simpa [hu] using hpower
  have hbound : d*N≤R := exp_monotone_le.mp (by
    rw [←hqN]
    exact le_of_dvd (exp_pos R) hdvd)
  have hrest : Exp.exp R=q*Exp.exp (R-d*N) := by
    conv_lhs => rw [←add_tsub_self_of_le hbound]
    rw [exp_add,←hqN]
  have hcancel : q*w=q*Exp.exp (R-d*N) := by
    simpa only [q,mul_comm] using he.symm.trans hrest
  exact ⟨hw,N,hN,hqN,hbound,mul_left_cancel₀ (ne_of_gt hq) hcancel⟩

end DiophantineConsistency.ArithmeticRadixAlignment

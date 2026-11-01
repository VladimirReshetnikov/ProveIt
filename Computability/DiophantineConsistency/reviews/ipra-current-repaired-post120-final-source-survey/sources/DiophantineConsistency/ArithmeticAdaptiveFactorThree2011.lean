import DiophantineConsistency.ArithmeticAdaptiveMainCongruence2011

/-! Cancellation of the adaptive constant-three factor in internal arithmetic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveFactorThree2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticGcdNormalization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A unit certificate modulo q cancels any fixed external power of q. -/
theorem cancel_unit_power (q H : V) (hq : 0<q) (hu : Bez H q 1) (n : ℕ)
    (t : V) (h : q^n∣H*t) : q^n∣t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have hqpow : q∣q^(n+1) := ⟨q^n, by rw [pow_succ]; ring⟩
    have hqt : q∣t := unit_certificate_cancel hu (dvd_trans hqpow h)
    obtain ⟨u,hu'⟩ := hqt
    have hnext : q^n∣H*u := by
      obtain ⟨w,hw⟩ := h
      refine ⟨w,?_⟩
      apply mul_left_cancel₀ (ne_of_gt hq)
      calc
        q*(H*u)=H*t := by rw [hu']; ring
        _=q^(n+1)*w := hw
        _=q*(q^n*w) := by rw [pow_succ]; ring
    obtain ⟨w,hw⟩ := ih u hnext
    refine ⟨w,?_⟩
    rw [hu',hw,pow_succ]
    ring

/-- An element congruent to one modulo q has an explicit unit certificate. -/
theorem one_plus_unit (q d : V) : Bez (1+q*d) q 1 := by
  refine ⟨0,d,1,0,?_⟩
  ring

/-- The loss of at most one q factor holds even when 3 divides q. -/
theorem cancel_factor_three (q Y X t : V) (hq : 0<q)
    (hY : q^3∣Y) (hd : q^5∣(3+4*Y*(X+1))*t) : q^4∣t := by
  obtain ⟨s,hs⟩ := hY
  let H : V := 3+4*Y*(X+1)
  by_cases h3 : (3:V)∣q
  · obtain ⟨r,hr⟩ := h3
    let d : V := 12*r*r*s*(X+1)
    let B : V := 1+q*d
    have hH : H=3*B := by dsimp [H,B,d]; rw [hs,hr]; ring
    have hpow : q^4∣B*t := by
      obtain ⟨w,hw⟩ := hd
      refine ⟨r*w,?_⟩
      apply mul_left_cancel₀ (by simp : (3:V)≠0)
      calc
        3*(B*t)=H*t := by rw [hH]; ring
        _=q^5*w := hw
        _=3*(q^4*(r*w)) := by rw [hr]; ring
    exact cancel_unit_power q B hq (one_plus_unit q d) 4 t hpow
  · have hm0 : q%3≠0 := fun h => h3 (mod_eq_zero_iff_dvd.mp h)
    have hmLt : q%3<3 := mod_lt q (by simp : (0:V)<3)
    have hm : q%3=1 ∨ q%3=2 := by
      have hle : q%3≤2 := lt_succ_iff_le.mp (by simpa only [show (2:V)+1=3 by ring] using hmLt)
      by_cases h2 : q%3=2
      · exact Or.inr h2
      · have hlt : q%3<2 := lt_of_le_of_ne hle h2
        rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hlt) with h0 | h1
        · exact False.elim (hm0 h0)
        · exact Or.inl h1
    have he := div_add_mod q 3
    let d : V := 4*q*q*s*(X+1)
    have hH : H=3+q*d := by dsimp [H,d]; rw [hs]; ring
    have hu : Bez H q 1 := by
      rcases hm with hm | hm
      · have hqeq : q=3*(q/3)+1 := by simpa only [hm] using he.symm
        refine ⟨q/3,0,0,1+(q/3)*d,?_⟩
        rw [hH]
        simp only [mul_zero,zero_add,add_zero]
        calc
          1+(3+q*d)*(q/3)=(3*(q/3)+1)+q*((q/3)*d) := by ring
          _=q+q*((q/3)*d) := congrArg (fun z : V => z+q*((q/3)*d)) hqeq.symm
          _=q*(1+(q/3)*d) := by ring
      · have hqeq : q=3*(q/3)+2 := by simpa only [hm] using he.symm
        refine ⟨0,1+(q/3+1)*d,q/3+1,0,?_⟩
        rw [hH]
        simp only [mul_zero,add_zero]
        calc
          1+q*(1+(q/3+1)*d)=(q+1)+q*((q/3+1)*d) := by ring
          _=(3*(q/3)+2+1)+q*((q/3+1)*d) :=
            congrArg (fun z : V => z+1+q*((q/3+1)*d)) hqeq
          _=(3+q*d)*(q/3+1) := by ring
    have hd4 : q^4∣H*t := dvd_trans ⟨q,by ring⟩ hd
    exact cancel_unit_power q H hq hu 4 t hd4
end DiophantineConsistency.ArithmeticAdaptiveFactorThree2011

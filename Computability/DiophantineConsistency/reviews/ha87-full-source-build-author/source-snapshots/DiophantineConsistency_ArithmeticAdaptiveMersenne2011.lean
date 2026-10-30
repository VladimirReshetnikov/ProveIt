import DiophantineConsistency.ArithmeticAdaptivePowerFinish2011
import DiophantineConsistency.ArithmeticRadixAlignment

/-! Internal cancellation of the adaptive factor three at a Mersenne port. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveMersenne2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticGcdNormalization ArithmeticRadixAlignment
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem same_mul {m x y z w : V} (hm : 0<m)
    (h : x%m=y%m) (h' : z%m=w%m) : (x*z)%m=(y*w)%m := by
  rw [mod_mul hm,mod_mul (a:=y) hm,h,h']

/-- For internal d≥4 and any internal exponent u, 3·2^u is not one modulo 2^d−1. -/
theorem three_power_not_one (d u J : V) (hd : 4≤d) :
    3*Exp.exp u ≠ (Exp.exp d-1)*J+1 := by
  intro heq
  let M : V := Exp.exp d-1
  let r : V := u%d
  let P : V := Exp.exp r
  let D : V := Exp.exp d
  let E : V := Exp.exp (d-1)
  have hd2 : (2:V)≤d := le_trans (by norm_num : (2:V)≤4) hd
  have hd1 : (1:V)≤d := le_trans (by simp : (1:V)≤2) hd2
  have hm1 : 1<M := radix_gt_one hd2
  have hm : 0<M := lt_trans (by simp) hm1
  have hdEq : d-1+1=d := tsub_add_cancel_of_le hd1
  have hr : r<d := mod_lt u (lt_of_lt_of_le (by simp) hd2)
  have hr1 : r+1≤d := lt_iff_succ_le.mp hr
  have hrle : r≤d-1 := by
    apply (add_le_add_iff_right (1:V)).mp
    rw [hdEq]; exact hr1
  have hP : P≤E := exp_monotone_le.mpr hrle
  have h2P : 2*P≤D := by
    have h := exp_monotone_le.mpr hr1
    simpa only [exp_succ] using h
  have hEgt : 1<E := by
    have h2 : (2:V)≤d-1 := by
      apply (add_le_add_iff_right (1:V)).mp
      rw [hdEq]
      exact le_trans (by norm_num : (2:V)+1≤4) hd
    have h := exp_monotone.mpr (lt_of_lt_of_le (by simp : (0:V)<2) h2)
    simpa only [exp_zero] using h
  have hD : D=2*E := by
    dsimp [D,E]
    conv_lhs => rw [←hdEq]
    rw [exp_succ]
  have hPplus : P+1<D := calc
    P+1≤E+1 := _root_.add_le_add hP (le_refl 1)
    _<2*E := by
      have h := add_lt_add_left hEgt E
      simpa only [two_mul,add_comm] using h
    _=D := hD.symm
  have hbound : 3*P<2*M+1 := by
    apply (add_lt_add_iff_right (1:V)).mp
    calc
      3*P+1=2*P+(P+1) := by ring
      _<D+D := add_lt_add_of_le_of_lt h2P hPplus
      _=(2*M+1)+1 := by
        have h : D=M+1 := (radix_add_one d).symm
        rw [h]; ring
  have hmod0 : (3*Exp.exp u)%M=1 := by
    rw [heq]
    simpa only [M,mul_comm J (Exp.exp d-1)] using mod_mul_add_of_lt J (Exp.exp d-1) hm1
  have hmod : (3*P)%M=1 := by
    have h := same_mul hm (show (3:V)%M=(3:V)%M from rfl) (exp_mod_radix d u hd2)
    rw [hmod0] at h
    exact h.symm
  let t : V := (3*P)/M
  have he : M*t+1=3*P := by
    have h := div_add_mod (3*P) M
    rw [hmod] at h
    exact h
  have htlt : t<2 := by
    by_contra hn
    have ht2 : 2≤t := le_of_not_gt hn
    have hle : 2*M+1≤3*P := calc
      2*M+1≤M*t+1 := _root_.add_le_add (by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left ht2 (Arithmetic.zero_le M)) (le_refl 1)
      _=3*P := he
    exact (not_le_of_gt hbound) hle
  rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp htlt) with h0|h1
  · have hP1 : 1≤P := one_le_exp r
    have h3 : (3:V)≤3*P := le_mul_of_one_le_right (by simp) hP1
    rw [h0,mul_zero,zero_add] at he
    exact (not_le_of_gt (by norm_num : (1:V)<3)) (by rw [he]; exact h3)
  · have h3D : (3:V)∣D := by
      refine ⟨P,?_⟩
      calc
        D=M+1 := (radix_add_one d).symm
        _=3*P := by simpa only [h1,mul_one] using he
    have hp2 : Pow2 (3:V) := Pow2.of_dvd h3D (exp_pow2 d)
    have htwo : (2:V)∣3 := hp2.two_dvd (by simp)
    have hz : (3:V)%2=0 := mod_eq_zero_iff_dvd.mpr htwo
    have hone : (3:V)%2=1 := by
      have h := mod_mul_add_of_lt (1:V) (2:V) (by simp : (1:V)<2)
      simpa only [show (1:V)*2+1=3 by ring] using h
    rw [hone] at hz
    exact (by simp : (1:V)≠0) hz

/-- The factor three cannot occur in q when q−1 is a Mersenne multiple. -/
theorem not_three_dvd (d R q J : V) (hd : 4≤d)
    (hq : q=(Exp.exp d-1)*J+1) (hdiv : q∣3*Exp.exp R) : ¬(3:V)∣q := by
  intro h3
  obtain ⟨w,hw⟩ := h3
  obtain ⟨z,hz⟩ := hdiv
  have hwdiv : w∣Exp.exp R := by
    refine ⟨z,?_⟩
    apply mul_left_cancel₀ (by simp : (3:V)≠0)
    calc
      3*Exp.exp R=q*z := hz
      _=3*(w*z) := by rw [hw]; ring
  have hwexp : w=Exp.exp (log w) := exponential_factor R w hwdiv
  have he : 3*Exp.exp (log w)=(Exp.exp d-1)*J+1 := by rw [←hwexp,←hw]; exact hq
  exact three_power_not_one d (log w) J hd he

/-- Exact cancellation by the derived additive Bezout certificate. -/
theorem cancel_three (d R q J : V) (hd : 4≤d)
    (hq : q=(Exp.exp d-1)*J+1) (hdiv : q∣3*Exp.exp R) : q∣Exp.exp R := by
  have h3 := not_three_dvd d R q J hd hq hdiv
  have hm0 : q%3≠0 := fun h => h3 (mod_eq_zero_iff_dvd.mp h)
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
  have hunit : Bez (3:V) q 1 := by
    rcases hm with hm | hm
    · have hqeq : q=3*(q/3)+1 := by simpa only [hm] using he.symm
      refine ⟨q/3,0,0,1,?_⟩
      simpa only [mul_zero,zero_add,add_zero,mul_one,add_comm] using hqeq.symm
    · have hqeq : q=3*(q/3)+2 := by simpa only [hm] using he.symm
      refine ⟨0,1,q/3+1,0,?_⟩
      simp only [mul_zero,add_zero,mul_one]
      calc
        1+q=1+(3*(q/3)+2) := congrArg (fun z : V => 1+z) hqeq
        _=3*(q/3+1) := by ring
  exact unit_certificate_cancel hunit hdiv
end DiophantineConsistency.ArithmeticAdaptiveMersenne2011

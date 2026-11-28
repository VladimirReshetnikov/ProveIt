import GRHArticle.SingularModuli.FactorialWindowLength
import GRHArticle.SingularModuli.SevenAdicReciprocalWindows
import Mathlib.NumberTheory.Multiplicity

/-!
# The factorial test for both infinite dyadic degree families

The same reciprocal congruence proves sharp cutoff at each degree in the
two families of `smd:thm:dyadic`. This identifies their local full-support
property independently of the CM class-number and reduction inputs.
-/

namespace GRHArticle.SingularModuli

local instance primeSevenForDyadicDegrees : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- A modular inverse of a small multiplier passes every interval test if
the modulus exceeds the base-seven digit bound. -/
theorem seven_inverse_full_cutoff {c h m : ℕ} (hh : 0 < h) (hc₀ : 2 ≤ c) (hc₁ : c ≤ 4)
    (hc : c*h ≡ 1 [MOD 7^m]) (hlog : 6*(Nat.log 7 h+1) < 7^m) :
    sparseDiskRootBound 7 h 1 hh (by norm_num) = h-1 := by
  apply (sparseDiskRootBound_eq_pred_iff_intervals hh (by norm_num)).mpr
  apply factorialWeight_crossing_of_oneSided
  · intro u hu
    let r := h-u
    have hr : 0 < r := by dsimp [r]; omega
    have hrh : r ≤ h := Nat.sub_le _ _
    have hrep : h-r = u := by dsimp [r]; omega
    have hv : (∑ i ∈ Finset.range r, padicValNat 7 (u+i+1)) < r := by
      by_cases hlong : 6*(Nat.log 7 h+1) < 5*r
      · exact interval_valuation_sum_lt_length_of_log hu.le hh.ne' (by decide) hlong
      · have hmul := Nat.mul_le_mul_right r hc₁
        have hsmall : c*r+1 < 7^m := by omega
        simpa only [hrep] using seven_inverse_left_short hc₀ hc₁ hr hrh hc hsmall
    rw [one_mul,← Nat.cast_sum]
    exact_mod_cast hv
  · intro r hr
    have hv : (∑ i ∈ Finset.range r, padicValNat 7 (h+i+1)) < r := by
      by_cases hlong : 6*(Nat.log 7 h+1) < 5*r
      · exact interval_valuation_sum_lt_length_of_log le_rfl hh.ne' (by decide) hlong
      · have hmul := Nat.mul_le_mul_right r hc₁
        exact seven_inverse_right_short hc₀ hc₁ hr hc (by omega)
    rw [one_mul,← Nat.cast_sum]
    exact_mod_cast hv

/-- The lifting of 8 = 1 + 7 supplies one extra power of seven at each
step of the family. -/
theorem eight_pow_seven_pow_modEq_one (n : ℕ) : 8^(7^n) ≡ 1 [MOD 7^(n+1)] := by
  have hval := padicValNat.pow_sub_pow (p := 7) (x := 8) (y := 1) (n := 7^n)
    (by decide) (by decide) (by decide) (by decide) (by positivity)
  rw [one_pow, show 8-1=7 by decide, padicValNat_self, padicValNat.prime_pow] at hval
  apply Nat.ModEq.symm
  apply (Nat.modEq_iff_dvd' (show 1 ≤ 8^(7^n) by exact Nat.one_le_iff_ne_zero.mpr (by positivity))).mpr
  convert pow_padicValNat_dvd (p := 7) (n := 8^(7^n)-1) using 2
  omega

private theorem dyadic_log_bound {e P : ℕ} (hP : 7 ≤ P) (he : e+1 ≤ 3*P) :
    6*(Nat.log 7 (2^e)+1) < 7*P := by
  have hp := Nat.pow_log_le_self 7 (show 2^e ≠ 0 by positivity)
  have hpow : 7^(Nat.log 7 (2^e)*14) ≤ 7^(5*e) := calc
    _ = (7^Nat.log 7 (2^e))^14 := pow_mul _ _ _
    _ ≤ (2^e)^14 := Nat.pow_le_pow_left hp _
    _ = (2^14)^e := by rw [← pow_mul,← pow_mul,Nat.mul_comm e]
    _ ≤ (7^5)^e := Nat.pow_le_pow_left (by decide) _
    _ = _ := (pow_mul _ _ _).symm
  have h := (Nat.pow_le_pow_iff_right (by decide : 1 < 7)).mp hpow
  omega

private theorem dyadic_cutoff_aux {k n : ℕ} (hk : k = 1 ∨ k = 2) (hn : 1 ≤ n) :
    let h := 2^(3*7^n-k)
    sparseDiskRootBound 7 h 1 (by change 0 < 2^_; positivity) (by norm_num) = h-1 := by
  let P := 7^n
  let h := 2^(3*P-k)
  have hP : 7 ≤ P := by simpa [P] using Nat.pow_le_pow_right (by decide : 0 < 7) hn
  have hk' : k ≤ 3*P := by omega
  have hmul : 2^k*h = 8^P := by
    dsimp [h]
    rw [← pow_add,Nat.add_sub_of_le hk',pow_mul]
    rfl
  apply seven_inverse_full_cutoff (c := 2^k) (m := n+1)
  · rcases hk with rfl | rfl <;> decide
  · rcases hk with rfl | rfl <;> decide
  · change 2^k*h ≡ 1 [MOD 7^(n+1)]
    rw [hmul]
    exact eight_pow_seven_pow_modEq_one n
  · change 6*(Nat.log 7 (2^(3*P-k))+1) < 7^(n+1)
    rw [pow_succ, mul_comm (7^n)]
    exact dyadic_log_bound hP (by omega)

/-- First family, with degree 2 raised to the power 3·7ⁿ−2, for every n. -/
theorem first_dyadic_full_cutoff (n : ℕ) :
    let h := 2^(3*7^n-2)
    sparseDiskRootBound 7 h 1 (by change 0 < 2^_; positivity) (by norm_num) = h-1 := by
  cases n with
  | zero =>
    change sparseDiskRootBound 7 2 1 (by decide) (by norm_num) = 1
    apply (sparseDiskRootBound_one_eq_pred_iff_short_intervals (by decide) (by decide)
      (by norm_num)).mpr
    intro u d hu hd hlen
    have hd₁ : d ≤ 1 := by
      change 5*d ≤ 6*(Nat.log 7 2+1) at hlen
      rw [show Nat.log 7 2 = 0 by decide] at hlen
      omega
    interval_cases u <;> interval_cases d <;> first | omega | norm_num [Finset.sum_range_one, padicValNat.eq_zero_of_not_dvd (by decide : ¬7 ∣ 2)]
  | succ n => exact dyadic_cutoff_aux (n := n+1) (Or.inr rfl) (by omega)

/-- Second family, with degree 2 raised to the power 3·7ⁿ−1, for n ≥ 1. -/
theorem second_dyadic_full_cutoff (n : ℕ) (hn : 1 ≤ n) :
    let h := 2^(3*7^n-1)
    sparseDiskRootBound 7 h 1 (by change 0 < 2^_; positivity) (by norm_num) = h-1 :=
  dyadic_cutoff_aux (Or.inl rfl) hn

/-- Every integral element of either stated degree with all its conjugates
in a single depth-one disk at seven has maximal minimum support. -/
theorem dyadic_degree_minimumSupport_eq_full
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra K ℂ_[7]] {x : L}
    (hx : IsIntegral K x)
    (hdeg : (∃ n : ℕ, (minpoly K x).natDegree = 2^(3*7^n-2)) ∨
      (∃ n : ℕ, 1 ≤ n ∧ (minpoly K x).natDegree = 2^(3*7^n-1)))
    (a : ℂ_[7]) (ha : a ≠ 0) (σ : Fin (minpoly K x).natDegree → L →ₐ[K] ℂ_[7])
    (hinj : Function.Injective fun i ↦ σ i x) (hdisk : ∀ i, ‖σ i x/a-1‖ ≤ (7:ℝ)⁻¹) :
    minimumSupport hx = (minpoly K x).natDegree+1 := by
  apply minimumSupport_eq_degree_add_one_of_intervalSums (b := 1) hx (by norm_num) a ha σ hinj
    (by simpa [Real.rpow_neg_one] using hdisk)
  apply (sparseDiskRootBound_eq_pred_iff_intervals (minpoly.natDegree_pos hx) (by norm_num)).mp
  have transfer {d h : ℕ} (hd : 0 < d) (hh : 0 < h) (he : d = h)
      (H : sparseDiskRootBound 7 h 1 hh (by norm_num) = h-1) :
      sparseDiskRootBound 7 d 1 hd (by norm_num) = d-1 := by
    subst h
    exact H
  rcases hdeg with ⟨n,hn⟩ | ⟨n,hn,he⟩
  · exact transfer _ _ hn (first_dyadic_full_cutoff n)
  · exact transfer _ _ he (second_dyadic_full_cutoff n hn)

end GRHArticle.SingularModuli

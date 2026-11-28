import GRHArticle.SingularModuli.FullSupportIntervals
import Mathlib.Data.Nat.ModEq

/-!
# Short valuation intervals about inverses modulo powers of seven

For multipliers from two through four a short one-sided interval about
the modular inverse embeds, as far as its valuation sum is concerned, in
an ordinary factorial of less than six times its length.
-/

namespace GRHArticle.SingularModuli

local instance primeSevenForReciprocalIntervals : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem sum_range_valuations_eq_factorial (N : ℕ) :
    (∑ i ∈ Finset.range (N+1), padicValNat 7 i) = padicValNat 7 N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)]
    exact Nat.add_comm _ _

private theorem sum_valuations_le_factorial_of_injection {r N : ℕ} (f g : ℕ → ℕ)
    (hval : ∀ i < r, padicValNat 7 (f i) ≤ padicValNat 7 (g i))
    (hbound : ∀ i < r, g i ≤ N) (hinj : Set.InjOn g ↑(Finset.range r)) :
    (∑ i ∈ Finset.range r, padicValNat 7 (f i)) ≤ padicValNat 7 N.factorial := by
  refine (Finset.sum_le_sum fun i hi ↦ hval i (Finset.mem_range.mp hi)).trans ?_
  rw [← Finset.sum_image hinj, ← sum_range_valuations_eq_factorial]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (by intros; exact Nat.zero_le _)
  intro i hi
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound j (Finset.mem_range.mp hj)))

private theorem valuation_le_of_transferred_divisors {x y m : ℕ} (hy : 0 < y) (hM : y < 7^m)
    (hdiv : ∀ d : ℕ, d ∣ 7^m → d ∣ x → d ∣ y) : padicValNat 7 x ≤ padicValNat 7 y := by
  let v := padicValNat 7 y
  have hvm : v < m := by
    have h := Nat.le_of_dvd hy (pow_padicValNat_dvd (p := 7) (n := y))
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 7)).mp (h.trans_lt hM)
  by_contra! h
  exact pow_succ_padicValNat_not_dvd hy.ne' (hdiv (7^(v+1))
    (pow_dvd_pow 7 hvm) ((pow_dvd_pow 7 h).trans pow_padicValNat_dvd))

private theorem seven_factorial_valuation_lt {c r : ℕ} (hc : c ≤ 4) (hr : 0 < r) :
    padicValNat 7 (c*r+1).factorial < r := by
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero 7 (Nat.succ_ne_zero (c*r))
  have hc' := Nat.mul_le_mul_right r hc
  norm_num at h
  omega

/-- The interval immediately after a modular inverse satisfies the strict
depth-one test for each multiplier between two and four. -/
theorem seven_inverse_right_short {c h r m : ℕ} (hc₀ : 2 ≤ c) (hc₁ : c ≤ 4)
    (hr : 0 < r) (hc : c*h ≡ 1 [MOD 7^m]) (hM : c*r+1 < 7^m) :
    (∑ i ∈ Finset.range r, padicValNat 7 (h+i+1)) < r := by
  let g (i : ℕ) := 1+c*(i+1)
  apply lt_of_le_of_lt (sum_valuations_le_factorial_of_injection _ g ?_ ?_ ?_)
    (seven_factorial_valuation_lt hc₁ hr)
  · intro i hi
    have hm := Nat.mul_le_mul_left c (show i+1 ≤ r by omega)
    refine valuation_le_of_transferred_divisors (m := m) (by dsimp [g]; omega) (by dsimp [g]; omega) ?_
    intro d hd hx
    have he : c*(h+i+1) ≡ g i [MOD 7^m] := by
      simpa only [g, Nat.add_assoc, Nat.mul_add] using hc.add_right (c*(i+1))
    exact (he.dvd_iff hd).mp (hx.trans (dvd_mul_left _ _))
  · intro i hi
    dsimp [g]
    have := Nat.mul_le_mul_left c (show i+1 ≤ r by omega)
    omega
  · intro i _ j _ hij
    dsimp [g] at hij
    exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_left (by omega : 0 < c) (Nat.add_left_cancel hij))

/-- The interval ending at the modular inverse also satisfies the strict
test. The endpoint has valuation zero. -/
theorem seven_inverse_left_short {c h r m : ℕ} (hc₀ : 2 ≤ c) (hc₁ : c ≤ 4)
    (hr : 0 < r) (hrh : r ≤ h) (hc : c*h ≡ 1 [MOD 7^m]) (hM : c*r+1 < 7^m) :
    (∑ i ∈ Finset.range r, padicValNat 7 (h-r+i+1)) < r := by
  let g (i : ℕ) := c*(r-1-i)-1
  apply lt_of_le_of_lt (sum_valuations_le_factorial_of_injection _ g ?_ ?_ ?_)
    (seven_factorial_valuation_lt hc₁ hr)
  · intro i hi
    let x := h-r+i+1
    change padicValNat 7 x ≤ padicValNat 7 (g i)
    by_cases hi' : i+1 = r
    · have hx : x = h := by dsimp [x]; omega
      have hz : padicValNat 7 h ≤ padicValNat 7 1 := by
        refine valuation_le_of_transferred_divisors (m := m) (by decide) (by omega) ?_
        intro d hd hdiv
        exact (hc.dvd_iff hd).mp (hdiv.trans (dvd_mul_left _ _))
      simpa [hx] using (hz.trans (by simp))
    · have hdist : 0 < r-1-i := by omega
      have htop := Nat.mul_le_mul_left c (show r-1-i ≤ r by omega)
      have hbot := Nat.mul_le_mul_left c hdist
      have hg : 0 < g i := by dsimp [g]; interval_cases c <;> omega
      refine valuation_le_of_transferred_divisors (m := m) hg (by dsimp [g]; omega) ?_
      intro d hd hx
      have hsum : c*x + g i + 1 = c*h := by
        dsimp [x,g]
        interval_cases c <;> omega
      have ht : c*x+g i ≡ 0 [MOD 7^m] := by
        apply Nat.ModEq.add_right_cancel' 1
        simpa only [hsum,zero_add] using hc
      have hsumdiv := (ht.dvd_iff hd).mpr (dvd_zero d)
      exact (Nat.dvd_add_iff_right (hx.trans (dvd_mul_left _ _))).mpr hsumdiv
  · intro i _
    dsimp [g]
    have := Nat.mul_le_mul_left c (show r-1-i ≤ r by omega)
    omega
  · intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    dsimp [g] at hij
    interval_cases c <;> omega

end GRHArticle.SingularModuli

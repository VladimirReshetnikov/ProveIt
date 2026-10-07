import OAI.Combinatorics.Progressions.Estimates.BoundedSubmoduleIntersection

namespace OAI

section

namespace Erdos3

open Module

theorem rational_height_count_le_cube (H : ℕ) : (2 * H + 1) * (H + 1) ≤ (H + 1) ^ 3 := by
  have h : 2 * H + 1 ≤ (H + 1) ^ 2 := by nlinarith
  calc
    _ ≤ (H + 1) ^ 2 * (H + 1) := Nat.mul_le_mul_right _ h
    _ = _ := by ring

theorem rational_height_count_exp_bound (H N : ℕ) {A : ℝ}
    (hA : 0 ≤ A) (hH : (H : ℝ) ≤ Real.exp A) :
    ((((2 * H + 1) * (H + 1)) ^ N : ℕ) : ℝ) ≤ Real.exp (3 * N * (A + 1)) := by
  have h1 : 1 ≤ Real.exp A := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hA
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hH1 : (H : ℝ) + 1 ≤ Real.exp (A + 1) := by
    calc
      _ ≤ Real.exp A + Real.exp A := add_le_add hH h1
      _ = 2 * Real.exp A := by ring
      _ ≤ Real.exp 1 * Real.exp A := mul_le_mul_of_nonneg_right htwo (Real.exp_pos A).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hcount : (((2 * H + 1) * (H + 1) : ℕ) : ℝ) ≤ Real.exp (3 * (A + 1)) := by
    calc
      _ ≤ ((H + 1 : ℕ) : ℝ) ^ 3 := by exact_mod_cast rational_height_count_le_cube H
      _ ≤ Real.exp (A + 1) ^ 3 := by
        apply pow_le_pow_left₀ (by positivity)
        simpa only [Nat.cast_add, Nat.cast_one] using hH1
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  rw [Nat.cast_pow]
  calc
    _ ≤ Real.exp (3 * (A + 1)) ^ N := pow_le_pow_left₀ (by positivity) hcount N
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem rational_log_height_count_exp_bound (N : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ((((2 * ⌈Real.exp A⌉₊ + 1) * (⌈Real.exp A⌉₊ + 1)) ^ N : ℕ) : ℝ) ≤
      Real.exp (3 * N * (A + 2)) := by
  have he := rational_height_count_exp_bound ⌈Real.exp A⌉₊ N
    (A := A + 1) (by linarith) (ceil_exp_le_exp_add_one hA)
  convert he using 1
  congr 1
  ring

theorem heightBoundedLieSubalgebras_ncard_exp_bound
    {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (m : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ((heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊).ncard : ℝ) ≤
      Real.exp (3 * (m : ℝ) * Fintype.card ι * (A + 2)) := by
  have hc := (finite_card_heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊).2
  have he := rational_log_height_count_exp_bound (m * Fintype.card ι) hA
  have hr := (Nat.cast_le.mpr hc).trans he
  simpa only [Nat.cast_mul, mul_assoc] using hr

end Erdos3

end

section

namespace Erdos3

theorem rationalConstraint_base_count_le_exp (m n d : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) :
    ((m * (n + 1) * (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d)) : ℕ) : ℝ) ≤
      Real.exp (2 * p + 3 * p ^ 2 * (p + 2)) := by
  have hpower := rational_log_height_count_exp_bound (n * d) hp
  have hnd : (n : ℝ) * d ≤ p ^ 2 := by
    simpa only [pow_two] using mul_le_mul hn hd (Nat.cast_nonneg d) hp
  have hpower' :
      (((((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d)) : ℕ) : ℝ) ≤
        Real.exp (3 * p ^ 2 * (p + 2)) := by
    apply hpower.trans (Real.exp_le_exp.mpr _)
    rw [Nat.cast_mul]
    nlinarith [mul_le_mul_of_nonneg_right hnd (show 0 ≤ 3 * (p + 2) by positivity)]
  have hmexp : (m : ℝ) ≤ Real.exp p := hm.trans (by linarith [Real.add_one_le_exp p])
  have hnexp : ((n + 1 : ℕ) : ℝ) ≤ Real.exp p := by
    rw [Nat.cast_add, Nat.cast_one]
    exact (add_le_add hn (le_refl 1)).trans (Real.add_one_le_exp p)
  calc
    _ ≤ Real.exp p * Real.exp p * Real.exp (3 * p ^ 2 * (p + 2)) := by
      rw [Nat.cast_mul, Nat.cast_mul]
      exact mul_le_mul (mul_le_mul hmexp hnexp (by positivity) (Real.exp_nonneg _))
        hpower' (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem rationalConstraint_list_count_le_exp (m n d N : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (n : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hN : (N : ℝ) ≤ p) :
    (((m * (n + 1) * (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d)) + 1) ^
      (N + 1) : ℕ) : ℝ) ≤ Real.exp ((p + 8) ^ 8) := by
  let M := m * (n + 1) * (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d))
  let F := 2 * p + 3 * p ^ 2 * (p + 2)
  have hM : (M : ℝ) ≤ Real.exp F := rationalConstraint_base_count_le_exp m n d hp hm hn hd
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have h1 : 1 ≤ Real.exp F := Real.one_le_exp hF
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hM1 : ((M + 1 : ℕ) : ℝ) ≤ Real.exp (F + 1) := by
    calc
      _ ≤ 2 * Real.exp F := by push_cast; linarith
      _ ≤ Real.exp 1 * Real.exp F := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hpoly : F + 1 ≤ (p + 8) ^ 4 := by
    dsimp only [F]
    nlinarith [pow_nonneg hp 3, pow_nonneg hp 4]
  have hN1 : ((N + 1 : ℕ) : ℝ) ≤ p + 8 := by push_cast; linarith
  have ht : 1 ≤ p + 8 := by linarith
  change (((M + 1) ^ (N + 1) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (F + 1)) ^ (N + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM1 _
    _ = Real.exp (((N + 1 : ℕ) : ℝ) * (F + 1)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((p + 8) ^ 5) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ (p + 8) * (p + 8) ^ 4 := mul_le_mul hN1 hpoly (by positivity) (by positivity)
        _ = _ := by ring
    _ ≤ _ := Real.exp_le_exp.mpr (pow_le_pow_right₀ ht (by norm_num))

theorem rationalConstraint_list_count_le_exp_of_le (M m n d N : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (n : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hN : (N : ℝ) ≤ p)
    (hM : M ≤ m * (n + 1) *
      (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d))) :
    (((M + 1) ^ (N + 1) : ℕ) : ℝ) ≤ Real.exp ((p + 8) ^ 8) := by
  apply le_trans _ (rationalConstraint_list_count_le_exp m n d N hp hm hn hd hN)
  exact_mod_cast Nat.pow_le_pow_left (Nat.add_le_add_right hM 1) (N + 1)

theorem rationalConstraint_floor_list_count_le_exp (m d N : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) (hN : (N : ℝ) ≤ p) :
    (((m * (⌊p⌋₊ + 1) * (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (⌊p⌋₊ * d)) + 1) ^
      (N + 1) : ℕ) : ℝ) ≤ Real.exp ((p + 8) ^ 8) :=
  rationalConstraint_list_count_le_exp m ⌊p⌋₊ d N hp hm (Nat.floor_le hp) hd hN

end Erdos3

end

end OAI

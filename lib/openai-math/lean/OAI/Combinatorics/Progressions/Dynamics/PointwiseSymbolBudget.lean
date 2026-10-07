import OAI.Combinatorics.Progressions.Polynomial.RankPolynomialFactorization

namespace OAI

section

namespace Erdos3

theorem shift_le_power_succ {p : ℝ} (hp : 0 ≤ p) (C : ℕ) :
    p + C ≤ (p + 2) ^ (C + 1) := by
  induction C with
  | zero => simp only [Nat.cast_zero, add_zero, zero_add, pow_one]; linarith
  | succ C ih =>
    have hpow : 1 ≤ (p + 2) ^ (C + 1) := one_le_pow₀ (by linarith)
    calc
      p + (C + 1 : ℕ) ≤ (p + 2) ^ (C + 1) + 1 := by push_cast; linarith
      _ ≤ (p + 2) ^ (C + 1) * (p + 2) := by nlinarith
      _ = (p + 2) ^ (C + 1 + 1) := (pow_succ _ _).symm

theorem shifted_self_power_le_base_power {p : ℝ} (hp : 0 ≤ p) (C : ℕ) :
    (p + C) ^ C ≤ (p + 2) ^ ((C + 1) * C) := by
  calc
    _ ≤ ((p + 2) ^ (C + 1)) ^ C := pow_le_pow_left₀ (by positivity) (shift_le_power_succ hp C) C
    _ = _ := (pow_mul _ _ _).symm

theorem exists_symbol_extension_budget (a c₀ c₁ c₂ c₃ c₄ : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q₁ := (p + c₀) ^ c₀ + (p + 2) ^ a + p + 2
      let q₂ := (q₁ + c₁) ^ c₁ + (q₁ + c₂) ^ c₂ + q₁ + 2
      let q₃ := (q₂ + c₃) ^ c₃ + q₂ + 2
      (p + c₀) ^ c₀ + (q₂ + c₃) ^ c₃ + (q₃ + c₄) ^ c₄ ≤ (p + 2) ^ C := by
  let Q₁ : Polynomial ℕ := (Polynomial.X + Polynomial.C c₀) ^ c₀ +
    (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let Q₂ : Polynomial ℕ := (Q₁ + Polynomial.C c₁) ^ c₁ + (Q₁ + Polynomial.C c₂) ^ c₂ + Q₁ + 2
  let Q₃ : Polynomial ℕ := (Q₂ + Polynomial.C c₃) ^ c₃ + Q₂ + 2
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C c₀) ^ c₀ +
    (Q₂ + Polynomial.C c₃) ^ c₃ + (Q₃ + Polynomial.C c₄) ^ c₄
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨(C + 1) * C, by nlinarith, ?_⟩
  intro p hp
  apply le_trans _ (shifted_self_power_le_base_power hp C)
  simpa [B, Q₁, Q₂, Q₃, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

section

namespace Erdos3

theorem symbol_spanning_count_bound (s d m k : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hk : (k : ℝ) ≤ p) :
    ((d * (s + 1) * (m + 1) ^ s * k : ℕ) : ℝ) ≤ (p + (s + 3)) ^ (s + 3) := by
  have hdim := NilpotentLieFiltration.symbol_dimension_bound_le_power s d m hp hd hm
  have hbase : p + (s + 2 : ℝ) ≤ p + (s + 3 : ℝ) := by linarith
  have hdim' : ((d * (s + 1) * (m + 1) ^ s : ℕ) : ℝ) ≤
      (p + (s + 3)) ^ (s + 2) :=
    hdim.trans (pow_le_pow_left₀ (by positivity) hbase _)
  rw [Nat.cast_mul]
  calc
    _ ≤ (p + (s + 3)) ^ (s + 2) * (p + (s + 3)) :=
      mul_le_mul hdim' (hk.trans (le_add_of_nonneg_right (by positivity))) (by positivity) (by positivity)
    _ = (p + (s + 3)) ^ (s + 3) := (pow_succ (p + (s + 3)) (s + 2)).symm

theorem symbol_spanning_parameter_ge (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ (p + (s + 3)) ^ (s + 3) := by
  apply (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ s + 3)).trans
  simpa only [pow_one] using pow_le_pow_right₀
    (by have := Nat.cast_nonneg (α := ℝ) s; linarith : (1 : ℝ) ≤ p + (s + 3))
    (by omega : 1 ≤ s + 3)

theorem symbol_spanning_parameter_power_bound (s k : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ((p + (s + 3)) ^ (s + 3) + 2) ^ k ≤
      (p + 2) ^ (((s + 4) * (s + 3) + 2) * k) := by
  apply polynomial_budget_comp hp (by positivity) ((s + 4) * (s + 3)) k _ le_rfl
  simpa only [Nat.cast_add, Nat.cast_ofNat] using shifted_self_power_le_base_power hp (s + 3)

theorem symbol_spanning_shifted_parameter_power_bound (s k : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ((p + (s + 3)) ^ (s + 3) + k) ^ k ≤
      (p + 2) ^ (((s + 4) * (s + 3) + 2) * ((k + 1) * k)) :=
  (shifted_self_power_le_base_power (by positivity : 0 ≤ (p + (s + 3)) ^ (s + 3)) k).trans
    (symbol_spanning_parameter_power_bound s ((k + 1) * k) hp)

end Erdos3

end

end OAI

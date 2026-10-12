import GowersSzemeredi.Proofs16IntegerTightCovers

/-! The polynomial integer cover recovers, and improves by one in the
innermost shift, the original common exponent in Corollary 16.11. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem classV_bound_all (Kc pc : Nat → Nat)
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) (k : Nat) :
    2 * classV Kc pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1) := by
  set E := (2 : Nat) ^ ((2 : Nat) ^ (k + 4)) with hE
  have hterm : ∀ j ∈ Finset.range k, (Kc j : Real) + pc j ≤ 2 ^ E := by
    intro j hj
    have hjk : j + 5 ≤ k + 4 := by have := Finset.mem_range.mp hj; omega
    refine (hconst j).trans (pow_le_pow_right₀ (by norm_num) ?_)
    exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hjk)
  have hsum : ∑ j ∈ Finset.range k, ((Kc j : Real) + pc j) ≤ k * 2 ^ E := by
    have := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hk2 : (2 : Real) * (k + 1) ≤ 2 ^ (k + 2) := by
    have h : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
    have h' : ((k + 1 : Nat) : Real) < ((2 ^ (k + 1) : Nat) : Real) := by exact_mod_cast h
    push_cast at h'
    rw [pow_succ]; linarith
  have hE1 : (1 : Real) ≤ 2 ^ E := one_le_pow₀ (by norm_num)
  have hstep : 2 * classV Kc pc k ≤ 2 ^ (E + k + 2) := by
    unfold classV
    rw [show E + k + 2 = E + (k + 2) by ring, pow_add]
    have hk0 : (0 : Real) ≤ k := Nat.cast_nonneg _
    nlinarith
  refine hstep.trans (pow_le_pow_right₀ (by norm_num) ?_)
  have hEk : E + k + 3 ≤ (2 : Nat) ^ ((2 : Nat) ^ (k + 6)) := by
    have h4 : (2 : Nat) ^ (k + 6) = 2 ^ (k + 4) * 4 := by
      rw [show k + 6 = (k + 4) + 2 by omega, pow_add]; norm_num
    have hE4 : (2 : Nat) ^ ((2 : Nat) ^ (k + 6)) = E ^ 4 := by rw [h4, pow_mul]
    have hEk' : k + 4 < E := lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by norm_num) (Nat.lt_two_pow_self (n := k + 4)).le)
    rw [hE4]
    have hE2 : 2 ≤ E := by omega
    nlinarith [Nat.mul_le_mul hE2 hE2]
  omega

private theorem corollary_degree_budget (k : Nat) :
    ((2 : Nat) ^ (2 ^ (k + 6)) + 8) * uDeg68 k + 3 ≤ 2 ^ (2 ^ (k + 8)) := by
  have hE : 1 ≤ (2 : Nat) ^ k := Nat.one_le_two_pow
  have hB : 8 ≤ (2 : Nat) ^ (64 * 2 ^ k) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (64 * 2 ^ k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hD : 1 ≤ (2 : Nat) ^ (68 * 2 ^ k) := Nat.one_le_two_pow
  have hmul : (2 : Nat) ^ (64 * 2 ^ k) * 2 ^ (68 * 2 ^ k) = 2 ^ (132 * 2 ^ k) := by
    rw [← pow_add]; congr 1; omega
  have hbig : 4 * (2 : Nat) ^ (132 * 2 ^ k) ≤ 2 ^ (256 * 2 ^ k) := by
    calc 4 * (2 : Nat) ^ (132 * 2 ^ k) = 2 ^ (132 * 2 ^ k + 2) := by rw [pow_add]; ring
      _ ≤ 2 ^ (256 * 2 ^ k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h6 : (2 : Nat) ^ (k + 6) = 64 * 2 ^ k := by rw [pow_add]; ring
  have h8 : (2 : Nat) ^ (k + 8) = 256 * 2 ^ k := by rw [pow_add]; ring
  rw [h6, h8, uDeg68]
  nlinarith

/-- A common exponent with shift `k+8`, stronger than the source's `k+9`,
is below both the graph density and the width exponent of the integer cover. -/
theorem corollary_16_11_polynomial_bounds {V alpha : Real} (hV : 1 ≤ V)
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) (k : Nat)
    (hVb : V ≤ (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)))) :
    (alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8))) ≤
      (alpha / 8) / uCount V (uDeg68 k) (alpha / 2) (alpha / 4) (alpha / 8) ∧
    (alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8))) ≤
      uExp V (uDeg68 k) (alpha / 2) (alpha / 4) (alpha / 8) := by
  let X : Real := 2 / alpha
  let B : Nat := 2 ^ (2 ^ (k + 6))
  let D : Nat := uDeg68 k
  let Q : Real := uCount V D (alpha / 2) (alpha / 4) (alpha / 8)
  have hX : 2 ≤ X := by dsimp [X]; apply (le_div_iff₀ ha).mpr; linarith
  have hX0 : 0 < X := by linarith
  have hQ1 : 1 ≤ Q := one_le_uCount _ _ _ _ _
  have hQ0 : 0 < Q := by linarith
  have hVX : V ≤ X ^ B := hVb.trans (pow_le_pow_left₀ (by norm_num) hX B)
  have h32 : (32 : Real) ≤ X ^ 5 := by
    calc 32 = (2 : Real) ^ 5 := by norm_num
      _ ≤ X ^ 5 := pow_le_pow_left₀ (by norm_num) hX 5
  have hbase : uniformBase V 1 (alpha / 4) (alpha / 2) (alpha / 8) = 32 * V * X ^ 3 := by
    dsimp [uniformBase, X]
    push_cast
    field_simp [ha.ne', hQ0.ne']
    ring
  have hQbound : Q ≤ X ^ ((B + 8) * D) := by
    dsimp [Q]
    rw [uCount_eq hV D (by positivity) (by linarith) (by positivity) (by linarith)
      (by positivity) (by linarith), hbase, pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    calc 32 * V * X ^ 3 ≤ (X ^ 5 * X ^ B) * X ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul h32 hVX (by linarith) (by positivity)) (by positivity)
      _ = X ^ (B + 8) := by rw [← pow_add, ← pow_add]; congr 1; omega
  have h4 : 4 ≤ X ^ 2 := by nlinarith
  have hden : 4 * X * Q ≤ X ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8))) := by
    calc 4 * X * Q ≤ (X ^ 2 * X) * X ^ ((B + 8) * D) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h4 hX0.le) hQbound hQ0.le (by positivity)
      _ = X ^ ((B + 8) * D + 3) := by rw [← pow_succ, ← pow_add]; congr 1; omega
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (corollary_degree_budget k)
  have heq : alpha / 2 = X⁻¹ := by dsimp [X]; field_simp [ha.ne']
  have hdensity : alpha / 8 / Q = (4 * X * Q)⁻¹ := by
    dsimp [X]
    field_simp [ha.ne', hQ0.ne']
    ring
  have hsmall : (alpha / 2) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8))) ≤ alpha / 8 / Q := by
    rw [heq, inv_pow, hdensity]
    exact inv_anti₀ (by positivity) hden
  refine ⟨hsmall, hsmall.trans ?_⟩
  change alpha / 8 / Q ≤ Q⁻¹
  rw [div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.mpr hQ0.le) (by linarith)

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs16VarietyControlAbsorption

/-! The variety route's piece parameter fits the dimension-three budget.

`MultiplyLinearWith.multiplyLinear_of_variety_shape` produces pieces that are
`MultiplyLinear γ s` with `s = 18r/γ + 64 + L`. Here `r` is the Lemma 16.9 scale
`section16Lemma9R (θ/2) γ 2` and `L` bounds the logarithmic losses.
`Section16BudgetedPieceAt 3` asks for `s ≤ η·s(θ,γ,3)` with the variety piece
mass `η = θ₂(θ₁(θ/2,γ,2))`.

With `x = 2/(θγ) ≥ 2` every quantity is a power of `x`:
* `18r/γ ≤ x^(6·2^256 + 9)`, since `r = 3γ⁻²(32x)^(2^256)`;
* `η⁻¹ ≤ x^(32 + 24·2^128)`;
* `s(θ,γ,3) = x^(2^512)`.

So `variety_piece_budget` holds for every `L ≤ x^(64·2^256)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The Lemma 16.9 scale of the dimension-three lift, in terms of `x = 2/(θγ)`.
No tactic here normalizes the huge powers: `(32·x)^(2^256)` must not be
expanded into `32^(2^256)·x^(2^256)`. -/
theorem section16Lemma9R_half_two_eq {theta gamma : Real} (ht : 0 < theta) (hg : 0 < gamma) :
    section16Lemma9R (theta / 2) gamma 2 =
      3 * (gamma⁻¹) ^ 2 * (32 * (2 / (theta * gamma))) ^ ((2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) := by
  unfold section16Lemma9R multipleS
  have h16 : (2 : Real) ^ (-(((2 : Nat) : Real) + 2)) = 1 / 16 := by
    rw [show (-(((2 : Nat) : Real) + 2)) = -((4 : Nat) : Real) by norm_num,
      Real.rpow_neg (by norm_num), Real.rpow_natCast]
    norm_num
  have hbase : 2 / (1 / 16 * (theta / 2) * gamma) = 32 * (2 / (theta * gamma)) := by
    field_simp; ring
  have h3 : (((2 : Nat) ^ 2 - 1 : Nat) : Real) = 3 := by norm_num
  rw [h16, hbase, h3, zpow_neg, zpow_ofNat, inv_pow]

/-- The variety piece mass, in terms of `x = 2/(θγ)`. -/
theorem section16VarietyPieceMassThree_eq {theta gamma : Real} (ht : 0 < theta) (hg : 0 < gamma) :
    section16ThetaTwo (section16ThetaOne (theta / 2) gamma 2) =
      ((2 : Real) ^ 32 * (4 * (2 / (theta * gamma))) ^ (8 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 5))))⁻¹ := by
  unfold section16ThetaTwo section16ThetaOne
  have hbase : theta / 2 * gamma / 4 = (4 * (2 / (theta * gamma)))⁻¹ := by
    field_simp
  have h32 : (2 : Real) ^ (-(32 : Real)) = ((2 : Real) ^ 32)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), show ((32 : Real)) = ((32 : Nat) : Real) by norm_num,
      Real.rpow_natCast]
  rw [hbase, h32, inv_pow, inv_pow, ← pow_mul, mul_inv,
    Nat.mul_comm ((2 : Nat) ^ ((2 : Nat) ^ (2 + 5))) 8]

/-- The budget comparison with the exponents as variables, so that no tactic
meets a huge numeral power. -/
theorem variety_budget_core {x gamma L : Real} {E1 E2 E3 F : Nat} (hx2 : 2 ≤ x) (hg : 0 < gamma)
    (hginv : gamma⁻¹ ≤ x) (hL : L ≤ x ^ F) (hE2 : 6 * E2 + 9 ≤ F) (hF : 6 ≤ F)
    (hE3 : F + 2 + (32 + 24 * E1) ≤ E3) :
    18 * (3 * gamma⁻¹ ^ 2 * (32 * x) ^ E2) / gamma + 64 + L ≤
      ((2 : Real) ^ 32 * (4 * x) ^ (8 * E1))⁻¹ * x ^ E3 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hp : ∀ m n : Nat, m ≤ n → x ^ m ≤ x ^ n := fun m n h => pow_le_pow_right₀ hx1 h
  have h6 : (64 : Real) ≤ x ^ 6 := by
    calc (64 : Real) = 2 ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) hx2 6
  have h5 : (32 : Real) ≤ x ^ 5 := by
    calc (32 : Real) = 2 ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) hx2 5
  have h2 : (4 : Real) ≤ x ^ 2 := by nlinarith
  -- the scale term
  have h32x : 32 * x ≤ x ^ 6 := by
    calc 32 * x ≤ x ^ 5 * x := mul_le_mul_of_nonneg_right h5 hx0.le
      _ = x ^ 6 := by ring
  have hr : 18 * (3 * gamma⁻¹ ^ 2 * (32 * x) ^ E2) / gamma ≤ x ^ (6 * E2 + 9) := by
    have h32 : (32 * x) ^ E2 ≤ (x ^ 6) ^ E2 := pow_le_pow_left₀ (by positivity) h32x E2
    have hg2 : gamma⁻¹ ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hginv 2
    have hg3 : gamma⁻¹ ^ 2 * gamma⁻¹ ≤ x ^ 2 * x :=
      mul_le_mul hg2 hginv (by positivity) (by positivity)
    calc 18 * (3 * gamma⁻¹ ^ 2 * (32 * x) ^ E2) / gamma
        = 54 * (gamma⁻¹ ^ 2 * gamma⁻¹) * (32 * x) ^ E2 := by rw [div_eq_mul_inv]; ring
      _ ≤ 54 * (x ^ 2 * x) * (x ^ 6) ^ E2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hg3 (by norm_num)) h32 (by positivity)
            (by positivity)
      _ ≤ x ^ 6 * (x ^ 2 * x) * (x ^ 6) ^ E2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = x ^ (6 * E2 + 9) := by rw [← pow_mul]; ring
  -- the mass term
  have h4x : 4 * x ≤ x ^ 3 := by
    calc 4 * x ≤ x ^ 2 * x := mul_le_mul_of_nonneg_right h2 hx0.le
      _ = x ^ 3 := by ring
  have hmass : (2 : Real) ^ 32 * (4 * x) ^ (8 * E1) ≤ x ^ (32 + 24 * E1) := by
    calc (2 : Real) ^ 32 * (4 * x) ^ (8 * E1) ≤ x ^ 32 * (x ^ 3) ^ (8 * E1) :=
          mul_le_mul (pow_le_pow_left₀ (by norm_num) hx2 32)
            (pow_le_pow_left₀ (by positivity) h4x _) (by positivity) (by positivity)
      _ = x ^ (32 + 24 * E1) := by rw [← pow_mul, ← pow_add]; congr 1; ring
  -- assemble
  have hA : 18 * (3 * gamma⁻¹ ^ 2 * (32 * x) ^ E2) / gamma ≤ x ^ F := hr.trans (hp _ _ hE2)
  have hB : (64 : Real) ≤ x ^ F := h6.trans (hp _ _ hF)
  generalize 18 * (3 * gamma⁻¹ ^ 2 * (32 * x) ^ E2) / gamma = T at hA ⊢
  have hsum : T + 64 + L ≤ x ^ (F + 2) := by
    have hxF : 0 ≤ x ^ F := by positivity
    calc T + 64 + L ≤ 3 * x ^ F := by linarith
      _ ≤ x ^ 2 * x ^ F := mul_le_mul_of_nonneg_right (by linarith) hxF
      _ = x ^ (F + 2) := by rw [← pow_add, add_comm]
  have hpos : 0 < (2 : Real) ^ 32 * (4 * x) ^ (8 * E1) := by positivity
  have hfinal : x ^ (F + 2) * ((2 : Real) ^ 32 * (4 * x) ^ (8 * E1)) ≤ x ^ E3 :=
    calc x ^ (F + 2) * ((2 : Real) ^ 32 * (4 * x) ^ (8 * E1))
        ≤ x ^ (F + 2) * x ^ (32 + 24 * E1) := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = x ^ (F + 2 + (32 + 24 * E1)) := by rw [← pow_add]
      _ ≤ x ^ E3 := hp _ _ hE3
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  exact (mul_le_mul_of_nonneg_right hsum hpos.le).trans hfinal

/-- **The variety piece parameter fits the dimension-three budget.** The losses
may be as large as `x^(64·2^256)`, `x = 2/(θγ)`. -/
theorem variety_piece_budget {theta gamma L : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hL : L ≤ (2 / (theta * gamma)) ^ (64 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6)))) :
    18 * section16Lemma9R (theta / 2) gamma 2 / gamma + 64 + L ≤
      section16ThetaTwo (section16ThetaOne (theta / 2) gamma 2) * multipleS theta gamma 3 := by
  rw [section16Lemma9R_half_two_eq ht hg, section16VarietyPieceMassThree_eq ht hg]
  unfold multipleS
  -- `hL` is cleared before arithmetic: `nlinarith` would fold its exponent to a
  -- literal and expand `(2/(θγ))^n`, overflowing `Nat.pow`.
  have hx2 : 2 ≤ 2 / (theta * gamma) := by
    clear hL
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_one₀ ht1 hg.le hg1]
  have hginv : gamma⁻¹ ≤ 2 / (theta * gamma) := by
    clear hL
    rw [inv_eq_one_div, div_le_div_iff₀ hg (by positivity)]
    nlinarith
  -- name the exponents and relate them without evaluating them
  have e3 : (2 : Nat) ^ ((2 : Nat) ^ (3 + 6)) =
      (2 : Nat) ^ ((2 : Nat) ^ (2 + 6)) * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6)) := by
    rw [← pow_add]; congr 1
  have e2 : (2 : Nat) ^ ((2 : Nat) ^ (2 + 6)) =
      (2 : Nat) ^ ((2 : Nat) ^ (2 + 5)) * (2 : Nat) ^ ((2 : Nat) ^ (2 + 5)) := by
    rw [← pow_add]; congr 1
  have e1 : 128 ≤ (2 : Nat) ^ ((2 : Nat) ^ (2 + 5)) :=
    calc 128 = (2 : Nat) ^ 7 := by norm_num
      _ ≤ (2 : Nat) ^ ((2 : Nat) ^ (2 + 5)) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.lt_two_pow_self).le
  generalize (2 : Nat) ^ ((2 : Nat) ^ (3 + 6)) = E3 at e3 ⊢
  generalize (2 : Nat) ^ ((2 : Nat) ^ (2 + 6)) = E2 at e3 e2 hL ⊢
  generalize (2 : Nat) ^ ((2 : Nat) ^ (2 + 5)) = E1 at e2 e1 ⊢
  subst e3 e2
  have hA : 128 * E1 ≤ E1 * E1 := Nat.mul_le_mul_right E1 e1
  have hB : 128 * (E1 * E1) ≤ E1 * E1 * (E1 * E1) :=
    Nat.mul_le_mul_right _ (e1.trans (Nat.le_mul_self E1))
  refine variety_budget_core hx2 hg hginv hL ?_ ?_ ?_
  · linarith
  · linarith
  · linarith

end LeanProofs.GowersSzemeredi

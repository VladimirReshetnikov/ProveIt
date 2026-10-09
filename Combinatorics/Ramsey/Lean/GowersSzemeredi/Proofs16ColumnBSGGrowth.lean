import GowersSzemeredi.Proofs16GlobalColumnBSG

/-! The BSG route starts from a density that is only singly exponential.

`global_column_bsg` and `global_column_word_system` take
`γ = globalColumnQuadrupleDensity α` as their only density input, and every
loss after it is polynomial in `γ` and `α`. This module bounds `γ` from
below. Write `d = columnSpectrumCap (columnEightDensity α)`.
* `columnEightDensity_ge`: `β = columnEightDensity α` is a fixed power of
  `α/2` times `2^(-1882)`.
* `globalColumnQuadrupleDensity_ge`:
  `2^(-30121)·(α/2)^74500 / 13^(4d) ≤ γ` for `0 < α ≤ 1`.

So `log(1/γ) ≤ 4d·log 13 + O(log(1/α))`, a polynomial in `1/α`, since
`d ≤ 16/β² + 1`. The model-elimination core instead guaranteed only
`exp(-2^(13^d)/2)` (`globalColumnAgreementDensity_le_triple_exp`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem columnEightDensity_ge {alpha : Real} (ha : 0 < alpha) :
    (2 : Real) ^ (-(1882 : Real)) * (alpha / 2) ^ 4656 ≤ columnEightDensity alpha := by
  unfold columnEightDensity
  rw [← pow_mul]

/-- **The BSG route's density is singly exponential.** -/
theorem globalColumnQuadrupleDensity_ge {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    (2 : Real) ^ (-(30121 : Real)) * (alpha / 2) ^ 74500 /
        (13 : Real) ^ (4 * columnSpectrumCap (columnEightDensity alpha)) ≤
      globalColumnQuadrupleDensity alpha := by
  set β := columnEightDensity alpha with hβdef
  set d := columnSpectrumCap β with hddef
  have hβ0 : 0 < β := columnEightDensity_pos ha
  have hβ := columnEightDensity_ge ha
  rw [← hβdef] at hβ
  have hr : alpha / 2 ≤ alpha / (2 - alpha) :=
    div_le_div_of_nonneg_left ha.le (by linarith) (by linarith)
  have h13 : (0 : Real) < 13 ^ d := by positivity
  -- the witness density
  have hw : columnWitnessDensity β = β ^ 4 / (4 * 13 ^ d) := rfl
  unfold globalColumnQuadrupleDensity
  rw [← hβdef, hw]
  -- monotonicity in `β` and in `α/(2-α)`
  have hβ4 : ((2 : Real) ^ (-(1882 : Real)) * (alpha / 2) ^ 4656) ^ 16 ≤ β ^ 16 :=
    pow_le_pow_left₀ (by positivity) hβ 16
  have hr4 : (alpha / 2) ^ 4 ≤ (alpha / (2 - alpha)) ^ 4 := pow_le_pow_left₀ (by positivity) hr 4
  have hlhs : (2 : Real) ^ (-(30121 : Real)) * (alpha / 2) ^ 74500 / (13 : Real) ^ (4 * d) =
      ((2 : Real) ^ (-(1882 : Real)) * (alpha / 2) ^ 4656) ^ 16 * (alpha / 2) ^ 4 /
        (512 * ((13 : Real) ^ d) ^ 4) := by
    have h2 : (2 : Real) ^ (-(30121 : Real)) = ((2 : Real) ^ (-(1882 : Real))) ^ 16 / 512 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [show (512 : Real) = (2 : Real) ^ (9 : Real) by norm_num, ← Real.rpow_sub (by norm_num)]
      norm_num
    rw [h2, ← pow_mul]
    field_simp
    ring
  rw [hlhs]
  have hrhs : (β ^ 4 / (4 * 13 ^ d)) ^ 4 * (alpha / (2 - alpha)) ^ 4 / 2 =
      β ^ 16 * (alpha / (2 - alpha)) ^ 4 / (512 * ((13 : Real) ^ d) ^ 4) := by
    field_simp
    ring
  rw [hrhs]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul hβ4 hr4 (by positivity) (by positivity)

/-- A refinement kernel radius is at least `(ρ/2)(ρ/5)^d (r/2)^(d+e)`. -/
theorem refinementKernelRadius_ge (d e : Nat) {ρ r : Real} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ρ / 2 * (ρ / 5) ^ d * (r / 2) ^ (d + e) ≤ refinementKernelRadius d e ρ r := by
  have hP : (denseLevelCells ρ : Real) ≤ 5 / ρ := by
    have h := (Nat.ceil_lt_add_one (by positivity : (0 : Real) ≤ 4 / ρ)).le
    have h1 : 4 / ρ + 1 ≤ 5 / ρ := by
      rw [div_add_one hρ.ne', div_le_div_iff_of_pos_right hρ]; linarith
    exact h.trans h1
  have hQ : (refinementCells r : Real) ≤ 2 / r := by
    have h := (Nat.ceil_lt_add_one (by positivity : (0 : Real) ≤ 1 / r)).le
    have h1 : 1 / r + 1 ≤ 2 / r := by
      rw [div_add_one hr.ne', div_le_div_iff_of_pos_right hr]; linarith
    exact h.trans h1
  have hP0 : (0 : Real) ≤ denseLevelCells ρ := by positivity
  have hQ0 : (0 : Real) ≤ refinementCells r := by positivity
  have hcap : (refinementKernelCap d e ρ r : Real) ≤ (5 / ρ) ^ d * (2 / r) ^ (d + e) := by
    unfold refinementKernelCap
    push_cast
    exact mul_le_mul (pow_le_pow_left₀ hP0 hP d) (pow_le_pow_left₀ hQ0 hQ (d + e))
      (by positivity) (by positivity)
  have hcpos : (0 : Real) < refinementKernelCap d e ρ r := by
    exact_mod_cast refinementKernelCap_pos d e hρ hr
  unfold refinementKernelRadius
  rw [le_div_iff₀ hcpos]
  calc ρ / 2 * (ρ / 5) ^ d * (r / 2) ^ (d + e) * (refinementKernelCap d e ρ r : Real)
      ≤ ρ / 2 * (ρ / 5) ^ d * (r / 2) ^ (d + e) * ((5 / ρ) ^ d * (2 / r) ^ (d + e)) :=
        mul_le_mul_of_nonneg_left hcap (by positivity)
    _ = ρ / 2 * ((ρ / 5) * (5 / ρ)) ^ d * ((r / 2) * (2 / r)) ^ (d + e) := by
        rw [mul_pow, mul_pow]; ring
    _ = ρ / 2 := by
        rw [show ρ / 5 * (5 / ρ) = 1 by field_simp, show r / 2 * (2 / r) = 1 by field_simp]
        simp

/-- **The zero-ladder radii are at most polynomially-exponentially small.**
With `u ≤ min(1/2, ρ₀/5, ρ₁)`, `ρ_n ≥ u^((16D+1)^n)`. -/
theorem zeroLadderRadius_ge {D : Nat} {ρ₀ ρ₁ u : Real} (h₀ : 0 < ρ₀) (h₀1 : ρ₀ ≤ 1)
    (h₁ : 0 < ρ₁) (h₁₀ : ρ₁ ≤ ρ₀) (hu : 0 < u) (hu2 : u ≤ 1 / 2) (hu₀ : u ≤ ρ₀ / 5)
    (hu₁ : u ≤ ρ₁) (n : Nat) :
    u ^ ((16 * D + 1) ^ n) ≤ zeroLadderRadius D ρ₀ ρ₁ n := by
  have hu1 : u ≤ 1 := by linarith
  induction n with
  | zero =>
    show u ^ ((16 * D + 1) ^ 0) ≤ ρ₁
    rw [pow_zero, pow_one]; exact hu₁
  | succ n ih =>
    obtain ⟨M, hM⟩ : ∃ M, (16 * D + 1) ^ n = M := ⟨_, rfl⟩
    rw [hM] at ih
    have hM1 : 1 ≤ M := by rw [← hM]; exact Nat.one_le_pow _ _ (by omega)
    have hρn := zeroLadderRadius_pos (D := D) h₀ h₁ n
    have hρn1 : zeroLadderRadius D ρ₀ ρ₁ n ≤ 1 := (zeroLadderRadius_le h₀ h₁ h₁₀ n).trans h₀1
    have hk := refinementKernelRadius_ge (4 * D) (2 * D) h₀ h₀1 hρn hρn1
    show u ^ ((16 * D + 1) ^ (n + 1)) ≤ refinementKernelRadius (4 * D) (2 * D) ρ₀ _
    refine le_trans ?_ hk
    have hA : u ≤ ρ₀ / 2 := by linarith
    have hB : u ^ (4 * D) ≤ (ρ₀ / 5) ^ (4 * D) := pow_le_pow_left₀ hu.le hu₀ _
    have hC : (u ^ M * u) ^ (4 * D + 2 * D) ≤ (zeroLadderRadius D ρ₀ ρ₁ n / 2) ^ (4 * D + 2 * D) := by
      apply pow_le_pow_left₀ (by positivity)
      have : u ^ M * u ≤ zeroLadderRadius D ρ₀ ρ₁ n * (1 / 2) :=
        mul_le_mul ih hu2 hu.le hρn.le
      linarith
    have hprod : u * u ^ (4 * D) * (u ^ M * u) ^ (4 * D + 2 * D) ≤
        ρ₀ / 2 * (ρ₀ / 5) ^ (4 * D) * (zeroLadderRadius D ρ₀ ρ₁ n / 2) ^ (4 * D + 2 * D) :=
      mul_le_mul (mul_le_mul hA hB (by positivity) (by positivity)) hC (by positivity)
        (by positivity)
    refine le_trans ?_ hprod
    have hexp : u * u ^ (4 * D) * (u ^ M * u) ^ (4 * D + 2 * D) =
        u ^ (1 + 4 * D + (M + 1) * (6 * D)) := by
      rw [(pow_succ u M).symm, show 4 * D + 2 * D = 6 * D by ring, ← pow_mul, ← pow_succ',
        ← pow_add]
      congr 1; ring
    rw [hexp, show (16 * D + 1) ^ (n + 1) = M * (16 * D + 1) by rw [pow_succ, hM]]
    apply pow_le_pow_of_le_one hu.le hu1
    nlinarith

end LeanProofs.GowersSzemeredi

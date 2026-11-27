import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# The analytic modular invariant and its first CM values

The invariant in the class-polynomial certificates is the quotient of the
cube of the normalized weight-four Eisenstein series by the discriminant.
-/

namespace GRHArticle.SingularModuli

open ModularForm UpperHalfPlane ModularGroup CongruenceSubgroup SlashInvariantForm
open scoped MatrixGroups Real

/-- The level-one modular invariant, normalized by its leading term `q⁻¹`. -/
noncomputable def modularInvariant (z : ℍ) : ℂ := E₄ z ^ 3 / ModularForm.discriminant z

private theorem transform_level_one {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
    [SlashInvariantFormClass F 𝒮ℒ k] (f : F) (g : SL(2, ℤ)) (z : ℍ) :
    f (g • z) = denom g z ^ k * f z :=
  slash_action_eqn'' (Γ := 𝒮ℒ) f (show (g : GL (Fin 2) ℝ) ∈ 𝒮ℒ from ⟨g, rfl⟩) z

theorem modularInvariant_smul (g : SL(2, ℤ)) (z : ℍ) :
    modularInvariant (g • z) = modularInvariant z := by
  have h₄ := transform_level_one E₄ g z
  have hΔ := transform_level_one CuspForm.discriminant g z
  change ModularForm.discriminant (g • z) = _ * ModularForm.discriminant z at hΔ
  rw [modularInvariant, h₄, hΔ, modularInvariant]
  simp only [zpow_ofNat, mul_pow, ← pow_mul]
  rw [show 4 * 3 = 12 by decide, mul_div_mul_left _ _ (pow_ne_zero _ (denom_ne_zero _ z))]

/-- The series and product evaluated in the article's class polynomial verifier. -/
theorem modularInvariant_qExpansion (z : ℍ) :
    let q := Function.Periodic.qParam 1 z
    modularInvariant z =
      (1 + 240 * ∑' n : ℕ+, (ArithmeticFunction.sigma 3 n : ℂ) * q ^ (n : ℕ)) ^ 3 /
      (q * ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24) := by
  intro q
  have h := EisensteinSeries.q_expansion_bernoulli (k := 4) (by decide) (by decide) z
  norm_num [bernoulli_eq_bernoulli'_of_ne_one (by decide : 4 ≠ 1), bernoulli'_four] at h
  rw [modularInvariant, ModularForm.discriminant_eq_q_prod]
  simp only [ModularForm.eta_q_eq_pow]
  dsimp [q, Function.Periodic.qParam]
  simp only [div_one]
  change ModularForm.E (k := 4) _ z = _ at h
  rw [show E₄ z = 1 + 240 * ∑' n : ℕ+, (ArithmeticFunction.sigma 3 n : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * z) ^ (n : ℕ) by linear_combination h]

private theorem eisenstein_six_at_i : E₆ UpperHalfPlane.I = 0 := by
  have h := transform_level_one E₆ S UpperHalfPlane.I
  have hs : S • UpperHalfPlane.I = UpperHalfPlane.I := stabilizer_I.mpr (by simp)
  rw [hs, denom_S] at h
  change E₆ _ = (Complex.I : ℂ) ^ (6 : ℤ) * E₆ _ at h
  norm_num [zpow_ofNat, pow_succ, Complex.I_mul_I] at h
  linear_combination h / 2

private theorem eisenstein_four_at_rho : E₄ ρ = 0 := by
  have h := transform_level_one E₄ (S * T) ρ
  have hs : (S * T) • ρ = ρ := stabilizer_ρ.mpr (by simp)
  rw [hs] at h
  have hd : denom (S * T : SL(2, ℤ)) ρ = (ρ : ℂ) + 1 := by
    rw [ModularGroup.denom_apply]
    norm_num [ModularGroup.S, ModularGroup.T, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hd] at h
  have hr := ρ_sq
  have hpow : ((ρ : ℂ) + 1) ^ (4 : ℕ) = -(ρ : ℂ) - 1 := by
    linear_combination ((ρ : ℂ) ^ 2 + 3 * ρ + 2) * hr
  rw [zpow_ofNat, hpow] at h
  have hne : (ρ : ℂ) + 2 ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    norm_num [ρ] at this
  apply (mul_eq_zero.mp (show ((ρ : ℂ) + 2) * E₄ ρ = 0 by linear_combination h)).resolve_left hne

/-- The square lattice has modular invariant 1728. -/
theorem modularInvariant_i : modularInvariant UpperHalfPlane.I = 1728 := by
  rw [modularInvariant, div_eq_iff (ModularForm.discriminant_ne_zero _)]
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq UpperHalfPlane.I
  rw [eisenstein_six_at_i] at h
  linear_combination -1728 * h

/-- The hexagonal lattice has modular invariant zero. -/
theorem modularInvariant_rho : modularInvariant ρ = 0 := by
  simp [modularInvariant, eisenstein_four_at_rho]

end GRHArticle.SingularModuli

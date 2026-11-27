import GRHArticle.SingularModuli.ModularInvariant

/-!
# Polynomial descent through the level-one modular invariant

A level-one modular form of weight `12 n`, divided by the `n`th power of the
modular discriminant, is a polynomial in the modular invariant.
-/

namespace GRHArticle.SingularModuli

open Polynomial ModularForm ModularFormClass EisensteinSeries CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

private noncomputable def highestEisensteinTerm (n : ℕ) : ModularForm 𝒮ℒ (12 * (n : ℤ)) :=
  ModularForm.mcast (by push_cast; ring) (E₄.pow (3 * n))

private theorem highestEisensteinTerm_apply (n : ℕ) (z : ℍ) :
    highestEisensteinTerm n z = E₄ z ^ (3 * n) := by
  simp only [highestEisensteinTerm, ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply]

private theorem highestEisensteinTerm_qExpansion_coeff_zero (n : ℕ) :
    (qExpansion 1 (highestEisensteinTerm n)).coeff 0 = 1 := by
  simp only [highestEisensteinTerm, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    E_qExpansion_coeff_zero (by decide : 3 ≤ 4) (by decide : Even 4), one_pow]

private theorem highestEisensteinTerm_via_modularInvariant (n : ℕ) (z : ℍ) :
    highestEisensteinTerm n z = (ModularForm.discriminant z) ^ n * (modularInvariant z) ^ n := by
  rw [highestEisensteinTerm_apply, modularInvariant, div_pow, ← pow_mul]
  field_simp [ModularForm.discriminant_ne_zero z]

/-- Every level-one form of weight `12 n` is `Δ ^ n` times a polynomial of
degree at most `n` in the modular invariant. -/
theorem modularForm_weight_twelve_mul_eq_discriminant_pow_polynomial :
    ∀ (n : ℕ) (f : ModularForm 𝒮ℒ (12 * (n : ℤ))), ∃ P : ℂ[X],
      P.natDegree ≤ n ∧ ∀ z : ℍ, f z = (ModularForm.discriminant z) ^ n *
        P.eval (modularInvariant z) := by
  intro n
  induction n with
  | zero =>
    intro f
    let f₀ := ModularForm.mcast (show (12 * (0 : ℕ) : ℤ) = 0 by decide) f
    obtain ⟨c, hc⟩ := levelOne_weight_zero_const f₀
    refine ⟨C c, by simp, ?_⟩
    intro z
    simp only [pow_zero, Polynomial.eval_C, one_mul]
    change f₀ z = c
    exact congrFun hc z
  | succ n ih =>
    intro f
    let c := (qExpansion 1 f).coeff 0
    let e := highestEisensteinTerm (n + 1)
    let g := f - c • e
    have hg₀ : (qExpansion 1 g).coeff 0 = 0 := by
      have hs := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c e
      change qExpansion 1 (c • e : ModularForm 𝒮ℒ _) = _ at hs
      rw [show (g : ℍ → ℂ) = (f : ℍ → ℂ) - (c • e : ModularForm 𝒮ℒ _) from rfl,
        ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL f
          (c • e : ModularForm 𝒮ℒ _),
        hs, map_sub, PowerSeries.coeff_smul, smul_eq_mul]
      rw [show (qExpansion 1 e).coeff 0 = 1 from highestEisensteinTerm_qExpansion_coeff_zero _,
        mul_one]
      exact sub_self c
    let cusp := toCuspForm g hg₀
    let g' := ModularForm.mcast
      (show 12 * ((n + 1 : ℕ) : ℤ) - 12 = 12 * (n : ℤ) by push_cast; ring)
      (CuspForm.discriminantEquiv cusp)
    obtain ⟨P, hP, hvalue⟩ := ih g'
    refine ⟨P + C c * X ^ (n+1),
      natDegree_add_le_of_degree_le (hP.trans (Nat.le_succ n)) (natDegree_C_mul_X_pow_le _ _), ?_⟩
    intro z
    have hgg : ModularForm.discriminant z * g' z = g z :=
      ModularForm.discriminant_mul_discriminantEquiv_apply cusp z
    have hstep : g z = ModularForm.discriminant z ^ (n + 1) * P.eval (modularInvariant z) := by
      rw [← hgg, hvalue z, pow_succ]
      ring
    have hf : f z = g z + c * e z := by
      change f z = (f z - c * e z) + c * e z
      ring
    rw [hf, hstep, show e z = _ from highestEisensteinTerm_via_modularInvariant (n+1) z,
      eval_add, eval_mul, eval_C, eval_pow, eval_X]
    ring

end GRHArticle.SingularModuli

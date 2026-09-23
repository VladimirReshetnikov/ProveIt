import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# Formal second-order translation in two variables

The first variable is the center and the second is the increment. The
binomial coefficient formula for formal substitution supplies an exact
quadratic remainder over every commutative ring, without coefficient growth
or characteristic assumptions.
This is the formal remainder identity used in `trigonometry:prop:lift`.
-/

namespace Surreal.FormalPowerSeries

open MvPowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

private theorem finTwo_eq_single_zero_iff (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 0 (d 0) ↔ d 1 = 0 := by
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    ext i
    fin_cases i <;> simp [h]

private theorem coeff_subst_first (f : PowerSeries R) (d : Fin 2 →₀ ℕ) :
    coeff d (PowerSeries.subst (X 0) f) = if d 1 = 0 then f.coeff (d 0) else 0 := by
  simp only [PowerSeries.coeff_subst_single, finTwo_eq_single_zero_iff]

private theorem coeff_subst_first_mul_second (f : PowerSeries R) (d : Fin 2 →₀ ℕ) :
    coeff d (PowerSeries.subst (X 0) f * X 1) =
      if d 1 = 1 then f.coeff (d 0) else 0 := by
  rw [X_def (1 : Fin 2), coeff_mul_monomial]
  simp only [Finsupp.single_le_iff, coeff_subst_first,
    Finsupp.tsub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne
    (by decide : (0 : Fin 2) ≠ 1), Nat.sub_zero, mul_one]
  by_cases h0 : d 1 = 0
  · simp [h0]
  · have hpos : 1 ≤ d 1 := Nat.one_le_iff_ne_zero.mpr h0
    have hsub : d 1 - 1 = 0 ↔ d 1 = 1 := by omega
    simp only [hpos, if_true, hsub]

private def translationSecondRemainderFin (f : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  fun d => ((d 0 + d 1 + 2).choose (d 0) : R) * f.coeff (d 0 + d 1 + 2)

private theorem coeff_translationSecondRemainderFin (f : PowerSeries R) (d : Fin 2 →₀ ℕ) :
    coeff d (translationSecondRemainderFin f) =
      ((d 0 + d 1 + 2).choose (d 0) : R) * f.coeff (d 0 + d 1 + 2) := rfl

private theorem translation_identity_fin (f : PowerSeries R) :
    PowerSeries.subst (X 0 + X 1) f =
      PowerSeries.subst (X 0) f + PowerSeries.subst (X 0) (PowerSeries.derivative R f) * X 1 +
        X 1 ^ 2 * translationSecondRemainderFin f := by
  ext d
  rw [PowerSeries.coeff_subst_X_zero_add_X_one]
  simp only [map_add, coeff_subst_first, coeff_subst_first_mul_second,
    PowerSeries.coeff_derivative]
  rw [X_pow_eq, coeff_monomial_mul]
  simp only [Finsupp.single_le_iff, one_mul, coeff_translationSecondRemainderFin,
    Finsupp.tsub_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), Nat.sub_zero]
  by_cases h0 : d 1 = 0
  · simp [h0]
  · by_cases h1 : d 1 = 1
    · simp [h1, Nat.choose_succ_self_right, mul_comm]
    · have h2 : 2 ≤ d 1 := by omega
      have he : d 0 + (d 1 - 2) + 2 = d 0 + d 1 := by omega
      simp [h0, h1, h2, he]

private theorem rename_subst {σ τ : Type*} (g : σ → τ) [Filter.TendstoCofinite g]
    (a : MvPowerSeries σ R) (ha : PowerSeries.HasSubst a) (f : PowerSeries R) :
    rename g (PowerSeries.subst a f) = PowerSeries.subst (rename g a) f := by
  rw [rename_eq_subst, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply ha.const (HasSubst.X_comp g)]
  rw [← rename_eq_subst]
  rfl

/-- The formal quadratic remainder after translating by the `true` variable,
with the `false` variable as center. -/
def translationSecondRemainder (f : PowerSeries R) : MvPowerSeries Bool R :=
  rename finTwoEquiv (translationSecondRemainderFin f)

/-- The translated quadratic remainder has the original quadratic coefficient at zero. -/
@[simp] theorem constantCoeff_translationSecondRemainder (f : PowerSeries R) :
    constantCoeff (translationSecondRemainder f) = f.coeff 2 := by
  rw [translationSecondRemainder, constantCoeff_rename,
    ← coeff_zero_eq_constantCoeff_apply, coeff_translationSecondRemainderFin]
  simp

/-- Exact formal translation with the derivative as linear term and a quadratic remainder. -/
theorem subst_add_eq_subst_add_derivative_mul_add_sq_mul (f : PowerSeries R) :
    PowerSeries.subst (X false + X true) f =
      PowerSeries.subst (X false) f +
        PowerSeries.subst (X false) (PowerSeries.derivative R f) * X true +
          X true ^ 2 * translationSecondRemainder f := by
  have h := congrArg (rename (R := R) finTwoEquiv) (translation_identity_fin f)
  simpa only [map_add, map_mul, map_pow,
    rename_subst finTwoEquiv (X (0 : Fin 2) + X 1)
      ((PowerSeries.HasSubst.X 0).add (PowerSeries.HasSubst.X 1)),
    rename_subst finTwoEquiv (X (0 : Fin 2)) (PowerSeries.HasSubst.X 0), rename_X,
    show finTwoEquiv 0 = false from rfl, show finTwoEquiv 1 = true from rfl,
    translationSecondRemainder] using h

end

end Surreal.FormalPowerSeries

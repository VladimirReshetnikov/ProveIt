import Surreal.Foundations.OmnificPurelyInfiniteModule

/-!
# Linear coefficient extraction on purely infinite omnific integers

The coefficientwise kernel clause of `odg:thm:decomposable` (a). Each
coefficient of an actual normal form is a real linear functional, and
vanishing of all coefficients detects zero.
-/

universe u
namespace Surreal.Foundations.SignSequence

open SmallNormalForm

noncomputable section

/-- Extract a fixed Conway coefficient from the actual purely infinite omnific vector space. -/
def omnificPurelyInfiniteCoeff (a : SignSequence.{u}) : omnificPurelyInfiniteIdeal.{u} →ₗ[ℝ] ℝ where
  toFun x := coeff (normalForm (omnificToSurreal x.val)) a
  map_add' x y := by
    change coeff (normalForm (omnificToSurreal (x.val + y.val))) a = _
    rw [map_add, normalForm_add, coeff_add]
  map_smul' r x := by
    change coeff (normalForm (omnificToSurreal (r • x).val)) a = _
    rw [omnificPurelyInfinite_real_smul]
    have hc : normalFormHahnHom (ofReal r : SignSequence.{u}) =
        _root_.HahnSeries.single 0 r := by
      ext g
      simp only [normalFormHahnHom, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, normalForm_ofReal, single, toSurreal_zero]
      change (Pi.single 0 r : _root_.Surreal.{u} → ℝ) (OrderDual.ofDual g) = _
      simp only [Pi.single_apply, _root_.HahnSeries.coeff_single]
      split_ifs <;> first | rfl | contradiction
    change (normalFormHahnHom (ofReal r * omnificToSurreal x.val)).coeff
      (OrderDual.toDual (toSurreal a)) = _
    rw [map_mul, hc, _root_.HahnSeries.coeff_single_zero_mul]
    rfl

/-- A purely infinite omnific integer is zero exactly when all its coefficients vanish. -/
theorem omnificPurelyInfinite_eq_zero_iff (x : omnificPurelyInfiniteIdeal.{u}) :
    x = 0 ↔ ∀ a, omnificPurelyInfiniteCoeff a x = 0 := by
  constructor
  · rintro rfl a
    exact map_zero _
  · intro hx
    apply Subtype.val_injective
    apply omnificToSurreal_injective
    apply cutEvaluationRingEquiv.symm.injective
    apply SmallNormalForm.ext
    intro a
    change coeff (normalForm (omnificToSurreal x.val)) a =
      coeff (normalForm (omnificToSurreal 0)) a
    rw [map_zero, normalForm_zero, coeff_zero]
    exact hx a

/-- Real linear equations hold exactly when they hold on each real coefficient vector. -/
theorem omnificPurelyInfinite_linear_coeff_iff {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) (x : n → omnificPurelyInfiniteIdeal.{u}) :
    (∀ j, ∑ k, A j k • x k = 0) ↔
      ∀ a j, ∑ k, A j k * omnificPurelyInfiniteCoeff a (x k) = 0 := by
  simp only [omnificPurelyInfinite_eq_zero_iff, map_sum, map_smul, smul_eq_mul]
  exact forall_comm

end
end Surreal.Foundations.SignSequence

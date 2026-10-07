import Mathlib.RingTheory.Nilpotent.Basic
import OAI.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient

namespace OAI

section

namespace Erdos3.WeightedLoweringAut

open MvPolynomial

variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

noncomputable def degreeAction (e : WeightedLoweringAut w R) (n : ℕ) :
    weightedSupportLE (R := R) w n ≃ₗ[R] weightedSupportLE (R := R) w n where
  toFun p := ⟨e.val p, e.preserves_degree p.property⟩
  invFun p := ⟨e.val.symm p, (e⁻¹).preserves_degree p.property⟩
  left_inv p := Subtype.ext (e.val.symm_apply_apply p)
  right_inv p := Subtype.ext (e.val.apply_symm_apply p)
  map_add' p q := Subtype.ext (map_add e.val (p : MvPolynomial σ R) (q : MvPolynomial σ R))
  map_smul' c p := Subtype.ext (map_smul e.val c (p : MvPolynomial σ R))

theorem degreeAction_apply_coe (e : WeightedLoweringAut w R) (n : ℕ)
    (p : weightedSupportLE (R := R) w n) :
    (e.degreeAction n p : MvPolynomial σ R) = e.val p := rfl

noncomputable def degreeActionHom (n : ℕ) :
    WeightedLoweringAut w R →*
      (weightedSupportLE (R := R) w n ≃ₗ[R] weightedSupportLE (R := R) w n) where
  toFun e := e.degreeAction n
  map_one' := by
    apply LinearEquiv.ext
    intro p
    rfl
  map_mul' e f := by
    apply LinearEquiv.ext
    intro p
    rfl

theorem degreeAction_difference_pow_coe (e : WeightedLoweringAut w R) (n k : ℕ)
    (p : weightedSupportLE (R := R) w n) :
    ((((e.degreeAction n).toLinearMap - 1) ^ k) p : MvPolynomial σ R) =
      (polynomialHomDifference e.val.toAlgHom ^ k) (p : MvPolynomial σ R) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl

theorem degreeAction_difference_pow_zero (e : WeightedLoweringAut w R) (n : ℕ) :
    ((e.degreeAction n).toLinearMap - 1) ^ (n + 1) = 0 := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change ((((e.degreeAction n).toLinearMap - 1) ^ (n + 1)) p : MvPolynomial σ R) = 0
  rw [degreeAction_difference_pow_coe]
  exact polynomialHomDifference_pow_eq_zero w e.val.toAlgHom e.property p.property

theorem degreeAction_difference_nilpotent (e : WeightedLoweringAut w R) (n : ℕ) :
    IsNilpotent ((e.degreeAction n).toLinearMap - 1) :=
  ⟨n + 1, e.degreeAction_difference_pow_zero n⟩

theorem degreeActionHom_injective (n : ℕ) (hw : ∀ i, w i ≤ n) :
    Function.Injective (degreeActionHom (w := w) (R := R) n) := by
  intro e f h
  have he : e.val.toAlgHom = f.val.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    have hi := congrArg (fun L : weightedSupportLE (R := R) w n ≃ₗ[R]
        weightedSupportLE (R := R) w n =>
      (L ⟨X i, weightedSupportLE_mono (hw i) (weightedSupportLE_X w i)⟩ :
        MvPolynomial σ R)) h
    exact hi
  apply Subtype.ext
  apply DFunLike.ext
  intro p
  exact congrArg (fun F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R => F p) he

end Erdos3.WeightedLoweringAut

end

end OAI

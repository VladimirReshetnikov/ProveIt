import Surreal.Foundations.SmallNormalFormConstants
import Surreal.Foundations.SignSequenceGameBirthday

/-!
# Conway monomials in the canonical cut evaluation

The Conway omega cut is the simplest positive representative of its
Archimedean class: all left options have strictly higher valuation, and all
right options have strictly lower valuation. Any positive representative of
the same class therefore realizes that cut and extends its sign prefix.
Combining this with the singleton candidate's opposite prefix relation
identifies evaluation of formal monomials with unit coefficient.
-/

universe u

namespace Surreal.Foundations.SignSequence
noncomputable section

/-- A Conway monomial is a sign prefix of every positive surreal of the
same valuation. This simplicity statement uses its native omega cut. -/
theorem omegaPower_isPrefix_of_pos_of_valuation_eq (a x : SignSequence.{u}) (hx : 0 < x)
    (hv : valuation x = valuation (omegaPower a)) : IsPrefix (omegaPower a) x := by
  have hx' : 0 < toSurreal x := by simpa only [toSurreal_zero] using (toSurreal_lt_iff 0 x).mpr hx
  have he : ArchimedeanClass.mk (toSurreal x) = ArchimedeanClass.mk (ω^ (toSurreal a)) := by
    simpa only [toSurreal_omegaPower] using
      (archimedeanClass_toSurreal_eq_iff x (omegaPower a)).mpr ((valuation_eq_iff _ _).mp hv)
  have hl : ∀ y (hy : y ∈ (ω^ (toIGame a)).moves .left),
      letI := IGame.Numeric.of_mem_moves hy
      _root_.Surreal.mk y < toSurreal x := by
    intro y hy
    letI := IGame.Numeric.of_mem_moves hy
    have hm := hy
    rw [IGame.leftMoves_wpow] at hm
    rcases Set.mem_insert_iff.mp hm with rfl | hm
    · simpa using hx'
    · obtain ⟨q, hq, b, hb, rfl⟩ := hm
      letI := IGame.Numeric.of_mem_moves hb
      have hq0 : q.toRat ≠ 0 := by exact_mod_cast ne_of_gt hq
      apply ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg ?_ hx'.le
      rw [_root_.Surreal.mk_mul, _root_.Surreal.mk_dyadic, _root_.Surreal.mk_wpow,
        ArchimedeanClass.mk_mul, ArchimedeanClass.mk_ratCast hq0, _root_.zero_add, he]
      exact _root_.Surreal.archimedeanClassMk_wpow_strictAnti
        ((_root_.Surreal.mk_lt_mk).mpr (IGame.Numeric.left_lt hb))
  have hr : ∀ y (hy : y ∈ (ω^ (toIGame a)).moves .right),
      letI := IGame.Numeric.of_mem_moves hy
      toSurreal x < _root_.Surreal.mk y := by
    intro y hy
    letI := IGame.Numeric.of_mem_moves hy
    have hm := hy
    rw [IGame.rightMoves_wpow] at hm
    obtain ⟨q, hq, b, hb, rfl⟩ := hm
    letI := IGame.Numeric.of_mem_moves hb
    have hq0 : q.toRat ≠ 0 := by exact_mod_cast ne_of_gt hq
    have hp : 0 < _root_.Surreal.mk ((q : IGame) * ω^ b) := by
      rw [_root_.Surreal.mk_mul, _root_.Surreal.mk_dyadic, _root_.Surreal.mk_wpow]
      exact mul_pos (by exact_mod_cast hq) (_root_.Surreal.wpow_pos _)
    apply ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg ?_ hp.le
    rw [_root_.Surreal.mk_mul, _root_.Surreal.mk_dyadic, _root_.Surreal.mk_wpow,
      ArchimedeanClass.mk_mul, ArchimedeanClass.mk_ratCast hq0, _root_.zero_add, he]
    exact _root_.Surreal.archimedeanClassMk_wpow_strictAnti
      ((_root_.Surreal.mk_lt_mk).mpr (IGame.Numeric.lt_right hb))
  have hc : cut (numericGameSignCut (ω^ (toIGame a))) = omegaPower a := by
    rw [cut_numericGameSignCut, _root_.Surreal.mk_wpow]
    rfl
  rw [← hc]
  apply cut_isPrefix
  constructor
  · intro i
    let y := (equivShrink ((ω^ (toIGame a)).moves .left)).symm i
    change toSurrealOrderIso.symm (_root_.Surreal.mk y.val) < x
    apply (toSurreal_lt_iff _ _).mp
    rw [toSurreal_orderIso_symm]
    exact hl y.val y.property
  · intro i
    let y := (equivShrink ((ω^ (toIGame a)).moves .right)).symm i
    change x < toSurrealOrderIso.symm (_root_.Surreal.mk y.val)
    apply (toSurreal_lt_iff _ _).mp
    rw [toSurreal_orderIso_symm]
    exact hr y.val y.property
end
end Surreal.Foundations.SignSequence
namespace Surreal.Foundations.SmallNormalForm
open SignSequence
noncomputable section

/-- Evaluation of a formal monomial with coefficient one is the actual
Conway omega power. -/
@[simp] theorem cutEvaluation_single_one (a : SignSequence.{u}) :
    cutEvaluation (single a 1) = omegaPower a := by
  have hp : IsPrefix (cutEvaluation (single a 1)) (omegaPower a) := by
    simpa only [map_one, _root_.one_mul] using cutEvaluation_single_isPrefix a 1
  have ha : a ∈ support (single a 1) := by simp
  have h := cutEvaluation_remainder (single a 1) a ha
  simp [trunc_single_self] at h
  have hl := leading_of_valuation_sub_omega_gt (cutEvaluation (single a 1)) a 1
    one_ne_zero (by simpa only [map_one, _root_.one_mul, WithTop.LinearOrderedAddCommGroup.coe_neg] using h)
  have hx : 0 < cutEvaluation (single a 1) := by
    rw [← SignSequence.leadingCoeff_pos_iff, hl.2]
    exact zero_lt_one
  apply hp.antisymm
  apply omegaPower_isPrefix_of_pos_of_valuation_eq a _ hx
  rw [valuation_of_ne_zero hx.ne', hl.1, valuation_omegaPower]
end
end Surreal.Foundations.SmallNormalForm

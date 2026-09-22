import Surreal.Foundations.SignSequenceValuationBounds
import Surreal.Foundations.SignSequenceBounds

/-!
# Algebra and nonuniqueness of small valuation approximations

The ultrametric inequality gives transitivity at a fixed valuation scale.
Every small family of approximation thresholds admits a nonzero monomial
perturbation beyond all of them. Consequently approximation conditions alone
cannot identify the value of an infinite normal form: the simplicity condition
in the cut construction is an additional, essential requirement.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

theorem valuation_sub_comm (x y : SignSequence.{u}) :
    valuation (x - y) = valuation (y - x) := by
  rw [← neg_sub y x, valuation_neg]

/-- Being closer than a fixed valuation scale is transitive. -/
theorem valuation_sub_gt_trans {x y z a : SignSequence.{u}}
    (hxy : (a : WithTop SignSequence.{u}) < valuation (x - y))
    (hyz : (a : WithTop SignSequence.{u}) < valuation (y - z)) :
    (a : WithTop SignSequence.{u}) < valuation (x - z) := by
  have h := (lt_min hxy hyz).trans_le (min_valuation_le_add (x - y) (y - z))
  simpa only [sub_add_sub_cancel] using h

/-- Close centers define the same strict valuation ball. -/
theorem valuation_sub_gt_iff_of_close {p q a : SignSequence.{u}}
    (hpq : (a : WithTop SignSequence.{u}) < valuation (p - q)) (x : SignSequence.{u}) :
    (a : WithTop SignSequence.{u}) < valuation (x - p) ↔
      (a : WithTop SignSequence.{u}) < valuation (x - q) := by
  constructor
  · intro h
    exact valuation_sub_gt_trans h hpq
  · intro h
    exact valuation_sub_gt_trans h (by simpa only [valuation_sub_comm q p] using hpq)

/-- A perturbation beyond every specified threshold preserves all approximations. -/
theorem valuation_approximations_add {I : Type v} (p a : I → SignSequence.{u})
    {x δ : SignSequence.{u}} (hx : ∀ i, (a i : WithTop SignSequence.{u}) < valuation (x - p i))
    (hδ : ∀ i, (a i : WithTop SignSequence.{u}) < valuation δ) :
    ∀ i, (a i : WithTop SignSequence.{u}) < valuation (x + δ - p i) := by
  intro i
  have h := (lt_min (hx i) (hδ i)).trans_le (min_valuation_le_add (x - p i) δ)
  convert h using 1
  congr 1
  abel

/-- Any solution of a small family of strict valuation bounds has a distinct
solution obtained by adding a positive Conway monomial. -/
theorem exists_larger_same_valuation_approximations {I : Type v} [Small.{u} I]
    (p a : I → SignSequence.{u}) {x : SignSequence.{u}}
    (hx : ∀ i, (a i : WithTop SignSequence.{u}) < valuation (x - p i)) :
    ∃ y : SignSequence.{u}, x < y ∧
      ∀ i, (a i : WithTop SignSequence.{u}) < valuation (y - p i) := by
  obtain ⟨b, hb⟩ := small_strict_upper_bounds.exists_bound_of_small_set (Set.range a)
  refine ⟨x + tMonomial b, lt_add_of_pos_right x (tMonomial_pos b), ?_⟩
  apply valuation_approximations_add p a hx
  intro i
  rw [valuation_tMonomial]
  exact WithTop.coe_lt_coe.mpr (hb _ (Set.mem_range_self i))

/-- A small family of valuation inequalities never has exactly one solution. -/
theorem not_existsUnique_valuation_approximations {I : Type v} [Small.{u} I]
    (p a : I → SignSequence.{u}) :
    ¬ ∃! x : SignSequence.{u}, ∀ i, (a i : WithTop SignSequence.{u}) < valuation (x - p i) := by
  rintro ⟨x, hx, huniq⟩
  obtain ⟨y, hxy, hy⟩ := exists_larger_same_valuation_approximations p a hx
  exact hxy.ne (huniq y hy).symm

end

end Surreal.Foundations.SignSequence

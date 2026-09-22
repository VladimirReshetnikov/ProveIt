import Surreal.Foundations.SignSequenceValuationBounds
import Surreal.Foundations.SignSequenceCutOperation

/-!
# Simplest intersections of small compatible valuation balls

Pairwise compatible strict valuation balls admit a common point when the
index type is small in the birthday universe. The cut of all ordinary
reciprocal-radius bounds selects a unique simplest point: it is a sign
prefix of every solution. This is the first approximation construction in
`docs/NORMAL_FORM_BRIDGE.md`; approximation alone is not a uniqueness
principle for infinite normal forms.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

variable {I : Type v}

private theorem valuationBall_options_separated (p a : I → SignSequence.{u})
    (h : ∀ i j, ((min (a i) (a j) : SignSequence.{u}) : WithTop SignSequence.{u}) < valuation (p i - p j))
    (i j : I) (n m : ℕ) :
    p i - tMonomial (a i) / ((n : SignSequence.{u}) + 1) <
      p j + tMonomial (a j) / ((m : SignSequence.{u}) + 1) := by
  have hri : 0 < tMonomial (a i) / ((n : SignSequence.{u}) + 1) :=
    div_pos (tMonomial_pos _) (by positivity)
  have hrj : 0 < tMonomial (a j) / ((m : SignSequence.{u}) + 1) :=
    div_pos (tMonomial_pos _) (by positivity)
  rcases le_total (a i) (a j) with hij | hji
  · have hv : (a i : WithTop SignSequence.{u}) < valuation (p i - p j) := by
      simpa only [min_eq_left hij] using h i j
    have hb := (abs_lt.mp ((valuation_gt_iff_forall_nat_abs_lt (p i - p j) (a i)).mp hv n)).2
    linarith
  · have hv : (a j : WithTop SignSequence.{u}) < valuation (p i - p j) := by
      simpa only [min_eq_right hji] using h i j
    have hb := (abs_lt.mp ((valuation_gt_iff_forall_nat_abs_lt (p i - p j) (a j)).mp hv m)).2
    linarith

variable [Small.{u} I]

/-- All reciprocal-radius interval bounds, indexed in the birthday universe. -/
def valuationBallCut (p a : I → SignSequence.{u})
    (h : ∀ i j, ((min (a i) (a j) : SignSequence.{u}) : WithTop SignSequence.{u}) < valuation (p i - p j)) :
    SmallCutData.{u, u + 1} SignSequence.{u} (· < ·) where
  Left := Shrink (I × ℕ)
  Right := Shrink (I × ℕ)
  left k := p ((equivShrink (I × ℕ)).symm k).1 -
    tMonomial (a ((equivShrink (I × ℕ)).symm k).1) /
      ((((equivShrink (I × ℕ)).symm k).2 : SignSequence.{u}) + 1)
  right k := p ((equivShrink (I × ℕ)).symm k).1 +
    tMonomial (a ((equivShrink (I × ℕ)).symm k).1) /
      ((((equivShrink (I × ℕ)).symm k).2 : SignSequence.{u}) + 1)
  separated l r := valuationBall_options_separated p a h
    ((equivShrink (I × ℕ)).symm l).1 ((equivShrink (I × ℕ)).symm r).1
    ((equivShrink (I × ℕ)).symm l).2 ((equivShrink (I × ℕ)).symm r).2

/-- Realizing the interval cut is exactly membership in all the valuation balls. -/
theorem valuationBallCut_realizes_iff (p a : I → SignSequence.{u})
    (h : ∀ i j, ((min (a i) (a j) : SignSequence.{u}) : WithTop SignSequence.{u}) < valuation (p i - p j))
    (x : SignSequence.{u}) :
    (valuationBallCut p a h).IsRealizedBy x ↔
      ∀ i, (a i : WithTop SignSequence.{u}) < valuation (x - p i) := by
  constructor
  · rintro ⟨hl, hr⟩ i
    apply (valuation_gt_iff_forall_nat_abs_lt (x - p i) (a i)).mpr
    intro n
    have hln := hl ((equivShrink (I × ℕ)) (i, n))
    have hrn := hr ((equivShrink (I × ℕ)) (i, n))
    simp only [valuationBallCut, Equiv.symm_apply_apply] at hln hrn
    rw [abs_lt]
    constructor <;> linarith
  · intro hx
    constructor
    · intro k
      let i := ((equivShrink (I × ℕ)).symm k).1
      let n := ((equivShrink (I × ℕ)).symm k).2
      have hb := (valuation_gt_iff_forall_nat_abs_lt (x - p i) (a i)).mp (hx i) n
      change p i - tMonomial (a i) / ((n : SignSequence.{u}) + 1) < x
      have hl := (abs_lt.mp hb).1
      linarith
    · intro k
      let i := ((equivShrink (I × ℕ)).symm k).1
      let n := ((equivShrink (I × ℕ)).symm k).2
      have hb := (valuation_gt_iff_forall_nat_abs_lt (x - p i) (a i)).mp (hx i) n
      change x < p i + tMonomial (a i) / ((n : SignSequence.{u}) + 1)
      have hr := (abs_lt.mp hb).2
      linarith

/-- The canonical simplest common point of a small compatible family of balls. -/
def simplestValuationBallPoint (p a : I → SignSequence.{u})
    (h : ∀ i j, ((min (a i) (a j) : SignSequence.{u}) : WithTop SignSequence.{u}) < valuation (p i - p j)) :
    SignSequence.{u} := cut (valuationBallCut p a h)

/-- The simplest point satisfies every required strict valuation inequality. -/
theorem simplestValuationBallPoint_mem (p a : I → SignSequence.{u})
    (h : ∀ i j, ((min (a i) (a j) : SignSequence.{u}) : WithTop SignSequence.{u}) < valuation (p i - p j))
    (i : I) :
    (a i : WithTop SignSequence.{u}) < valuation (simplestValuationBallPoint p a h - p i) :=
  (valuationBallCut_realizes_iff p a h _).mp (cut_realizes _) i

/-- Simplicity compares the canonical point with every solution, not just other cuts. -/
theorem simplestValuationBallPoint_isPrefix (p a : I → SignSequence.{u})
    (h : ∀ i j, ((min (a i) (a j) : SignSequence.{u}) : WithTop SignSequence.{u}) < valuation (p i - p j))
    (x : SignSequence.{u}) (hx : ∀ i, (a i : WithTop SignSequence.{u}) < valuation (x - p i)) :
    IsPrefix (simplestValuationBallPoint p a h) x :=
  cut_isPrefix _ x ((valuationBallCut_realizes_iff p a h x).mpr hx)

/-- Compatible small valuation balls have a unique simplest common point.
The uniqueness includes the prefix condition and does not assert that the
intersection itself is a singleton. No nonempty-index assumption is needed. -/
theorem existsUnique_simplest_valuationBall_point (p a : I → SignSequence.{u})
    (h : ∀ i j, ((min (a i) (a j) : SignSequence.{u}) : WithTop SignSequence.{u}) < valuation (p i - p j)) :
    ∃! x : SignSequence.{u},
      (∀ i, (a i : WithTop SignSequence.{u}) < valuation (x - p i)) ∧
      ∀ y : SignSequence.{u},
        (∀ i, (a i : WithTop SignSequence.{u}) < valuation (y - p i)) → IsPrefix x y := by
  refine ⟨simplestValuationBallPoint p a h,
    ⟨simplestValuationBallPoint_mem p a h, simplestValuationBallPoint_isPrefix p a h⟩, ?_⟩
  intro y hy
  exact IsPrefix.antisymm (hy.2 _ (simplestValuationBallPoint_mem p a h))
    (simplestValuationBallPoint_isPrefix p a h y hy.1)

/-- With no ball constraints the simplest point is the empty sign sequence, zero. -/
@[simp] theorem simplestValuationBallPoint_of_isEmpty [IsEmpty I]
    (p a : I → SignSequence.{u})
    (h : ∀ i j, ((min (a i) (a j) : SignSequence.{u}) : WithTop SignSequence.{u}) < valuation (p i - p j)) :
    simplestValuationBallPoint p a h = 0 := by
  apply IsPrefix.antisymm (simplestValuationBallPoint_isPrefix p a h 0 (fun i => isEmptyElim i))
  exact ⟨by simp, fun i hi => by simp at hi⟩

end

end Surreal.Foundations.SignSequence

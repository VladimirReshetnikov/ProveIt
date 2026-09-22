import Surreal.Foundations.SignSequenceField
import Mathlib.Tactic.Ring

/-!
# The Conway product cut on the sign carrier

The multiplication transported through the proved sign/game equivalence
satisfies the four-family genetic formula `found:eq:mulcut`. The rectangle
identity proves the strict option bounds and hence their separation. The
exact cut value follows from the upstream raw-game multiplication formula,
rather than only from those bounds.

All option indices are small in the birthday universe. Multiplication,
its ring laws, and inversion have already been established in
`SignSequenceField`; this module identifies their product with the source's
canonical recursive presentation.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The common algebraic expression in all four Conway product families. -/
def mulOption (x y a b : SignSequence.{u}) : SignSequence.{u} :=
  a * y + x * b - a * b

/-- The difference from the product factors into the two option gaps. -/
theorem mul_sub_mulOption (x y a b : SignSequence.{u}) :
    x * y - mulOption x y a b = (x - a) * (y - b) := by
  unfold mulOption
  ring

theorem mulOption_lt_mul_of_lt_of_lt {x y a b : SignSequence.{u}}
    (ha : a < x) (hb : b < y) : mulOption x y a b < x * y := by
  apply sub_pos.mp
  rw [mul_sub_mulOption]
  exact mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)

theorem mulOption_lt_mul_of_gt_of_gt {x y a b : SignSequence.{u}}
    (ha : x < a) (hb : y < b) : mulOption x y a b < x * y := by
  apply sub_pos.mp
  rw [mul_sub_mulOption]
  exact mul_pos_of_neg_of_neg (sub_neg.mpr ha) (sub_neg.mpr hb)

theorem mul_lt_mulOption_of_lt_of_gt {x y a b : SignSequence.{u}}
    (ha : a < x) (hb : y < b) : x * y < mulOption x y a b := by
  apply sub_neg.mp
  rw [mul_sub_mulOption]
  exact mul_neg_of_pos_of_neg (sub_pos.mpr ha) (sub_neg.mpr hb)

theorem mul_lt_mulOption_of_gt_of_lt {x y a b : SignSequence.{u}}
    (ha : x < a) (hb : b < y) : x * y < mulOption x y a b := by
  apply sub_neg.mp
  rw [mul_sub_mulOption]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr ha) (sub_pos.mpr hb)

/-- Left product options pair left with left, or right with right. -/
def mulLeft (x y : SignSequence.{u}) :
    (LeftIndex x × LeftIndex y) ⊕ (RightIndex x × RightIndex y) → SignSequence.{u} :=
  Sum.elim
    (fun p => mulOption x y (leftOption x p.1) (leftOption y p.2))
    (fun p => mulOption x y (rightOption x p.1) (rightOption y p.2))

/-- Right product options pair left with right, or right with left. -/
def mulRight (x y : SignSequence.{u}) :
    (LeftIndex x × RightIndex y) ⊕ (RightIndex x × LeftIndex y) → SignSequence.{u} :=
  Sum.elim
    (fun p => mulOption x y (leftOption x p.1) (rightOption y p.2))
    (fun p => mulOption x y (rightOption x p.1) (leftOption y p.2))

theorem mulLeft_lt_mul (x y : SignSequence.{u})
    (i : (LeftIndex x × LeftIndex y) ⊕ (RightIndex x × RightIndex y)) :
    mulLeft x y i < x * y := by
  rcases i with ⟨i, j⟩ | ⟨i, j⟩
  · exact mulOption_lt_mul_of_lt_of_lt (leftOption_lt x i) (leftOption_lt y j)
  · exact mulOption_lt_mul_of_gt_of_gt (lt_rightOption x i) (lt_rightOption y j)

theorem mul_lt_mulRight (x y : SignSequence.{u})
    (j : (LeftIndex x × RightIndex y) ⊕ (RightIndex x × LeftIndex y)) :
    x * y < mulRight x y j := by
  rcases j with ⟨i, j⟩ | ⟨i, j⟩
  · exact mul_lt_mulOption_of_lt_of_gt (leftOption_lt x i) (lt_rightOption y j)
  · exact mul_lt_mulOption_of_gt_of_lt (lt_rightOption x i) (leftOption_lt y j)

/-- The four actual product-option families satisfy numeric separation. -/
theorem mul_options_separated (x y : SignSequence.{u})
    (i : (LeftIndex x × LeftIndex y) ⊕ (RightIndex x × RightIndex y))
    (j : (LeftIndex x × RightIndex y) ⊕ (RightIndex x × LeftIndex y)) :
    mulLeft x y i < mulRight x y j :=
  (mulLeft_lt_mul x y i).trans (mul_lt_mulRight x y j)

/-- The separated product cut, with option indices in the lower universe. -/
def mulCut (x y : SignSequence.{u}) :
    SmallCutData.{u, u + 1} SignSequence.{u} (· < ·) where
  Left := Shrink ((LeftIndex x × LeftIndex y) ⊕ (RightIndex x × RightIndex y))
  Right := Shrink ((LeftIndex x × RightIndex y) ⊕ (RightIndex x × LeftIndex y))
  left i := mulLeft x y ((equivShrink _).symm i)
  right j := mulRight x y ((equivShrink _).symm j)
  separated i j := mul_options_separated x y ((equivShrink _).symm i) ((equivShrink _).symm j)

/-- The product satisfies every strict bound of its genetic cut. -/
theorem mulCut_realized (x y : SignSequence.{u}) : (mulCut x y).IsRealizedBy (x * y) :=
  ⟨fun i => mulLeft_lt_mul x y ((equivShrink _).symm i),
    fun j => mul_lt_mulRight x y ((equivShrink _).symm j)⟩

private theorem range_shrink_sum {A B : Type (u + 1)} [Small.{u} A] [Small.{u} B]
    {X : Type*} (f : A ⊕ B → X) :
    Set.range (fun i : Shrink (A ⊕ B) => f ((equivShrink (A ⊕ B)).symm i)) =
      Set.range (fun i : A => f (Sum.inl i)) ∪ Set.range (fun j : B => f (Sum.inr j)) :=
  ((equivShrink (A ⊕ B)).symm.surjective.range_comp f).trans (Sum.range_eq f)

private theorem toGame_toSurreal_mulOption (x y a b : SignSequence.{u}) :
    _root_.Surreal.toGame (toSurreal (mulOption x y a b)) =
      Game.mk (IGame.mulOption (toIGame x) (toIGame y) (toIGame a) (toIGame b)) := by
  simp only [mulOption, toSurreal_sub, toSurreal_add, toSurreal_mul]
  simp only [toSurreal, ← _root_.Surreal.mk_mul, ← _root_.Surreal.mk_add, ← _root_.Surreal.mk_sub,
    _root_.Surreal.toGame_mk, IGame.mulOption]

/-- The actual field product is exactly the simplest value of Conway's
four-family multiplication cut (`found:eq:mulcut`). -/
theorem mul_eq_cut (x y : SignSequence.{u}) : x * y = cut (mulCut x y) := by
  have hl :
      _root_.Surreal.toGame '' Set.range (toSurrealCut (mulCut x y)).left =
        Game.mk '' ((fun p => IGame.mulOption (toIGame x) (toIGame y) p.1 p.2) ''
          ((toIGame x).moves .left ×ˢ (toIGame y).moves .left ∪
            (toIGame x).moves .right ×ˢ (toIGame y).moves .right)) := by
    simp only [leftMoves_toIGame, rightMoves_toIGame, Set.image_union,
      Set.prod_range_range_eq, ← Set.range_comp]
    change Set.range (fun i : Shrink ((LeftIndex x × LeftIndex y) ⊕
      (RightIndex x × RightIndex y)) =>
      _root_.Surreal.toGame (toSurreal (mulLeft x y ((equivShrink _).symm i)))) =
        Set.range (fun p : LeftIndex x × LeftIndex y =>
          Game.mk (IGame.mulOption (toIGame x) (toIGame y)
            (toIGame (leftOption x p.1)) (toIGame (leftOption y p.2)))) ∪
        Set.range (fun p : RightIndex x × RightIndex y =>
          Game.mk (IGame.mulOption (toIGame x) (toIGame y)
            (toIGame (rightOption x p.1)) (toIGame (rightOption y p.2))))
    rw [range_shrink_sum (fun i => _root_.Surreal.toGame (toSurreal (mulLeft x y i)))]
    congr 1
    · apply congrArg Set.range
      funext p
      exact toGame_toSurreal_mulOption x y (leftOption x p.1) (leftOption y p.2)
    · apply congrArg Set.range
      funext p
      exact toGame_toSurreal_mulOption x y (rightOption x p.1) (rightOption y p.2)
  have hr :
      _root_.Surreal.toGame '' Set.range (toSurrealCut (mulCut x y)).right =
        Game.mk '' ((fun p => IGame.mulOption (toIGame x) (toIGame y) p.1 p.2) ''
          ((toIGame x).moves .left ×ˢ (toIGame y).moves .right ∪
            (toIGame x).moves .right ×ˢ (toIGame y).moves .left)) := by
    simp only [leftMoves_toIGame, rightMoves_toIGame, Set.image_union,
      Set.prod_range_range_eq, ← Set.range_comp]
    change Set.range (fun i : Shrink ((LeftIndex x × RightIndex y) ⊕
      (RightIndex x × LeftIndex y)) =>
      _root_.Surreal.toGame (toSurreal (mulRight x y ((equivShrink _).symm i)))) =
        Set.range (fun p : LeftIndex x × RightIndex y =>
          Game.mk (IGame.mulOption (toIGame x) (toIGame y)
            (toIGame (leftOption x p.1)) (toIGame (rightOption y p.2)))) ∪
        Set.range (fun p : RightIndex x × LeftIndex y =>
          Game.mk (IGame.mulOption (toIGame x) (toIGame y)
            (toIGame (rightOption x p.1)) (toIGame (leftOption y p.2))))
    rw [range_shrink_sum (fun i => _root_.Surreal.toGame (toSurreal (mulRight x y i)))]
    congr 1
    · apply congrArg Set.range
      funext p
      exact toGame_toSurreal_mulOption x y (leftOption x p.1) (rightOption y p.2)
    · apply congrArg Set.range
      funext p
      exact toGame_toSurreal_mulOption x y (rightOption x p.1) (leftOption y p.2)
  apply toSurrealOrderEmbedding.injective
  change toSurreal (x * y) = toSurreal (cut (mulCut x y))
  rw [toSurreal_mul, toSurreal_cut]
  apply _root_.Surreal.toGame_inj.mp
  rw [gameCut, _root_.Surreal.toGame_ofSets]
  change _root_.Surreal.toGame
    (_root_.Surreal.mk (toIGame x) * _root_.Surreal.mk (toIGame y)) = _
  rw [← _root_.Surreal.mk_mul, _root_.Surreal.toGame_mk, IGame.mul_eq, Game.mk_ofSets]
  congr 1
  exact congrArg₂ Player.cases hl.symm hr.symm

end

end Surreal.Foundations.SignSequence

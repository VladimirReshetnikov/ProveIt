import Surreal.Foundations.SignSequenceComparison
import Surreal.Foundations.SignSequenceRecursion
import CombinatorialGames.Game.Graph
import CombinatorialGames.Surreal.Basic

/-!
# Canonical sign sequences as numeric games

This is the first bridge between the sign model of `found:sub:signs` and
the numeric-game construction used for `found:eq:comparison`. The move
sets are exactly the canonical truncations, are small in the universe of
birthdays, and decrease the well-founded prefix relation. Comparison is
proved before numericity, directly from the recursive comparison rules.

The resulting map into the upstream quotient of numeric games is an
order embedding. Surjectivity and compatibility with arithmetic are
separate obligations; no existing operation on signs is replaced here.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The game graph whose moves are the canonical sign truncations. -/
def canonicalGameGraph : GameGraph SignSequence.{u} where
  moves
    | .left, x => Set.range (leftOption x)
    | .right, x => Set.range (rightOption x)

instance small_canonicalGameGraph_left (x : SignSequence.{u}) :
    Small.{u} (canonicalGameGraph.moves .left x) :=
  small_range (leftOption x)

instance small_canonicalGameGraph_right (x : SignSequence.{u}) :
    Small.{u} (canonicalGameGraph.moves .right x) :=
  small_range (rightOption x)

/-- Every move removes a nonempty terminal part of a sign sequence. -/
theorem canonicalGameGraph_move_simpler {x y : SignSequence.{u}} {p : Player}
    (h : y ∈ canonicalGameGraph.moves p x) : Simpler y x := by
  cases p with
  | left =>
    obtain ⟨i, rfl⟩ := h
    exact leftOption_simpler x i
  | right =>
    obtain ⟨i, rfl⟩ := h
    exact rightOption_simpler x i

instance canonicalGameGraph_isWellFounded : canonicalGameGraph.IsWellFounded where
  wf := ⟨simpler_wellFounded.mono (fun _ _ h => by
    obtain ⟨p, hp⟩ := h
    exact canonicalGameGraph_move_simpler hp)⟩

/-- The raw game with exactly the canonical sign options. -/
def toIGame (x : SignSequence.{u}) : IGame.{u} := canonicalGameGraph.toIGame x

@[simp] theorem leftMoves_toIGame (x : SignSequence.{u}) :
    (toIGame x).moves .left = Set.range (fun i : LeftIndex x => toIGame (leftOption x i)) := by
  rw [toIGame, GameGraph.moves_toIGame]
  exact (Set.range_comp' _ _).symm

@[simp] theorem rightMoves_toIGame (x : SignSequence.{u}) :
    (toIGame x).moves .right = Set.range (fun i : RightIndex x => toIGame (rightOption x i)) := by
  rw [toIGame, GameGraph.moves_toIGame]
  exact (Set.range_comp' _ _).symm

/-- The raw game is the cut of the images of all canonical options. -/
theorem toIGame_eq (x : SignSequence.{u}) :
    toIGame x =
      !{Set.range (fun i : LeftIndex x => toIGame (leftOption x i)) |
        Set.range (fun i : RightIndex x => toIGame (rightOption x i))} := by
  apply IGame.ext
  intro p
  cases p <;> simp

private theorem toIGame_le_iff_options (x y : SignSequence.{u}) :
    toIGame x ≤ toIGame y ↔
      (∀ i : LeftIndex x, ¬toIGame y ≤ toIGame (leftOption x i)) ∧
      (∀ j : RightIndex y, ¬toIGame (rightOption y j) ≤ toIGame x) := by
  rw [IGame.le_iff_forall_lf, leftMoves_toIGame, rightMoves_toIGame]
  simp only [Set.forall_mem_range]

private theorem toIGame_le_iff_both (x y : SignSequence.{u}) :
    (toIGame x ≤ toIGame y ↔ x ≤ y) ∧ (toIGame y ≤ toIGame x ↔ y ≤ x) := by
  induction x, y using Prod.GameAdd.recursion simpler_wellFounded simpler_wellFounded with
  | IH x y ih =>
    constructor
    · rw [toIGame_le_iff_options, le_iff_options_lt]
      apply and_congr
      · apply forall_congr'
        intro i
        rw [(ih (leftOption x i) y (.fst (leftOption_simpler x i))).2, not_le]
      · apply forall_congr'
        intro j
        rw [(ih x (rightOption y j) (.snd (rightOption_simpler y j))).2, not_le]
    · rw [toIGame_le_iff_options, le_iff_options_lt]
      apply and_congr
      · apply forall_congr'
        intro i
        rw [(ih x (leftOption y i) (.snd (leftOption_simpler y i))).1, not_le]
      · apply forall_congr'
        intro j
        rw [(ih (rightOption x j) y (.fst (rightOption_simpler x j))).1, not_le]

/-- Numerical comparison agrees exactly with comparison of the raw games. -/
@[simp] theorem toIGame_le_iff (x y : SignSequence.{u}) :
    toIGame x ≤ toIGame y ↔ x ≤ y := (toIGame_le_iff_both x y).1

@[simp] theorem toIGame_lt_iff (x y : SignSequence.{u}) :
    toIGame x < toIGame y ↔ x < y := by
  rw [lt_iff_le_not_ge, toIGame_le_iff, toIGame_le_iff, lt_iff_le_not_ge]

/-- Game equivalence identifies precisely equal sign sequences. -/
@[simp] theorem toIGame_equiv_iff (x y : SignSequence.{u}) :
    toIGame x ≈ toIGame y ↔ x = y := by
  change (toIGame x ≤ toIGame y ∧ toIGame y ≤ toIGame x) ↔ x = y
  rw [toIGame_le_iff, toIGame_le_iff, le_antisymm_iff]

/-- Canonical sign games are numeric: their options are recursively
numeric and every left option is less than every right option. -/
instance numeric_toIGame (x : SignSequence.{u}) : IGame.Numeric (toIGame x) := by
  induction x using simpler_wellFounded.induction with
  | h x ih =>
    constructor
    · intro a ha b hb
      rw [leftMoves_toIGame] at ha
      rw [rightMoves_toIGame] at hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      exact (toIGame_lt_iff _ _).mpr ((leftOption_lt x i).trans (lt_rightOption x j))
    · intro p a ha
      cases p with
      | left =>
        rw [leftMoves_toIGame] at ha
        obtain ⟨i, rfl⟩ := ha
        exact ih _ (leftOption_simpler x i)
      | right =>
        rw [rightMoves_toIGame] at ha
        obtain ⟨i, rfl⟩ := ha
        exact ih _ (rightOption_simpler x i)

/-- A sign sequence regarded as an equivalence class of numeric games. -/
def toSurreal (x : SignSequence.{u}) : _root_.Surreal.{u} := _root_.Surreal.mk (toIGame x)

@[simp] theorem toSurreal_le_iff (x y : SignSequence.{u}) :
    toSurreal x ≤ toSurreal y ↔ x ≤ y := toIGame_le_iff x y

@[simp] theorem toSurreal_lt_iff (x y : SignSequence.{u}) :
    toSurreal x < toSurreal y ↔ x < y := toIGame_lt_iff x y

theorem toSurreal_strictMono : StrictMono (toSurreal : SignSequence.{u} → _root_.Surreal.{u}) :=
  fun _ _ h => (toSurreal_lt_iff _ _).mpr h

/-- The explicit embedding into the upstream numeric-game quotient. -/
def toSurrealOrderEmbedding : SignSequence.{u} ↪o _root_.Surreal.{u} :=
  OrderEmbedding.ofStrictMono toSurreal toSurreal_strictMono

@[simp] theorem toSurreal_inj (x y : SignSequence.{u}) : toSurreal x = toSurreal y ↔ x = y :=
  toSurrealOrderEmbedding.injective.eq_iff

end

end Surreal.Foundations.SignSequence

import Surreal.Foundations.SignSequenceGames
import Surreal.Foundations.SignSequenceCutComparison
import Surreal.Foundations.GameCuts

/-!
# The sign carrier and the numeric-game quotient

The embedding from canonical signs into numeric games preserves every
small separated cut. Induction over a numeric game's options then proves
surjectivity, giving the equivalence of the two carriers in
`found:sub:signs`. This stage identifies their numerical orders and small
cut operations; arithmetic compatibility is a separate result.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Apply the sign-to-game embedding to the values of a small cut,
retaining both lower-universe index types. -/
def toSurrealCut (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    SmallCutData.{u, u + 1} _root_.Surreal.{u} (· < ·) where
  Left := c.Left
  Right := c.Right
  left i := toSurreal (c.left i)
  right i := toSurreal (c.right i)
  separated i j := (toSurreal_lt_iff _ _).mpr (c.separated i j)

@[simp] theorem toSurrealCut_realizes_iff
    (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) (x : SignSequence.{u}) :
    (toSurrealCut c).IsRealizedBy (toSurreal x) ↔ c.IsRealizedBy x := by
  change (∀ i, toSurreal (c.left i) < toSurreal x) ∧
    (∀ j, toSurreal x < toSurreal (c.right j)) ↔ _
  simp only [toSurreal_lt_iff]
  rfl

private theorem gameCut_eq_of_ranges
    (c d : SmallCutData.{u, u + 1} _root_.Surreal.{u} (· < ·))
    (hl : Set.range c.left = Set.range d.left)
    (hr : Set.range c.right = Set.range d.right) : gameCut c = gameCut d := by
  apply le_antisymm
  · apply (gameCut_le_gameCut_iff c d).mpr
    constructor
    · intro i
      obtain ⟨j, hj⟩ := hl ▸ (show c.left i ∈ Set.range c.left from ⟨i, rfl⟩)
      exact hj ▸ left_lt_gameCut d j
    · intro j
      obtain ⟨i, hi⟩ := hr.symm ▸ (show d.right j ∈ Set.range d.right from ⟨j, rfl⟩)
      exact hi ▸ gameCut_lt_right c i
  · apply (gameCut_le_gameCut_iff d c).mpr
    constructor
    · intro j
      obtain ⟨i, hi⟩ := hl.symm ▸ (show d.left j ∈ Set.range d.left from ⟨j, rfl⟩)
      exact hi ▸ left_lt_gameCut c i
    · intro i
      obtain ⟨j, hj⟩ := hr ▸ (show c.right i ∈ Set.range c.right from ⟨i, rfl⟩)
      exact hj ▸ gameCut_lt_right d j

private theorem range_toSurrealCut_canonical_left (x : SignSequence.{u}) :
    Set.range (toSurrealCut (canonicalCut x)).left =
      Set.range (fun i : LeftIndex x => toSurreal (leftOption x i)) := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(equivShrink (LeftIndex x)).symm i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨equivShrink (LeftIndex x) i, by simp [toSurrealCut, canonicalCut]⟩

private theorem range_toSurrealCut_canonical_right (x : SignSequence.{u}) :
    Set.range (toSurrealCut (canonicalCut x)).right =
      Set.range (fun i : RightIndex x => toSurreal (rightOption x i)) := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(equivShrink (RightIndex x)).symm i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨equivShrink (RightIndex x) i, by simp [toSurrealCut, canonicalCut]⟩

/-- The image of the canonical sign cut reconstructs the same numeric
game class. -/
@[simp] theorem gameCut_toSurrealCut_canonical (x : SignSequence.{u}) :
    gameCut (toSurrealCut (canonicalCut x)) = toSurreal x := by
  calc
    gameCut (toSurrealCut (canonicalCut x)) = gameCut (numericGameCut (toIGame x)) := by
      apply gameCut_eq_of_ranges
      · rw [range_toSurrealCut_canonical_left]
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          let a : (toIGame x).moves .left := ⟨toIGame (leftOption x i), by
            rw [leftMoves_toIGame]
            exact ⟨i, rfl⟩⟩
          refine ⟨equivShrink ((toIGame x).moves .left) a, ?_⟩
          simp only [numericGameCut, Equiv.symm_apply_apply]
          rfl
        · rintro ⟨i, rfl⟩
          let a := (equivShrink ((toIGame x).moves .left)).symm i
          have ha : a.val ∈ Set.range (fun j : LeftIndex x => toIGame (leftOption x j)) := by
            simpa only [leftMoves_toIGame] using a.property
          obtain ⟨j, hj⟩ := ha
          refine ⟨j, ?_⟩
          apply _root_.Surreal.mk_eq_mk.mpr
          change toIGame (leftOption x j) ≈ a.val
          change toIGame (leftOption x j) = a.val at hj
          rw [hj]
      · rw [range_toSurrealCut_canonical_right]
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          let a : (toIGame x).moves .right := ⟨toIGame (rightOption x i), by
            rw [rightMoves_toIGame]
            exact ⟨i, rfl⟩⟩
          refine ⟨equivShrink ((toIGame x).moves .right) a, ?_⟩
          simp only [numericGameCut, Equiv.symm_apply_apply]
          rfl
        · rintro ⟨i, rfl⟩
          let a := (equivShrink ((toIGame x).moves .right)).symm i
          have ha : a.val ∈ Set.range (fun j : RightIndex x => toIGame (rightOption x j)) := by
            simpa only [rightMoves_toIGame] using a.property
          obtain ⟨j, hj⟩ := ha
          refine ⟨j, ?_⟩
          apply _root_.Surreal.mk_eq_mk.mpr
          change toIGame (rightOption x j) ≈ a.val
          change toIGame (rightOption x j) = a.val at hj
          rw [hj]
    _ = toSurreal x := gameCut_numericGameCut (toIGame x)

/-- The embedding preserves every small separated cut, independently of
its presentation or any duplicate options. -/
theorem toSurreal_cut (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    toSurreal (cut c) = gameCut (toSurrealCut c) := by
  have hc := gameCut_toSurrealCut_canonical (cut c)
  apply le_antisymm
  · rw [← hc]
    apply (gameCut_le_gameCut_iff _ _).mpr
    constructor
    · intro i
      obtain ⟨j, hj⟩ := leftOption_cut_le c ((equivShrink (LeftIndex (cut c))).symm i)
      exact ((toSurreal_le_iff _ _).mpr hj).trans_lt (left_lt_gameCut (toSurrealCut c) j)
    · intro j
      rw [hc]
      exact (toSurreal_lt_iff _ _).mpr ((cut_realizes c).2 j)
  · rw [← hc]
    apply (gameCut_le_gameCut_iff _ _).mpr
    constructor
    · intro i
      rw [hc]
      exact (toSurreal_lt_iff _ _).mpr ((cut_realizes c).1 i)
    · intro j
      obtain ⟨i, hi⟩ := le_rightOption_cut c ((equivShrink (RightIndex (cut c))).symm j)
      exact (gameCut_lt_right (toSurrealCut c) i).trans_le ((toSurreal_le_iff _ _).mpr hi)

/-- Every numeric game has a sign representative, by induction on all
of its left and right options. -/
theorem exists_toSurreal_eq_mk (x : IGame.{u}) [hx : IGame.Numeric x] :
    ∃ y : SignSequence.{u}, toSurreal y = _root_.Surreal.mk x := by
  classical
  induction x using IGame.moveRecOn generalizing hx with
  | ind x ih =>
    have hl : ∀ i : (numericGameCut x).Left,
        ∃ y : SignSequence.{u}, toSurreal y = (numericGameCut x).left i := by
      intro i
      let a := (equivShrink (x.moves .left)).symm i
      exact @ih .left a.val a.property (IGame.Numeric.of_mem_moves a.property)
    have hr : ∀ j : (numericGameCut x).Right,
        ∃ y : SignSequence.{u}, toSurreal y = (numericGameCut x).right j := by
      intro j
      let a := (equivShrink (x.moves .right)).symm j
      exact @ih .right a.val a.property (IGame.Numeric.of_mem_moves a.property)
    choose l hl using hl
    choose r hr using hr
    let c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·) :=
      { Left := (numericGameCut x).Left
        Right := (numericGameCut x).Right
        left := l
        right := r
        separated := fun i j => (toSurreal_lt_iff _ _).mp (by
          rw [hl i, hr j]
          exact (numericGameCut x).separated i j) }
    refine ⟨cut c, ?_⟩
    rw [toSurreal_cut]
    calc
      gameCut (toSurrealCut c) = gameCut (numericGameCut x) := by
        apply gameCut_eq_of_ranges
        · exact congrArg Set.range (funext hl)
        · exact congrArg Set.range (funext hr)
      _ = _root_.Surreal.mk x := gameCut_numericGameCut x

/-- Every equivalence class of numeric games is represented by a sign
sequence of an ordinal length in the same universe. -/
theorem toSurreal_surjective :
    Function.Surjective (toSurreal : SignSequence.{u} → _root_.Surreal.{u}) := by
  intro x
  induction x using _root_.Surreal.ind with
  | mk x => exact exists_toSurreal_eq_mk x

/-- The sign carrier and the upstream numeric-game quotient have exactly
the same numerical order. -/
def toSurrealOrderIso : SignSequence.{u} ≃o _root_.Surreal.{u} :=
  OrderIso.ofSurjective toSurrealOrderEmbedding toSurreal_surjective

@[simp] theorem toSurrealOrderIso_apply (x : SignSequence.{u}) :
    toSurrealOrderIso x = toSurreal x := rfl

@[simp] theorem toSurreal_orderIso_symm (x : _root_.Surreal.{u}) :
    toSurreal (toSurrealOrderIso.symm x) = x := toSurrealOrderIso.apply_symm_apply x

@[simp] theorem orderIso_symm_toSurreal (x : SignSequence.{u}) :
    toSurrealOrderIso.symm (toSurreal x) = x := toSurrealOrderIso.symm_apply_apply x

end

end Surreal.Foundations.SignSequence

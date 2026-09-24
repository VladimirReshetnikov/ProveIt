import CombinatorialGames.Surreal.Basic
import Surreal.Foundations.SmallCutData

/-!
# Small cuts in the numeric-game quotient

The upstream surreal carrier provides separators for the lower-universe cut
data of `found:sub:cutdata`. Its cut comparison rule is `found:eq:comparison`.
These results concern the numeric-game quotient; identifying it with our sign
carrier is a separate construction.
-/

universe u

namespace Surreal.Foundations

open IGame

noncomputable section

/-- Form a surreal from two separated option families with indices in `Type u`.
The carrier itself is in `Type (u + 1)`, and no unrestricted cut is used. -/
def gameCut (c : SmallCutData.{u, u + 1} _root_.Surreal.{u} (· < ·)) :
    _root_.Surreal.{u} :=
  !{Set.range c.left | Set.range c.right}' (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact c.separated i j)

/-- Every left option of the native cut lies strictly below its value. -/
theorem left_lt_gameCut
    (c : SmallCutData.{u, u + 1} _root_.Surreal.{u} (· < ·)) (i : c.Left) :
    c.left i < gameCut c :=
  _root_.Surreal.lt_ofSets_of_mem_left ⟨i, rfl⟩

/-- Every right option of the native cut lies strictly above its value. -/
theorem gameCut_lt_right
    (c : SmallCutData.{u, u + 1} _root_.Surreal.{u} (· < ·)) (j : c.Right) :
    gameCut c < c.right j :=
  _root_.Surreal.ofSets_lt_of_mem_right ⟨j, rfl⟩

/-- The native cut realizes precisely the strict option bounds required by
the small-cut interface. -/
theorem gameCut_realizes
    (c : SmallCutData.{u, u + 1} _root_.Surreal.{u} (· < ·)) :
    c.IsRealizedBy (gameCut c) :=
  ⟨left_lt_gameCut c, gameCut_lt_right c⟩

/-- The numeric-game quotient has small cut fillers at the lower universe. -/
theorem game_hasSmallCutFillers :
    HasSmallCutFillers.{u, u + 1} _root_.Surreal.{u} (· < ·) :=
  fun c => ⟨gameCut c, gameCut_realizes c⟩

private theorem gameCut_numeric
    (c : SmallCutData.{u, u + 1} _root_.Surreal.{u} (· < ·)) :
    Numeric !{fun p => Surreal.out '' Player.cases (Set.range c.left) (Set.range c.right) p} := by
  refine .mk ?_ (by simp)
  rw [moves_ofSets, moves_ofSets]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩ _ ⟨_, ⟨j, rfl⟩, rfl⟩
  rw [← Surreal.mk_lt_mk, Surreal.out_eq, Surreal.out_eq]
  exact c.separated i j

/-- Conway's comparison rule `found:eq:comparison` for native small cuts.
It compares the actual game cuts, rather than arbitrary separators of their
option families. -/
theorem gameCut_le_gameCut_iff
    (c d : SmallCutData.{u, u + 1} _root_.Surreal.{u} (· < ·)) :
    gameCut c ≤ gameCut d ↔
      (∀ i, c.left i < gameCut d) ∧ (∀ j, gameCut c < d.right j) := by
  haveI := gameCut_numeric c
  haveI := gameCut_numeric d
  change @Surreal.mk _ _ ≤ @Surreal.mk _ _ ↔ _
  rw [Surreal.mk_le_mk, IGame.le_iff_forall_lf, IGame.moves_ofSets, IGame.moves_ofSets]
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · intro i
      have h := hl _ ⟨c.left i, ⟨i, rfl⟩, rfl⟩
      rw [← Surreal.mk_le_mk, Surreal.out_eq] at h
      exact lt_of_not_ge h
    · intro j
      have h := hr _ ⟨d.right j, ⟨j, rfl⟩, rfl⟩
      rw [← Surreal.mk_le_mk, Surreal.out_eq] at h
      exact lt_of_not_ge h
  · rintro ⟨hl, hr⟩
    constructor
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      rw [← Surreal.mk_le_mk, Surreal.out_eq]
      exact not_le_of_gt (hl i)
    · rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      rw [← Surreal.mk_le_mk, Surreal.out_eq]
      exact not_le_of_gt (hr j)

/-- Strict comparison has a witness among the opposite options. -/
theorem gameCut_lt_gameCut_iff
    (c d : SmallCutData.{u, u + 1} _root_.Surreal.{u} (· < ·)) :
    gameCut c < gameCut d ↔
      (∃ i, gameCut c ≤ d.left i) ∨ (∃ j, c.right j ≤ gameCut d) := by
  rw [← not_le, gameCut_le_gameCut_iff]
  simp only [not_and_or, not_forall, not_lt]

/-- The left and right moves of a numeric game, reindexed in the lower
universe and mapped into the surreal quotient. -/
def numericGameCut (x : IGame.{u}) [Numeric x] :
    SmallCutData.{u, u + 1} _root_.Surreal.{u} (· < ·) where
  Left := Shrink xᴸ
  Right := Shrink xᴿ
  left i := Surreal.mk ((equivShrink xᴸ).symm i)
  right j := Surreal.mk ((equivShrink xᴿ).symm j)
  separated i j := Surreal.mk_lt_mk.mpr
    (Numeric.left_lt_right ((equivShrink xᴸ).symm i).property
      ((equivShrink xᴿ).symm j).property)

/-- Reconstructing a numeric game from its quotient-valued move sets gives
its original surreal value. This statement retains small move indices and
does not select a canonical representative of the quotient. -/
theorem gameCut_numericGameCut (x : IGame.{u}) [Numeric x] :
    gameCut (numericGameCut x) = Surreal.mk x := by
  have hn : Numeric !{xᴸ | xᴿ} := by simpa only [ofSets_leftMoves_rightMoves] using
    (inferInstance : Numeric x)
  have h := Surreal.mk_ofSets (s := xᴸ) (t := xᴿ) (H := hn)
  simp only [ofSets_leftMoves_rightMoves] at h
  rw [h]
  unfold gameCut numericGameCut
  dsimp only
  have hl := (equivShrink xᴸ).symm.surjective.range_comp
    (fun y : xᴸ => Surreal.mk y)
  have hr := (equivShrink xᴿ).symm.surjective.range_comp
    (fun y : xᴿ => Surreal.mk y)
  simp only [Function.comp_def] at hl hr
  congr 1
  exact congrArg₂ Player.cases hl hr

end

end Surreal.Foundations

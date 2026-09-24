import Surreal.Foundations.SignSequenceGameEquiv
import CombinatorialGames.Game.Birthday

/-!
# Birthdays across the sign/game equivalence

The birthday of a canonical sign game is precisely its sign length. Among
all numeric raw games representing the same number, this canonical game
has the least birthday. These statements connect the ordinal length and
numeric-game notions of simplicity in `found:sub:signs` and
`found:sub:package`, without confusing birthday precedence with the prefix
relation.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The raw birthday of the canonical game is exactly the sign length. -/
@[simp] theorem birthday_toIGame (x : SignSequence.{u}) :
    (toIGame x).birthday = NatOrdinal.of x.birthday := by
  induction x using simpler_wellFounded.induction with
  | h x ih =>
    apply le_antisymm
    · apply IGame.birthday_le_iff.mpr
      intro p a ha
      cases p with
      | left =>
        rw [leftMoves_toIGame] at ha
        obtain ⟨i, rfl⟩ := ha
        rw [ih _ (leftOption_simpler x i)]
        exact i.val.property
      | right =>
        rw [rightMoves_toIGame] at ha
        obtain ⟨i, rfl⟩ := ha
        rw [ih _ (rightOption_simpler x i)]
        exact i.val.property
    · by_contra! hb
      let b := NatOrdinal.val (toIGame x).birthday
      have hb' : b < x.birthday := hb
      rcases SignType.trichotomy (x.signAt b) with hn | hz | hp
      · let i : RightIndex x := ⟨⟨b, hb'⟩, hn⟩
        have hm : toIGame (rightOption x i) ∈ (toIGame x).moves .right := by
          rw [rightMoves_toIGame]
          exact ⟨i, rfl⟩
        have hlt := IGame.birthday_lt_of_mem_moves hm
        rw [ih _ (rightOption_simpler x i)] at hlt
        change NatOrdinal.of b < (toIGame x).birthday at hlt
        exact (lt_irrefl _) hlt
      · exact ((x.signAt_ne_zero_iff b).mpr hb') hz
      · let i : LeftIndex x := ⟨⟨b, hb'⟩, hp⟩
        have hm : toIGame (leftOption x i) ∈ (toIGame x).moves .left := by
          rw [leftMoves_toIGame]
          exact ⟨i, rfl⟩
        have hlt := IGame.birthday_lt_of_mem_moves hm
        rw [ih _ (leftOption_simpler x i)] at hlt
        change NatOrdinal.of b < (toIGame x).birthday at hlt
        exact (lt_irrefl _) hlt

/-- The option cut of a numeric game, represented on the sign carrier. -/
def numericGameSignCut (g : IGame.{u}) [IGame.Numeric g] :
    SmallCutData.{u, u + 1} SignSequence.{u} (· < ·) where
  Left := (numericGameCut g).Left
  Right := (numericGameCut g).Right
  left i := toSurrealOrderIso.symm ((numericGameCut g).left i)
  right j := toSurrealOrderIso.symm ((numericGameCut g).right j)
  separated i j := toSurrealOrderIso.symm.strictMono ((numericGameCut g).separated i j)

/-- Reconstructing from the sign representatives of all options recovers
the sign representative of the numeric game itself. -/
theorem cut_numericGameSignCut (g : IGame.{u}) [IGame.Numeric g] :
    cut (numericGameSignCut g) = toSurrealOrderIso.symm (_root_.Surreal.mk g) := by
  apply (toSurreal_inj _ _).mp
  rw [toSurreal_cut, toSurreal_orderIso_symm, ← gameCut_numericGameCut g]
  apply le_antisymm
  · apply (gameCut_le_gameCut_iff _ _).mpr
    constructor
    · intro i
      simpa only [toSurrealCut, numericGameSignCut, toSurreal_orderIso_symm] using
        left_lt_gameCut (numericGameCut g) i
    · intro j
      simpa only [toSurrealCut, numericGameSignCut, toSurreal_orderIso_symm] using
        gameCut_lt_right (toSurrealCut (numericGameSignCut g)) j
  · apply (gameCut_le_gameCut_iff _ _).mpr
    constructor
    · intro i
      simpa only [toSurrealCut, numericGameSignCut, toSurreal_orderIso_symm] using
        left_lt_gameCut (toSurrealCut (numericGameSignCut g)) i
    · intro j
      simpa only [toSurrealCut, numericGameSignCut, toSurreal_orderIso_symm] using
        gameCut_lt_right (numericGameCut g) j

/-- Taking the canonical sign representative never increases the birthday
of a numeric raw game. -/
theorem birthday_orderIso_symm_mk_le (g : IGame.{u}) [hg : IGame.Numeric g] :
    (toSurrealOrderIso.symm (_root_.Surreal.mk g)).birthday ≤ NatOrdinal.val g.birthday := by
  induction g using IGame.moveRecOn generalizing hg with
  | ind g ih =>
    rw [← cut_numericGameSignCut g]
    apply birthday_cut_le
    · intro i
      let a := (equivShrink (g.moves .left)).symm i
      change (toSurrealOrderIso.symm (_root_.Surreal.mk a.val)).birthday <
        NatOrdinal.val g.birthday
      exact (@ih .left a.val a.property (IGame.Numeric.of_mem_moves a.property)).trans_lt
        (NatOrdinal.val.strictMono (IGame.birthday_lt_of_mem_moves a.property))
    · intro j
      let a := (equivShrink (g.moves .right)).symm j
      change (toSurrealOrderIso.symm (_root_.Surreal.mk a.val)).birthday <
        NatOrdinal.val g.birthday
      exact (@ih .right a.val a.property (IGame.Numeric.of_mem_moves a.property)).trans_lt
        (NatOrdinal.val.strictMono (IGame.birthday_lt_of_mem_moves a.property))

/-- The sign birthday is at most the birthday of every numeric game
representing that number. -/
theorem birthday_le_of_toSurreal_eq_mk (x : SignSequence.{u}) (g : IGame.{u})
    [IGame.Numeric g] (h : toSurreal x = _root_.Surreal.mk g) :
    x.birthday ≤ NatOrdinal.val g.birthday := by
  have hg := birthday_orderIso_symm_mk_le g
  rwa [← h, orderIso_symm_toSurreal] at hg

/-- The canonical raw game attains the least birthday among numeric
representatives of its surreal value. -/
theorem toIGame_birthday_minimal (x : SignSequence.{u}) (g : IGame.{u})
    [IGame.Numeric g] (h : toSurreal x = _root_.Surreal.mk g) :
    (toIGame x).birthday ≤ g.birthday := by
  rw [birthday_toIGame]
  exact birthday_le_of_toSurreal_eq_mk x g h

end

end Surreal.Foundations.SignSequence

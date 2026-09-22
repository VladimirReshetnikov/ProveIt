import Surreal.Foundations.SignSequenceGameEquiv
import Surreal.Foundations.SignSequenceGameConstants
import Surreal.Foundations.SignSequenceAddGroup
import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Arithmetic compatibility of the sign/game equivalence

The bridge preserves the Conway addition already constructed on signs in
`found:eq:addcut`. The proof follows the two summands' canonical options by
well-founded pair recursion. Negation and subtraction then follow from the
existing additive-group laws. No arithmetic operation is replaced here.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

private theorem range_shrink_sum {A B : Type (u + 1)} [Small.{u} A] [Small.{u} B]
    {X : Type*} (f : A ⊕ B → X) :
    Set.range (fun i : Shrink (A ⊕ B) => f ((equivShrink (A ⊕ B)).symm i)) =
      Set.range (fun i : A => f (Sum.inl i)) ∪ Set.range (fun j : B => f (Sum.inr j)) :=
  ((equivShrink (A ⊕ B)).symm.surjective.range_comp f).trans (Sum.range_eq f)

/-- The sign/game map preserves the previously defined recursive addition
of `found:eq:addcut`, rather than defining a new addition by transport. -/
@[simp] theorem toSurreal_add (x y : SignSequence.{u}) :
    toSurreal (x + y) = toSurreal x + toSurreal y := by
  induction x, y using Prod.GameAdd.recursion simpler_wellFounded simpler_wellFounded with
  | IH x y ih =>
    have hl :
        _root_.Surreal.toGame '' Set.range (toSurrealCut (addCut x y)).left =
          Game.mk '' ((· + toIGame y) '' (toIGame x).moves .left ∪
            (toIGame x + ·) '' (toIGame y).moves .left) := by
      rw [Set.image_union, leftMoves_toIGame, leftMoves_toIGame]
      simp only [← Set.range_comp]
      change Set.range (fun i : Shrink (LeftIndex x ⊕ LeftIndex y) =>
        _root_.Surreal.toGame (toSurreal (addLeft x y ((equivShrink _).symm i)))) =
          Set.range (fun i : LeftIndex x => Game.mk (toIGame (leftOption x i) + toIGame y)) ∪
          Set.range (fun i : LeftIndex y => Game.mk (toIGame x + toIGame (leftOption y i)))
      rw [range_shrink_sum (fun i => _root_.Surreal.toGame (toSurreal (addLeft x y i)))]
      congr 1
      · apply congrArg Set.range
        funext i
        change _root_.Surreal.toGame (toSurreal (leftOption x i + y)) = _
        rw [ih _ _ (.fst (leftOption_simpler x i))]
        simp only [_root_.Surreal.toGame_add, toSurreal, _root_.Surreal.toGame_mk, Game.mk_add]
      · apply congrArg Set.range
        funext i
        change _root_.Surreal.toGame (toSurreal (x + leftOption y i)) = _
        rw [ih _ _ (.snd (leftOption_simpler y i))]
        simp only [_root_.Surreal.toGame_add, toSurreal, _root_.Surreal.toGame_mk, Game.mk_add]
    have hr :
        _root_.Surreal.toGame '' Set.range (toSurrealCut (addCut x y)).right =
          Game.mk '' ((· + toIGame y) '' (toIGame x).moves .right ∪
            (toIGame x + ·) '' (toIGame y).moves .right) := by
      rw [Set.image_union, rightMoves_toIGame, rightMoves_toIGame]
      simp only [← Set.range_comp]
      change Set.range (fun i : Shrink (RightIndex x ⊕ RightIndex y) =>
        _root_.Surreal.toGame (toSurreal (addRight x y ((equivShrink _).symm i)))) =
          Set.range (fun i : RightIndex x => Game.mk (toIGame (rightOption x i) + toIGame y)) ∪
          Set.range (fun i : RightIndex y => Game.mk (toIGame x + toIGame (rightOption y i)))
      rw [range_shrink_sum (fun i => _root_.Surreal.toGame (toSurreal (addRight x y i)))]
      congr 1
      · apply congrArg Set.range
        funext i
        change _root_.Surreal.toGame (toSurreal (rightOption x i + y)) = _
        rw [ih _ _ (.fst (rightOption_simpler x i))]
        simp only [_root_.Surreal.toGame_add, toSurreal, _root_.Surreal.toGame_mk, Game.mk_add]
      · apply congrArg Set.range
        funext i
        change _root_.Surreal.toGame (toSurreal (x + rightOption y i)) = _
        rw [ih _ _ (.snd (rightOption_simpler y i))]
        simp only [_root_.Surreal.toGame_add, toSurreal, _root_.Surreal.toGame_mk, Game.mk_add]
    calc
      toSurreal (x + y) = gameCut (toSurrealCut (addCut x y)) := by
        rw [add_eq_cut x y, toSurreal_cut]
      _ = toSurreal x + toSurreal y := by
        apply _root_.Surreal.toGame_inj.mp
        rw [gameCut, _root_.Surreal.toGame_ofSets, _root_.Surreal.toGame_add]
        change _ = Game.mk (toIGame x) + Game.mk (toIGame y)
        rw [← Game.mk_add, IGame.add_eq, Game.mk_ofSets]
        congr 1
        exact congrArg₂ Player.cases hl hr

/-- The map preserves the existing zero and Conway addition. -/
def toSurrealAddHom : SignSequence.{u} →+ _root_.Surreal.{u} where
  toFun := toSurreal
  map_zero' := toSurreal_zero
  map_add' := toSurreal_add

@[simp] theorem toSurrealAddHom_apply (x : SignSequence.{u}) :
    toSurrealAddHom x = toSurreal x := rfl

/-- Independent sign reversal agrees with game negation. -/
@[simp] theorem toSurreal_neg (x : SignSequence.{u}) :
    toSurreal (-x) = -toSurreal x := toSurrealAddHom.map_neg x

@[simp] theorem toSurreal_sub (x y : SignSequence.{u}) :
    toSurreal (x - y) = toSurreal x - toSurreal y := toSurrealAddHom.map_sub x y

/-- The carrier equivalence preserves the already established additive group. -/
def toSurrealAddEquiv : SignSequence.{u} ≃+ _root_.Surreal.{u} where
  toEquiv := toSurrealOrderIso.toEquiv
  map_add' := toSurreal_add

@[simp] theorem toSurrealAddEquiv_apply (x : SignSequence.{u}) :
    toSurrealAddEquiv x = toSurreal x := rfl

/-- The signs and numeric-game quotients are isomorphic as ordered additive
groups, with their previously fixed operations and numerical orders. -/
def toSurrealOrderAddIso : SignSequence.{u} ≃+o _root_.Surreal.{u} where
  toAddEquiv := toSurrealAddEquiv
  map_le_map_iff' := toSurreal_le_iff _ _

@[simp] theorem toSurrealOrderAddIso_apply (x : SignSequence.{u}) :
    toSurrealOrderAddIso x = toSurreal x := rfl

end

end Surreal.Foundations.SignSequence

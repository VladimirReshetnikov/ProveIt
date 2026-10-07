import Mathlib.Algebra.Lie.Free
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

abbrev WordPolynomial (X : Type*) := MonoidAlgebra ℚ (FreeSemigroup X)

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

def rightBracket (x : L) : Module.End ℚ L where
  toFun z := ⁅z, x⁆
  map_add' z w := add_lie z w x
  map_smul' c z := smul_lie c z x

@[simp] theorem rightBracket_apply (x z : L) : rightBracket x z = ⁅z, x⁆ := rfl

def rightBracketList (f : X → L) : List X → Module.End ℚ L
  | [] => 1
  | x :: xs => rightBracketList f xs * rightBracket (f x)

@[simp] theorem rightBracketList_nil (f : X → L) : rightBracketList f [] = 1 := rfl
@[simp] theorem rightBracketList_cons (f : X → L) (x : X) (xs : List X) :
    rightBracketList f (x :: xs) = rightBracketList f xs * rightBracket (f x) := rfl

theorem rightBracketList_append (f : X → L) (xs ys : List X) :
    rightBracketList f (xs ++ ys) = rightBracketList f ys * rightBracketList f xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, rightBracketList_cons, ih, mul_assoc]

def rightBracketWord (f : X → L) (w : FreeSemigroup X) : Module.End ℚ L :=
  rightBracketList f (w.head :: w.tail)

theorem rightBracketWord_mul (f : X → L) (u v : FreeSemigroup X) :
    rightBracketWord f (u * v) = rightBracketWord f v * rightBracketWord f u := by
  change rightBracketList f ((u.head :: u.tail) ++ (v.head :: v.tail)) = _
  exact rightBracketList_append f _ _

def dynkinWord (f : X → L) (w : FreeSemigroup X) : L :=
  rightBracketList f w.tail (f w.head)

theorem dynkinWord_mul (f : X → L) (u v : FreeSemigroup X) :
    dynkinWord f (u * v) = rightBracketWord f v (dynkinWord f u) := by
  simp only [dynkinWord, FreeSemigroup.tail_mul, FreeSemigroup.head_mul,
    rightBracketList_append, Module.End.mul_apply, rightBracketWord]

noncomputable def wordLinearMap {M : Type*} [AddCommGroup M] [Module ℚ M]
    (v : FreeSemigroup X → M) : WordPolynomial X →ₗ[ℚ] M :=
  (Finsupp.linearCombination ℚ v).comp (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp] theorem wordLinearMap_single {M : Type*} [AddCommGroup M] [Module ℚ M]
    (v : FreeSemigroup X → M) (w : FreeSemigroup X) (r : ℚ) :
    wordLinearMap v (MonoidAlgebra.single w r) = r • v w := by
  simp [wordLinearMap]

noncomputable def dynkinMap (f : X → L) : WordPolynomial X →ₗ[ℚ] L :=
  wordLinearMap (dynkinWord f)

noncomputable def rightAction (f : X → L) : WordPolynomial X →ₗ[ℚ] Module.End ℚ L :=
  wordLinearMap (rightBracketWord f)

@[simp] theorem dynkinMap_single (f : X → L) (w : FreeSemigroup X) (r : ℚ) :
    dynkinMap f (MonoidAlgebra.single w r) = r • dynkinWord f w := wordLinearMap_single _ _ _

@[simp] theorem rightAction_single (f : X → L) (w : FreeSemigroup X) (r : ℚ) :
    rightAction f (MonoidAlgebra.single w r) = r • rightBracketWord f w :=
  wordLinearMap_single _ _ _

theorem rightAction_mul (f : X → L) (p q : WordPolynomial X) :
    rightAction f (p * q) = rightAction f q * rightAction f p := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p₁ p₂ h₁ h₂ => simp [add_mul, h₁, h₂, mul_add]
  | single u r =>
    induction q using MonoidAlgebra.induction_linear with
    | zero => simp
    | add q₁ q₂ h₁ h₂ => simp [mul_add, h₁, h₂, add_mul]
    | single v t =>
      simp only [MonoidAlgebra.single_mul_single, rightAction_single, rightBracketWord_mul]
      rw [smul_mul_smul, mul_comm r t]

theorem dynkinMap_mul (f : X → L) (p q : WordPolynomial X) :
    dynkinMap f (p * q) = rightAction f q (dynkinMap f p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p₁ p₂ h₁ h₂ => simp [add_mul, h₁, h₂]
  | single u r =>
    induction q using MonoidAlgebra.induction_linear with
    | zero => simp
    | add q₁ q₂ h₁ h₂ => simp [mul_add, h₁, h₂]
    | single v t =>
      simp only [MonoidAlgebra.single_mul_single, dynkinMap_single, rightAction_single,
        dynkinWord_mul, LinearMap.smul_apply, map_smul, smul_smul]

end Erdos3

end

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

def lieTreeEval (f : X → L) : FreeMagma X → L
  | .of x => f x
  | .mul u v => ⁅lieTreeEval f u, lieTreeEval f v⁆

noncomputable def commutatorTree : FreeMagma X → WordPolynomial X
  | .of x => MonoidAlgebra.single (FreeSemigroup.of x) 1
  | .mul u v => commutatorTree u * commutatorTree v - commutatorTree v * commutatorTree u

theorem rightBracket_lie (u v : L) :
    rightBracket ⁅u, v⁆ = rightBracket v * rightBracket u - rightBracket u * rightBracket v := by
  ext z
  change ⁅z, ⁅u, v⁆⁆ = ⁅⁅z, u⁆, v⁆ - ⁅⁅z, v⁆, u⁆
  rw [leibniz_lie, ← lie_skew u ⁅z, v⁆, sub_eq_add_neg]

theorem rightAction_commutatorTree (f : X → L) (t : FreeMagma X) :
    rightAction f (commutatorTree t) = rightBracket (lieTreeEval f t) := by
  induction t using FreeMagma.rec with
  | of x =>
    simp [commutatorTree, lieTreeEval, rightBracketWord, FreeSemigroup.of]
  | mul u v hu hv =>
    simp only [commutatorTree, map_sub, rightAction_mul, hu, hv, lieTreeEval, rightBracket_lie]

theorem dynkinMap_commutatorTree (f : X → L) (t : FreeMagma X) :
    dynkinMap f (commutatorTree t) = (t.length : ℚ) • lieTreeEval f t := by
  induction t using FreeMagma.rec with
  | of x => simp [commutatorTree, lieTreeEval, dynkinWord, FreeSemigroup.of]
  | mul u v hu hv =>
    simp only [commutatorTree, map_sub, dynkinMap_mul, rightAction_commutatorTree,
      hu, hv, rightBracket_apply, smul_lie, FreeMagma.length, Nat.cast_add,
      lieTreeEval, add_smul]
    rw [← lie_skew (lieTreeEval f v) (lieTreeEval f u), smul_neg, sub_neg_eq_add]

end Erdos3

end

end OAI

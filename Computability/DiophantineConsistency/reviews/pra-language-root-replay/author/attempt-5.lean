import DiophantineConsistency.PRACodeEncoding
import Foundation.FirstOrder.Arithmetic.Basic.Model

/-! First-order language of primitive-recursive function codes, equipped with
concrete arithmetic symbols. This module states no PRA axioms or conservation. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRALanguage
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes List.Vector

/-- Addition by recursion on the first argument: `(r,x) ↦ x+r`. -/
def addCore : Code 2 := .prec (.proj 0) (.comp .succ (.cons (.proj 1) (.nil 3)))
/-- Addition in the ordered-ring language's usual argument order. -/
def addCode : Code 2 := .comp addCore (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))
def mulCore : Code 2 := .prec (.zero 1)
  (.comp addCode (.cons (.proj 1) (.cons (.proj 2) (.nil 3))))
def mulCode : Code 2 := .comp mulCore (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))
def oneCode : Code 0 := .comp .succ (.cons (.zero 0) (.nil 0))

def language : Language where
  Func := Code
  Rel := Language.ORing.Rel

instance : language.Encodable where
  func := fun _ => inferInstance
  rel := fun _ => inferInstance

instance : language.ORing where
  eq := .eq
  lt := .lt
  zero := .zero 0
  one := oneCode
  add := addCode
  mul := mulCode

def embedding : ℒₒᵣ →ᵥ language := Language.ORing.embedding language

theorem eval_addCore (r x : ℕ) :
    eval addCore (r ::ᵥ x ::ᵥ nil) = x + r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change eval addCore (r ::ᵥ x ::ᵥ nil) + 1 = x + (r + 1)
      rw [ih, Nat.add_assoc]

theorem eval_addCode (x y : ℕ) :
    eval addCode (x ::ᵥ y ::ᵥ nil) = x + y := by
  change eval addCore (y ::ᵥ x ::ᵥ nil) = x + y
  exact eval_addCore y x

theorem eval_mulCore (r x : ℕ) :
    eval mulCore (r ::ᵥ x ::ᵥ nil) = x * r := by
  induction r with
  | zero => simp [mulCore, eval, forget, PRAFunctionCodes.eval]
  | succ r ih =>
      change eval addCode (eval mulCore (r ::ᵥ x ::ᵥ nil) ::ᵥ x ::ᵥ nil) = x * (r + 1)
      rw [eval_addCode, ih, Nat.mul_add]
      simp [Nat.add_comm]

theorem eval_mulCode (x y : ℕ) :
    eval mulCode (x ::ᵥ y ::ᵥ nil) = x * y := by
  change eval mulCore (y ::ᵥ x ::ᵥ nil) = x * y
  exact eval_mulCore y x

/-- Standard interpretation of every function code and the two relations. -/
@[reducible] def natStructure : Structure language ℕ where
  func := fun _ f v => eval f (List.Vector.ofFn v)
  rel := fun _ r v => match r with
    | .eq => v 0 = v 1
    | .lt => v 0 < v 1

theorem ofFn_two (v : Fin 2 → ℕ) :
    List.Vector.ofFn v = v 0 ::ᵥ v 1 ::ᵥ nil := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    rfl

theorem nat_reduct : natStructure.lMap embedding = Arithmetic.standardModel ℕ := by
  apply Structure.ext
  · funext k f v
    cases f with
    | zero => rfl
    | one => rfl
    | add =>
      change eval addCode (List.Vector.ofFn v) = v 0 + v 1
      rw [ofFn_two, eval_addCode]
    | mul =>
      change eval mulCode (List.Vector.ofFn v) = v 0 * v 1
      rw [ofFn_two, eval_mulCode]
  · funext k r v
    cases r <;> rfl

/-- Every ordered-ring formula has exactly the same natural semantics after
mapping its symbols into the primitive-recursive language. -/
theorem nat_formula_map {ξ : Type} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n)
    (b : Fin n → ℕ) (v : ξ → ℕ) :
    Semiformula.Eval (s := natStructure) b v (Semiformula.lMap embedding φ) ↔
      Semiformula.Eval (s := Arithmetic.standardModel ℕ) b v φ := by
  rw [Semiformula.eval_lMap, nat_reduct]

end DiophantineConsistency.PRALanguage

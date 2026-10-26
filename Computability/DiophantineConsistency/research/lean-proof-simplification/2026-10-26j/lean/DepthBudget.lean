import Lean.Elab.Tactic.Omega

/-!
Standalone mechanism prototype, checked with Lean 4.32.0.
This is a certificate language for upper bounds on representation depth.
It does not import ProveIt and is not a replacement for its primitive
GraphRep depth lemmas. Those lemmas are the intended trusted interface.
-/

namespace NewSimplification.DepthBudget

inductive Plan where
  | input
  | unary (floor charge : Nat) (child : Plan)
  | binary (floor charge : Nat) (left right : Plan)
  deriving Repr

def Plan.required : Plan → Nat
  | .input => 0
  | .unary floor _ child => max floor child.required
  | .binary floor _ left right => max floor (max left.required right.required)

def Plan.extra : Plan → Nat
  | .input => 0
  | .unary _ charge child => charge + child.extra
  | .binary _ charge left right => charge + max left.extra right.extra

/-- A derivation using local depth upper bounds. No evaluator is unfolded. -/
inductive Covers (base : Nat) : Plan → Nat → Prop where
  | input {d : Nat} : d ≤ base → Covers base .input d
  | unary {floor charge child dc d}
      (hc : Covers base child dc)
      (hd : d ≤ max floor dc + charge) :
      Covers base (.unary floor charge child) d
  | binary {floor charge left right dl dr d}
      (hl : Covers base left dl) (hr : Covers base right dr)
      (hd : d ≤ max floor (max dl dr) + charge) :
      Covers base (.binary floor charge left right) d

/-- The checker propagates two natural-number bounds and never expands the
represented graph or polynomial syntax. Its certificate plan is itself a tree. -/
theorem sound {base d : Nat} {p : Plan}
    (hc : Covers base p d) (hf : p.required ≤ base) :
    d ≤ base + p.extra := by
  induction hc with
  | input h => simpa [Plan.extra] using h
  | @unary floor charge child dc d hc hd ih =>
      simp only [Plan.required] at hf
      have hh := ih (by omega)
      simp only [Plan.extra]
      omega
  | @binary floor charge left right dl dr d hl hr hd ihl ihr =>
      simp only [Plan.required] at hf
      have hleft := ihl (by omega)
      have hright := ihr (by omega)
      simp only [Plan.extra]
      omega

def add (a b : Plan) : Plan := .binary 0 6 a b
def mul (a b : Plan) : Plan := .binary 0 6 a b
def arithmetic (a b : Plan) : Plan := .binary 512 8 a b
def factorial (a : Plan) : Plan := .unary 16384 6 a

/- These plans reproduce the constructor shapes of the corresponding
BoundedForallDepth proofs at commit 8e8b5dcb9549. They are cost data only.
The equality checks below verify this file's cost arithmetic, not the
unimplemented adapter from the actual repository GraphRep constructors. -/

def factorialPlan : Plan :=
  let n := Plan.input
  let cst := Plan.input
  let shift := add n cst
  let radius := arithmetic shift shift
  let c := arithmetic (add radius n) n
  let numerator := add (arithmetic (add radius cst) n) (arithmetic c cst)
  arithmetic numerator c

def productPlan : Plan :=
  let n := Plan.input
  let t := Plan.input
  let cst := Plan.input
  let q := add (arithmetic (add (mul (add n cst) t) cst) n) cst
  let first := mul (arithmetic t n) (mul (factorial n) (arithmetic (add q n) n))
  let denominator := arithmetic (mul t q) cst
  arithmetic first denominator

theorem factorialPlan_required : factorialPlan.required = 512 := by decide
theorem factorialPlan_extra : factorialPlan.extra = 50 := by decide
theorem productPlan_required : productPlan.required = 16384 := by decide
theorem productPlan_extra : productPlan.extra = 66 := by decide

theorem factorial_bound {d : Nat} (h : Covers 512 factorialPlan d) : d ≤ 562 := by
  have hs := sound h (by decide)
  simpa only [factorialPlan_extra] using hs

theorem product_bound {base d : Nat} (hf : 16384 ≤ base)
    (h : Covers base productPlan d) : d ≤ base + 66 := by
  have hs := sound h (by simpa only [productPlan_required] using hf)
  simpa only [productPlan_extra] using hs

#print axioms sound
#print axioms factorial_bound
#print axioms product_bound

end NewSimplification.DepthBudget

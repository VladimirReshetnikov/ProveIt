import DiophantineConsistency.SharingSeed33Syntax
import DiophantineConsistency.CurrentKernelData2011

/-! Source-only prototype. No theorem is claimed by this file. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroLanguage
open ExecutableJones

/-- Natural expressions in macro exponents and finite-range bounds. -/
inductive NExpr where
  | lit (n : Nat)
  | index
  | expo
  | add (a b : NExpr)
  | sub (a b : NExpr)
  | mul (a b : NExpr)
  | pow (a b : NExpr)

/-- Ring terms may reference only nodes in the already constructed prefix. -/
inductive Term (n : Nat) where
  | constant (z : Int)
  | input (i : Fin 9)
  | ref (i : Fin n)
  | fixedZ
  | fixedY
  | pcoef
  | add (a b : Term n)
  | sub (a b : Term n)
  | mul (a b : Term n)
  | pow (a : Term n) (exponent : NExpr)
  | sumRange (upper : NExpr) (body : Term n)
  | sumStar (body : Term n)

/-- A dependency-ordered telescope; the output is its final entry. -/
inductive Dag : Nat → Type where
  | nil : Dag 0
  | snoc {n : Nat} (prior : Dag n) (entry : Term n) : Dag (n + 1)

def seed : Expr (Fin 34) := SharingSeed33.seed CurrentWindowCarry2011.ports

def NExpr.scoped (indexOK starOK : Bool) : NExpr → Bool
  | .lit _ => true
  | .index => indexOK
  | .expo => starOK
  | .add a b | .sub a b | .mul a b | .pow a b => a.scoped indexOK starOK && b.scoped indexOK starOK

def Term.scoped {n : Nat} (indexOK starOK : Bool) : Term n → Bool
  | .constant _ | .input _ | .ref _ | .fixedZ | .fixedY => true
  | .pcoef => starOK
  | .add a b | .sub a b | .mul a b => a.scoped indexOK starOK && b.scoped indexOK starOK
  | .pow a e => a.scoped indexOK starOK && e.scoped indexOK starOK
  | .sumRange upper body => upper.scoped indexOK starOK && body.scoped true starOK
  | .sumStar body => body.scoped indexOK true

def Dag.scoped : {n : Nat} → Dag n → Bool
  | _, .nil => true
  | _, .snoc prior entry => prior.scoped && entry.scoped false false

/-- `sub` is natural subtraction, including its truncation at zero. -/
def NExpr.eval (r : Nat) (k : Fin 35 → Nat) : NExpr → Nat
  | .lit n => n
  | .index => r
  | .expo => codingExpo 33 4 k
  | .add a b => a.eval r k + b.eval r k
  | .sub a b => a.eval r k - b.eval r k
  | .mul a b => a.eval r k * b.eval r k
  | .pow a b => a.eval r k ^ b.eval r k

/-- Sum and power macros remain symbolic; no enormous range is expanded here. -/
def Term.eval {R : Type*} [CommRing R] {n : Nat}
    (a : Fin 9 → R) (prev : Fin n → R) (r : Nat) (k : Fin 35 → Nat) : Term n → R
  | .constant z => (z : R)
  | .input i => a i
  | .ref i => prev i
  | .fixedZ => (indexZ seed 0 : R)
  | .fixedY => (indexY seed 0 : R)
  | .pcoef => (pCoefficient seed k : R)
  | .add x y => x.eval a prev r k + y.eval a prev r k
  | .sub x y => x.eval a prev r k - y.eval a prev r k
  | .mul x y => x.eval a prev r k * y.eval a prev r k
  | .pow x exponent => x.eval a prev r k ^ exponent.eval r k
  | .sumRange upper body => ∑ j ∈ Finset.range (upper.eval r k), body.eval a prev j k
  | .sumStar body => ∑ k' ∈ codingStar 33 4, body.eval a prev r k'

def Dag.values {R : Type*} [CommRing R] (a : Fin 9 → R) : {n : Nat} → Dag n → (Fin n → R)
  | _, .nil => Fin.elim0
  | _, .snoc prior entry =>
      let prev := prior.values a
      Fin.snoc prev (entry.eval a prev 0 (fun _ => 0))

end DiophantineConsistency.Sign33MacroLanguage

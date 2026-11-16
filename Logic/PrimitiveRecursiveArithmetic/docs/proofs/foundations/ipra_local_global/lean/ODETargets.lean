import Std

/-!
Executable finite definitions and precise UNPROVED targets for Section 4.
The Goal declarations below are definitions of propositions, not theorems.
They neither assert an axiom nor supply a proof of the proposition.
These are ordinary Lean data definitions; their PR encodings and embedded
PRAAx derivations are the separate milestones in FORMALIZATION.md.
-/

namespace IPRALocalGlobal.ODE

abbrev Vec (d : Nat) := Fin d → Rat

structure Monomial (d : Nat) where
  coeff : Rat
  powers : Fin d → Nat

abbrev Poly (d : Nat) := List (Monomial d)
abbrev Field (d : Nat) := Fin d → Poly d

def sumQ (xs : List Rat) : Rat := xs.foldl (· + ·) 0
def maxQ (xs : List Rat) : Rat := xs.foldl (fun a b => if a ≤ b then b else a) 0
def norm {d : Nat} (x : Vec d) : Rat := maxQ (List.ofFn fun i => (x i).abs)
def near {d : Nat} (r : Rat) (x y : Vec d) : Prop :=
  ∀ i, (x i - y i).abs ≤ r
def inBox {d : Nat} (B : Rat) (x : Vec d) : Prop := ∀ i, (x i).abs ≤ B
def add {d : Nat} (x y : Vec d) : Vec d := fun i => x i + y i
def scale {d : Nat} (r : Rat) (x : Vec d) : Vec d := fun i => r * x i

def totalDegree {d : Nat} (m : Monomial d) : Nat :=
  (List.ofFn m.powers).foldl (· + ·) 0

def evalMonomial {d : Nat} (m : Monomial d) (x : Vec d) : Rat :=
  m.coeff * (List.ofFn fun i => x i ^ m.powers i).foldl (· * ·) 1

def evalPoly {d : Nat} (P : Poly d) (x : Vec d) : Rat :=
  sumQ (P.map fun m => evalMonomial m x)

def evalField {d : Nat} (F : Field d) (x : Vec d) : Vec d :=
  fun i => evalPoly (F i) x

def polyCap {d : Nat} (P : Poly d) (B : Rat) : Rat :=
  sumQ (P.map fun m => m.coeff.abs * B ^ totalDegree m)

def polyLip {d : Nat} (P : Poly d) (B : Rat) : Rat :=
  sumQ (P.map fun m =>
    if totalDegree m = 0 then 0
    else m.coeff.abs * (totalDegree m : Rat) * B ^ (totalDegree m - 1))

def fieldCap {d : Nat} (F : Field d) (B : Rat) : Rat :=
  maxQ (1 :: List.ofFn fun i => polyCap (F i) B)

def fieldLip {d : Nat} (F : Field d) (B : Rat) : Rat :=
  maxQ (List.ofFn fun i => polyLip (F i) B)

def dyadic (n : Nat) : Rat := 1 / (2 ^ n : Nat)
def mesh (T : Rat) (n : Nat) : Rat := T / (2 ^ n : Nat)

def eulerNode {d : Nat} (F : Field d) (x₀ : Vec d) (T : Rat)
    (n : Nat) : Nat → Vec d
  | 0 => x₀
  | j + 1 =>
      let x := eulerNode F x₀ T n j
      add x (scale (mesh T n) (evalField F x))

/-- At t=T the endpoint branch prevents an out-of-range step. The target
theorems below restrict t to [0,T] and assume T>0. -/
def polygon {d : Nat} (F : Field d) (x₀ : Vec d) (T : Rat)
    (n : Nat) (t : Rat) : Vec d :=
  let N := 2 ^ n
  let h := mesh T n
  let j := min N (t / h).floor.toNat
  let x := eulerNode F x₀ T n j
  if j = N then x else add x (scale (t - (j : Rat) * h) (evalField F x))

def growth (L T : Rat) : Nat := 3 ^ (L * T).ceil.toNat
def errorCap (L M T : Rat) : Nat :=
  max 1 (((growth L T : Rat) * L * M * T * T).ceil.toNat)

def ceilLog₂ (K : Nat) : Nat :=
  ((List.range (K + 1)).find? fun r => decide (K ≤ 2 ^ r)).getD K

def localB {d : Nat} (x₀ : Vec d) : Rat := 1 + norm x₀
def localT {d : Nat} (F : Field d) (x₀ : Vec d) : Rat :=
  1 / (2 * fieldCap F (localB x₀))

def solution {d : Nat} (F : Field d) (x₀ : Vec d) (p : Nat) (t : Rat) : Vec d :=
  let B := localB x₀
  let M := fieldCap F B
  let L := fieldLip F B
  let T := localT F x₀
  let c := ceilLog₂ (errorCap L M T) + 3
  polygon F x₀ T (p + c) t

def regular {d : Nat} (Y : Nat → Rat → Vec d) (T : Rat) : Prop :=
  ∀ p q t, 0 ≤ t → t ≤ T → near (dyadic p + dyadic q) (Y p t) (Y q t)

structure Controlled {d : Nat} (F : Field d) (x₀ : Vec d) (B T C : Rat)
    (Y : Nat → Rat → Vec d) : Prop where
  reg : regular Y T
  box : ∀ p t, 0 ≤ t → t ≤ T → inBox B (Y p t)
  initial : ∀ p, near (dyadic p) (Y p 0) x₀
  defect : ∀ p q r, 0 ≤ q → q ≤ T → 0 ≤ r → r ≤ T →
    near (C * (r - q) ^ 2 + dyadic p) (Y p r)
      (add (Y p q) (scale (r - q) (evalField F (Y p q))))

def UniformEulerBox {d : Nat} (F : Field d) (x₀ : Vec d) (T B : Rat) : Prop :=
  ∀ n j, j ≤ 2 ^ n → inBox B (eulerNode F x₀ T n j)

def RefinementGoal : Prop :=
  ∀ (d : Nat) (F : Field d) (x₀ : Vec d) (B T : Rat),
    0 < d → 1 ≤ B → 0 < T → UniformEulerBox F x₀ T B →
    ∀ n t, 0 ≤ t → t ≤ T →
      near ((growth (fieldLip F B) T : Rat) * fieldLip F B *
        fieldCap F B * T * T * dyadic n / 2)
        (polygon F x₀ T (n+1) t) (polygon F x₀ T n t)

def LocalExistenceGoal : Prop :=
  ∀ (d : Nat) (F : Field d) (x₀ : Vec d), 0 < d →
    Controlled F x₀ (localB x₀) (localT F x₀)
      (fieldLip F (localB x₀) * fieldCap F (localB x₀) / 2) (solution F x₀)

/-- Equality stated by arbitrarily accurate common-precision observations.
The paper constructs a PR schedule, which the subsequent deep proof must use. -/
def SameName {d : Nat} (Y Z : Nat → Rat → Vec d) (T : Rat) : Prop :=
  ∀ k t, 0 ≤ t → t ≤ T → ∃ p, k ≤ p ∧ near (dyadic k) (Y p t) (Z p t)

def UniquenessGoal : Prop :=
  ∀ (d : Nat) (F : Field d) (x₀ : Vec d) (B T C₁ C₂ : Rat)
    (Y Z : Nat → Rat → Vec d),
    0 < d → 1 ≤ B → 0 < T → 0 ≤ C₁ → 0 ≤ C₂ →
    Controlled F x₀ B T C₁ Y → Controlled F x₀ B T C₂ Z → SameName Y Z T

def mulPoly {d : Nat} (P Q : Poly d) : Poly d :=
  P.flatMap fun a => Q.map fun b =>
    { coeff := a.coeff * b.coeff, powers := fun i => a.powers i + b.powers i }

def derivative {d : Nat} (P : Poly d) (i : Fin d) : Poly d :=
  P.filterMap fun m =>
    if m.powers i = 0 then none
    else some {
      coeff := m.coeff * (m.powers i : Rat)
      powers := fun j => if j = i then m.powers j - 1 else m.powers j }

def samePowers {d : Nat} (a b : Fin d → Nat) : Bool :=
  (List.ofFn fun i => decide (a i = b i)).all id

def coefficient {d : Nat} (P : Poly d) (a : Fin d → Nat) : Rat :=
  sumQ (P.map fun m => if samePowers m.powers a then m.coeff else 0)

def coefficientZero {d : Nat} (P : Poly d) : Bool :=
  P.all fun m => decide (coefficient P m.powers = 0)

def liePolynomial {d : Nat} (F : Field d) (H : Poly d) : Poly d :=
  (List.ofFn fun i => mulPoly (derivative H i) (F i)).flatten

def remainderCap {d : Nat} (H : Poly d) (B M T : Rat) : Rat :=
  let D := maxQ [1, B, M*T]
  sumQ (H.map fun m =>
    if totalDegree m < 2 then 0
    else m.coeff.abs * (2 ^ totalDegree m : Nat) * D ^ (totalDegree m - 2))

def ConservationGoal : Prop :=
  ∀ (d : Nat) (F : Field d) (H : Poly d) (x₀ : Vec d) (B T : Rat),
    0 < d → 1 ≤ B → 0 < T → UniformEulerBox F x₀ T B →
    coefficientZero (liePolynomial F H) = true →
    ∀ n t, 0 ≤ t → t ≤ T →
      (evalPoly H (polygon F x₀ T n t) - evalPoly H x₀).abs ≤
        remainderCap H B (fieldCap F B) T * fieldCap F B ^ 2 * T ^ 2 * dyadic n

end IPRALocalGlobal.ODE

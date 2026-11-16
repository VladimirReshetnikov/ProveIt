import Std

/-!
Executable coefficient-list definitions and UNPROVED theorem targets for the
superelliptic certificate development. `def ...Target : Prop` only names a
proposition. It neither assumes nor proves it. There are no custom axioms or
placeholder proofs in this file. The accompanying article supplies complete
human proofs and a dependency-ordered plan for these targets.
-/

namespace IPRAFramework.PowerGapTargets

abbrev Polynomial := List Int

def normalize : Polynomial → Polynomial
  | [] => []
  | a :: p =>
    let q := normalize p
    if q.isEmpty && a == 0 then [] else a :: q

def coeff (p : Polynomial) (i : Nat) : Int := p[i]?.getD 0

def evaluate (p : Polynomial) (x : Int) : Int :=
  p.foldr (fun a b => a + x * b) 0

def add (p q : Polynomial) : Polynomial :=
  normalize ((List.range (max p.length q.length)).map
    (fun i => coeff p i + coeff q i))

def scalar (c : Int) (p : Polynomial) : Polynomial := normalize (p.map (c * ·))

def multiply (p q : Polynomial) : Polynomial :=
  if p.isEmpty || q.isEmpty then []
  else normalize ((List.range (p.length + q.length - 1)).map fun k =>
    (List.range (k + 1)).foldl
      (fun s i => s + coeff p i * coeff q (k - i)) 0)

def power (p : Polynomial) : Nat → Polynomial
  | 0 => [1]
  | n + 1 => multiply (power p n) p

def norm (p : Polynomial) : Nat := p.foldl (fun s a => s + a.natAbs) 0

def lowerNorm (p : Polynomial) : Nat := norm (p.take (p.length - 1))

structure Certificate where
  m : Nat
  D : Nat
  f : Polynomial
  A : Polynomial
  R : Polynomial
  deriving Repr

def valid (c : Certificate) : Bool :=
  decide (2 ≤ c.m) && decide (1 ≤ c.D) &&
  (normalize c.f == c.f) && (normalize c.A == c.A) &&
  (normalize c.R == c.R) && decide (2 ≤ c.A.length) &&
  !c.R.isEmpty &&
  decide (c.R.length - 1 < (c.m - 1) * (c.A.length - 1)) &&
  (scalar (Int.ofNat (c.D ^ c.m)) c.f == add (power c.A c.m) c.R)

def xBound (c : Certificate) : Nat :=
  (c.m - 1) * lowerNorm c.A + norm c.R

def yBound (c : Certificate) : Nat :=
  c.f.zipIdx.foldl (fun s (a, i) => s + a.natAbs * xBound c ^ i) 0

def RootBoundTarget : Prop :=
  ∀ (p : Polynomial), normalize p = p → p ≠ [] →
  ∀ x : Int, evaluate p x = 0 → x.natAbs ≤ lowerNorm p

def LeadingTermTarget : Prop :=
  ∀ (p : Polynomial), normalize p = p → 2 ≤ p.length →
  ∀ x : Int, 1 ≤ x.natAbs →
  x.natAbs ^ (p.length - 1) ≤
    (evaluate p x).natAbs + lowerNorm p * x.natAbs ^ (p.length - 2)

def CoefficientEvaluationTarget : Prop :=
  ∀ c : Certificate, valid c = true → ∀ x : Int,
    (Int.ofNat c.D) ^ c.m * evaluate c.f x =
      evaluate c.A x ^ c.m + evaluate c.R x

def OutsideBoxTarget : Prop :=
  ∀ c : Certificate, valid c = true → ∀ x : Int,
    xBound c < x.natAbs →
    evaluate c.R x ≠ 0 ∧
      (evaluate c.R x).natAbs < (evaluate c.A x).natAbs ^ (c.m - 1)

def HeightBoundTarget : Prop :=
  ∀ c : Certificate, valid c = true → ∀ x y : Int,
    y ^ c.m = evaluate c.f x →
      x.natAbs ≤ xBound c ∧ y.natAbs ≤ yBound c

def FamilyClassificationTarget : Prop :=
  ∀ m r : Nat, 3 ≤ m → 1 ≤ r → ∀ x y : Int,
    y ^ m = x ^ (m * r) + x + 1 ↔
      (x = -1 ∧ y ^ m = (-1 : Int) ^ (m * r)) ∨
      (x = 0 ∧ y ^ m = 1)

def sample : Certificate :=
  {m := 3, D := 1, f := [1, 1, 0, 1], A := [0, 1], R := [1, 1]}

#eval valid sample
#eval (xBound sample, yBound sample)

end IPRAFramework.PowerGapTargets

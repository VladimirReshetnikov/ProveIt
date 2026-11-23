/-
Finite semantic definitions accompanying chapters/analytic.tex.
STATUS: uncompiled formalization blueprint. No admitted theorem declarations.
Proof obligations are types in AnalyticGoals, not axioms or completed proofs.
Quote every fixed construction into PR/PTm before claiming an iPRA derivation.
-/
import ElementaryDefinitions

namespace NumberTheoryIPRA.Analytic
open NumberTheoryIPRA.Elementary

def primesUpTo (n : Nat) : List Nat :=
  (List.range (n + 1)).filter primeB

def primeCount (n : Nat) : Nat := (primesUpTo n).length

def primorial (n : Nat) : Nat := (primesUpTo n).foldl (· * ·) 1

def harmonic (n : Nat) : Rat :=
  (List.range n).foldl (fun a i => a + 1 / ((i + 1 : Nat) : Rat)) 0

def zetaPartial (s n : Nat) : Rat :=
  (List.range n).foldl
    (fun a i => a + 1 / (((i + 1 : Nat) : Rat) ^ s)) 0

def eulerProduct (s n : Nat) : Rat :=
  (primesUpTo n).foldl
    (fun a p => a * (1 - 1 / ((p : Rat) ^ s))⁻¹) 1

def eulerTruncated (s n j : Nat) : Rat :=
  (primesUpTo n).foldl
    (fun a p => a * (List.range (j + 1)).foldl
      (fun b e => b + 1 / ((p : Rat) ^ (s * e))) 0) 1

def primeReciprocalSum (n : Nat) : Rat :=
  (primesUpTo n).foldl (fun a p => a + 1 / (p : Rat)) 0

def primeReciprocalBound (k : Nat) : Nat := 2 ^ (2 * 4 ^ (4 * k + 1))

def omega (n : Nat) : Nat :=
  ((primesUpTo n).filter (fun p => dividesB p n)).length

def bigOmega (n : Nat) : Nat := (factors n).length

def sieveSurvivors (x z : Nat) : Nat :=
  ((List.range x).filter (fun i => coprimeB (i + 1) (primorial z))).length

def sieveMobiusSum (x z : Nat) : Int :=
  let m := primorial z
  (List.range m).foldl
    (fun a i =>
      let d := i + 1
      if dividesB d m then a + mobius d * ((x / d : Nat) : Int) else a) 0

def coprimePairs (x : Nat) : Nat :=
  (List.range x).foldl
    (fun a i => a + ((List.range x).filter
      (fun j => coprimeB (i + 1) (j + 1))).length) 0

def coprimeMobiusSum (x : Nat) : Int :=
  (List.range x).foldl (fun a i =>
    let d := i + 1
    a + mobius d * ((x / d : Nat) : Int) ^ 2) 0

/-- A list of obligations, not a constructed inhabitant and not an axiom. -/
structure AnalyticGoals : Prop where
  harmonicGrowth : ∀ m : Nat, (1 : Rat) + (m : Rat) / 2 ≤ harmonic (2 ^ m)
  chebyshev : ∀ k : Nat, 3 ≤ k →
    2 ^ (k - 1) ≤ k * primeCount (2 ^ k) ∧
    k * primeCount (2 ^ k) ≤ 6 * 2 ^ k
  eulerError : ∀ s n : Nat, 2 ≤ s → 1 ≤ n →
    0 ≤ eulerProduct s n - zetaPartial s n ∧
    eulerProduct s n - zetaPartial s n ≤ 1 / ((n : Rat) ^ (s - 1))
  primeReciprocalDivergence : ∀ k : Nat,
    (k : Rat) < primeReciprocalSum (primeReciprocalBound k)
  sieveIdentity : ∀ x z : Nat, (sieveSurvivors x z : Int) = sieveMobiusSum x z
  coprimeIdentity : ∀ x : Nat, (coprimePairs x : Int) = coprimeMobiusSum x

end NumberTheoryIPRA.Analytic

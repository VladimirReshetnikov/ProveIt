import Std

/-!
# An exact arithmetic target for the constructive prime number theorem

STATUS: formalization outline with executable definitions and small helper
proofs. This file was NOT compiled in the preparation environment, which did
not contain Lean. It does NOT prove the prime number theorem, and declares
no PNT axiom. The analytic estimates and their object-level iPRA derivations
are specified in the accompanying article and formalization plan.

This file needs only Lean's standard library. Its numerical kernel uses
natural numbers, structural recursion, and bounded tests. In particular,
the theorem's matrix contains no real numbers, logarithms, infinite limits,
or quantification over functions.

Write D(n)=(n^2)! and A(n)=sum_{j=n+1}^{n^2} D(n)/j. Then A(n)/D(n)
is the rational logarithm surrogate H_(n^2)-H_n. For n>=1,
  0 <= log n - A(n)/D(n) <= 1/n.
The interval theorem is a remaining formalization obligation; it is not
silently assumed by an axiom in this file.
-/

namespace ConstructivePNT

/-- Inclusive bounded conjunction. Each fixed primitive-recursive p gives
    a primitive-recursive function of the bound and parameters of p. -/
def allUpTo (p : Nat → Bool) : Nat → Bool
  | 0 => p 0
  | b + 1 => allUpTo p b && p (b + 1)

theorem allUpTo_iff (p : Nat → Bool) (b : Nat) :
    allUpTo p b = true ↔ ∀ i, i ≤ b → p i = true := by
  induction b with
  | zero =>
      constructor
      · intro h i hi
        have : i = 0 := by omega
        subst i
        exact h
      · intro h
        exact h 0 (Nat.le_refl 0)
  | succ b ih =>
      simp only [allUpTo, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h, hb⟩ i hi
        by_cases hil : i ≤ b
        · exact h i hil
        · have : i = b + 1 := by omega
          subst i
          exact hb
      · intro h
        exact ⟨fun i hi => h i (by omega), h (b + 1) (Nat.le_refl _)⟩

/-- A fully bounded definition of primality, valid also at 0 and 1. -/
def primeB (n : Nat) : Bool :=
  decide (2 ≤ n) &&
    allUpTo (fun d => decide (d ≤ 1 ∨ n ≤ d ∨ n % d ≠ 0)) n

/-- Number of primes at most n. -/
def primeCount : Nat → Nat
  | 0 => 0
  | n + 1 => primeCount n + if primeB (n + 1) then 1 else 0

theorem primeCount_le (n : Nat) : primeCount n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
      simp only [primeCount]
      split <;> omega

/-- Structural factorial, avoiding any external arithmetic library. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (Nat.succ_pos n) ih

/-- Sum over 0 <= j < b. -/
def sumBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => sumBelow f b + f b

def logDenominator (n : Nat) : Nat := fact (n * n)

def logNumerator (n : Nat) : Nat :=
  let d := logDenominator n
  sumBelow (fun j => if n < j then d / j else 0) (n * n + 1)

theorem logDenominator_pos (n : Nat) : 0 < logDenominator n :=
  fact_pos (n * n)

/-- Absolute difference, expressed entirely in natural arithmetic. -/
def absGap (a b : Nat) : Nat := (a - b) + (b - a)

/-- Exact decidable form of
      |pi(n)*(H_(n^2)-H_n)/n - 1| <= 1/k,
    for k>0 and n>=2. -/
abbrev rationalPNTBound (k n : Nat) : Prop :=
  k * absGap (primeCount n * logNumerator n) (n * logDenominator n)
    ≤ n * logDenominator n

def rationalPNTBoundB (k n : Nat) : Bool := decide (rationalPNTBound k n)

/-- The specification a concrete primitive-recursive cutoff must satisfy.
    This definition is not a proved theorem or an axiom. -/
def IsPNTModulus (cutoff : Nat → Nat) : Prop :=
  ∀ k n, 0 < k → cutoff k ≤ n → 2 ≤ n → rationalPNTBound k n

/-- The deliberately generous modulus selected in the accompanying proof.
    Keep it symbolic: even k=1 is far beyond feasible expansion. -/
def pntModulus (k : Nat) : Nat :=
  if k = 0 then 2 else
    let q := 8 * k
    let d := 2 ^ 20 * q ^ 3
    2 ^ (2 ^ (d ^ 2 + 2))

/-- The exact arithmetic PNT sentence whose iPRA derivation is the goal.
    It is stated here as a definition, not as a proved Lean theorem. -/
def ArithmeticPNT : Prop := IsPNTModulus pntModulus

/-- Fold all antecedents into one Boolean matrix. The closed arithmetic
    sentence is forall k n, pntCheck cutoff k n = true. -/
def pntCheck (cutoff : Nat → Nat) (k n : Nat) : Bool :=
  decide (k = 0 ∨ n < cutoff k ∨ n < 2) || rationalPNTBoundB k n

theorem pntCheck_iff (cutoff : Nat → Nat) :
    (∀ k n, pntCheck cutoff k n = true) ↔ IsPNTModulus cutoff := by
  constructor
  · intro h k n hk hn h2
    have hh := h k n
    simp only [pntCheck, rationalPNTBoundB, Bool.or_eq_true, decide_eq_true_eq] at hh
    rcases hh with hearly | hbound
    · omega
    · exact hbound
  · intro h k n
    by_cases hk : 0 < k
    · by_cases hcut : cutoff k ≤ n
      · by_cases h2 : 2 ≤ n
        · have hb : rationalPNTBoundB k n = true :=
            decide_eq_true (h k n hk hcut h2)
          simp [pntCheck, hb]
        · have hn : n < 2 := by omega
          simp [pntCheck, hn]
      · have hn : n < cutoff k := by omega
        simp [pntCheck, hn]
    · have hz : k = 0 := by omega
      simp [pntCheck, hz]

/-- The finite-ceiling formulation needed before using QF induction.
    For fixed X, allUpTo compresses every n<=X into one Boolean.
    Taking X=n recovers the external unbounded statement without inducting
    on a formula containing an unbounded quantifier over n. -/
theorem finiteCeilings_iff (cutoff : Nat → Nat) :
    (∀ k X, allUpTo (pntCheck cutoff k) X = true) ↔
      IsPNTModulus cutoff := by
  rw [← pntCheck_iff]
  constructor
  · intro h k n
    exact (allUpTo_iff _ _).mp (h k n) n (Nat.le_refl n)
  · intro h k X
    exact (allUpTo_iff _ _).mpr (fun n _ => h k n)

/-!
Remaining obligations, in dependency order:

1. Identify primeB with standard primality and prove all numerical functions
   above primitive recursive by explicit codes in ConciseIPRA.PR.
2. Prove exactness of the divisions D(n)/j and the harmonic interval bound.
3. Formalize the finite Selberg estimates and quantitative contraction in
   the article, with a fixed finite ceiling X at every induction.
4. Prove ArithmeticPNT, i.e. IsPNTModulus pntModulus. The explicit modulus
   is defined above, but no such proof is supplied in this outline.
5. Build the stronger, object-level certificate
   Prf PRAAx [] (universalCheck compiledCheck) in ObjectTarget.lean.
6. Derive conventional real-analytic PNT in ambient Mathlib as a semantic
   corollary. If the rational error is <=1/(2k) and n>=2k, its error from
   replacing the harmonic surrogate by log is at most 1/n<=1/(2k).

Neither a proof of Primrec alone nor a Mathlib proof with Real.log proves
object-level iPRA derivability. These are separate obligations.
-/

end ConstructivePNT

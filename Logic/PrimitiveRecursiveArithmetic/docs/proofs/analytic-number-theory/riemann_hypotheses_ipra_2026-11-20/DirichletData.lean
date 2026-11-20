import Init

/-!
Finite arithmetic data for the Riemann and Dirichlet hypotheses.
The supplementary Mertens formulations use the absolute values of these integer sums.
Every loop here has a bound supplied at entry. No factorization oracle or
complex character values occur in evaluation.
-/
namespace RHData

/-- Conjunction over the natural numbers strictly below the bound. -/
def allBelow (test : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => allBelow test k && test k

/-- Trial division by all integers in [2,p). -/
def primeTest (p : Nat) : Bool :=
  decide (2 ≤ p) && allBelow (fun d => decide (d < 2) || (p % d != 0)) p

/-- The local factor at a prime is 1, -1, or 0 according to its multiplicity. -/
def mobiusStep (n p : Nat) (acc : Int) : Int :=
  if primeTest p && (n % p == 0) then
    if n % (p * p) == 0 then 0 else -acc
  else acc

def mobiusProduct (n : Nat) : Nat → Int
  | 0 => 1
  | k + 1 => mobiusStep n (k + 1) (mobiusProduct n k)

/-- The usual Möbius function, totalized by μ(0)=0. -/
def mobius (n : Nat) : Int :=
  if n == 0 then 0 else mobiusProduct n n

/-- A canonical unit residue; for q=1 its sole representative is 0. -/
def reducedClass (q a : Nat) : Bool :=
  decide (0 < q) && decide (a < q) && (Nat.gcd a q == 1)

/-- Sum of μ(n) for 1 ≤ n ≤ x and n mod q = a. -/
def progressionMertens (q a : Nat) : Nat → Int
  | 0 => 0
  | x + 1 =>
    progressionMertens q a x + (if (x + 1) % q = a then mobius (x + 1) else 0)

/-- Mertens' function is the one progression modulo 1. -/
def mertens (x : Nat) : Int := progressionMertens 1 0 x

theorem reduced_one_zero : reducedClass 1 0 = true := by decide

theorem progression_hit (q a x : Nat) (h : (x + 1) % q = a) :
    progressionMertens q a (x + 1) = progressionMertens q a x + mobius (x + 1) := by
  simp [progressionMertens, h]

theorem progression_miss (q a x : Nat) (h : (x + 1) % q ≠ a) :
    progressionMertens q a (x + 1) = progressionMertens q a x := by
  simp [progressionMertens, h]

theorem mertens_succ (x : Nat) : mertens (x + 1) = mertens x + mobius (x + 1) := by
  exact progression_hit 1 0 x (Nat.mod_one _)

example : mobius 1 = 1 := by decide
example : mobius 4 = 0 := by decide
example : mobius 6 = 1 := by decide
example : mobius 7 = -1 := by decide
example : mertens 10 = -1 := by decide
example : progressionMertens 3 1 10 = 1 := by decide

end RHData

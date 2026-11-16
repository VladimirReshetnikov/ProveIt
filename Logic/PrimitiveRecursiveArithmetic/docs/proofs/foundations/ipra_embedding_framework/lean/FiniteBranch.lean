import Std

/-!
# Executable finite core for a separated simple branch

This file defines exact finite algorithms and records the outstanding proof
targets.  The structure `KernelGoals` is a specification: no instance of it is
asserted.  The small examples at the end are kernel-checked computations.
Neither these computations nor compilation establish an object-language iPRA
derivation.  The companion chapter supplies the mathematical proofs and the
outline describes the remaining arithmetization work.  The axiom audit for
these computations includes propext, Classical.choice, and Quot.sound via
the imported rational/finite-container infrastructure.  These metatheory
dependencies must not be confused with the intended intuitionistic arithmetic
proofs after translation to signed-integer/positive-denominator codes.
-/

namespace IPRAEmbedding.FiniteBranch

structure GQ where
  re : Rat
  im : Rat
  deriving Repr, DecidableEq, Inhabited

def zero : GQ := ⟨0, 0⟩
def one : GQ := ⟨1, 0⟩
def real (a : Rat) : GQ := ⟨a, 0⟩
def add (a b : GQ) : GQ := ⟨a.re + b.re, a.im + b.im⟩
def neg (a : GQ) : GQ := ⟨-a.re, -a.im⟩
def sub (a b : GQ) : GQ := add a (neg b)
def mul (a b : GQ) : GQ :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def ratAbs (a : Rat) : Rat := if a < 0 then -a else a
def norm1 (a : GQ) : Rat := ratAbs a.re + ratAbs a.im

abbrev Poly := Array GQ

def coeff (u : Poly) (k : Nat) : GQ := u[k]?.getD zero
def tabulate (K : Nat) (f : Nat → GQ) : Poly :=
  ((List.range (K + 1)).map f).toArray
def zeroPoly (K : Nat) : Poly := tabulate K (fun _ => zero)
def onePoly (K : Nat) : Poly :=
  tabulate K (fun k => if k = 0 then one else zero)
def polyAdd (K : Nat) (u v : Poly) : Poly :=
  tabulate K (fun k => add (coeff u k) (coeff v k))
def polySub (K : Nat) (u v : Poly) : Poly :=
  tabulate K (fun k => sub (coeff u k) (coeff v k))
def polyMul (K : Nat) (u v : Poly) : Poly :=
  tabulate K fun k =>
    (List.range (k + 1)).foldl
      (fun acc i => add acc (mul (coeff u i) (coeff v (k - i)))) zero
def polyPow (K : Nat) (u : Poly) : Nat → Poly
  | 0 => onePoly K
  | n + 1 => polyMul K (polyPow K u n) u

structure Term where
  xPower : Nat
  zPower : Nat
  value : GQ
  deriving Repr, DecidableEq, Inhabited

abbrev Bivariate := Array Term

def shiftScale (K i : Nat) (a : GQ) (u : Poly) : Poly :=
  tabulate K fun k => if i ≤ k then mul a (coeff u (k - i)) else zero

/-- Evaluate Q(X,U), retaining coefficients only through degree K. -/
def substitute (K : Nat) (q : Bivariate) (u : Poly) : Poly :=
  q.foldl (fun acc t =>
    polyAdd K acc
      (shiftScale K t.xPower t.value (polyPow K u t.zPower)))
    (zeroPoly K)

def iterate (K : Nat) (q : Bivariate) : Nat → Poly
  | 0 => zeroPoly K
  | n + 1 => substitute K q (iterate K q n)

/-- The kth stabilized coefficient is computed with exactly k iterations. -/
def branchCoeff (q : Bivariate) (k : Nat) : GQ :=
  coeff (iterate k q k) k

/-- S_K; the stabilization theorem identifies it with the coefficient prefix. -/
def partialSum (q : Bivariate) (K : Nat) : Poly := iterate K q K

def weightedNorm (r : Rat) (u : Poly) : Rat :=
  (List.range u.size).foldl
    (fun acc k => acc + norm1 (coeff u k) * r ^ k) 0

def evaluate (u : Poly) (x : GQ) : GQ :=
  u.toList.reverse.foldl (fun acc a => add a (mul x acc)) zero

def coeffMajorant (q : Bivariate) : Rat :=
  q.foldl (fun acc t => acc + norm1 t.value) 0

def admissible (D : Nat) (B : Rat) (q : Bivariate) : Prop :=
  2 ≤ D ∧ 1 ≤ B ∧ coeffMajorant q ≤ B ∧
  (∀ t ∈ q.toList, t.xPower + t.zPower ≤ D) ∧
  (∀ t ∈ q.toList,
     (t.xPower = 0 ∧ t.zPower ≤ 1) → t.value = zero)

def branchS (D : Nat) (B : Rat) : Rat := 1 / (4 * D * B)
def branchR (D : Nat) (B : Rat) : Rat := 1 / (16 * D * B * B)

/-!
These are exact targets, not axioms.  Filling the fields of `KernelGoals`
requires proofs of finite coefficient convolution, truncation, factorization,
and the rational inequalities from the paper.  `residualLow` deliberately
checks the low coefficients only; the full residual estimate must evaluate
the untruncated bivariate polynomial, not the degree-K truncation.
-/
structure KernelGoals : Prop where
  invariant : ∀ (D : Nat) (B : Rat) (q : Bivariate),
    admissible D B q → ∀ K n,
      weightedNorm (branchR D B) (iterate K q n) ≤ branchS D B
  stable : ∀ (D : Nat) (B : Rat) (q : Bivariate),
    admissible D B q → ∀ K k n,
      k ≤ K → k ≤ n →
      coeff (iterate K q n) k = branchCoeff q k
  residualLow : ∀ (D : Nat) (B : Rat) (q : Bivariate),
    admissible D B q → ∀ K k,
      k ≤ K →
      coeff (substitute K q (partialSum q K)) k =
        coeff (partialSum q K) k

/-- Q(X,Z) = (X - Z^2)/2, giving sqrt(1+X)-1 near zero. -/
def sqrtQ : Bivariate :=
  #[⟨1, 0, real (1/2)⟩, ⟨0, 2, real (-1/2)⟩]

theorem sqrt_coeff_0 : branchCoeff sqrtQ 0 = zero := by decide +kernel
theorem sqrt_coeff_1 : branchCoeff sqrtQ 1 = real (1/2) := by decide +kernel
theorem sqrt_coeff_2 : branchCoeff sqrtQ 2 = real (-1/8) := by decide +kernel
theorem sqrt_coeff_3 : branchCoeff sqrtQ 3 = real (1/16) := by decide +kernel
theorem sqrt_coeff_4 : branchCoeff sqrtQ 4 = real (-5/128) := by decide +kernel

#print axioms sqrt_coeff_0
#print axioms sqrt_coeff_1
#print axioms sqrt_coeff_2
#print axioms sqrt_coeff_3
#print axioms sqrt_coeff_4

end IPRAEmbedding.FiniteBranch

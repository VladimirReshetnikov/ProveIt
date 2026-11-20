import Std

/-!
# Metric topology: checked semantic interfaces and explicit implementation targets

This file is self-contained Lean 4.32.0 code, with no `sorry` and no declared
axioms.  It does NOT assert that arbitrary Lean functions are primitive
recursive, and does NOT contain an encoded iPRA derivation of the chapter.

The `PrecisionSpace` interface is the finite-precision analogue of metric
inequalities d(x,y) <= 2^(-k).  Its product construction is kernel checked.
For the actual iPRA endpoint, instantiate all fields with the fixed PR
procedures and compile the rational loop invariants described below.
-/

namespace GeneralTopologyIPRA.Metric

/-- Positive-denominator rational syntax; no quotient or order decision on reals. -/
structure RatCode where
  num : Int
  den : Nat
  den_pos : 0 < den

def RatCode.le (a b : RatCode) : Prop :=
  a.num * Int.ofNat b.den <= b.num * Int.ofNat a.den

def RatCode.eqv (a b : RatCode) : Prop :=
  a.num * Int.ofNat b.den = b.num * Int.ofNat a.den

instance (a b : RatCode) : Decidable (a.le b) := inferInstanceAs
  (Decidable (a.num * Int.ofNat b.den <= b.num * Int.ofNat a.den))

instance (a b : RatCode) : Decidable (a.eqv b) := inferInstanceAs
  (Decidable (a.num * Int.ofNat b.den = b.num * Int.ofNat a.den))

def RatCode.add (a b : RatCode) : RatCode :=
  { num := a.num * Int.ofNat b.den + b.num * Int.ofNat a.den
    den := a.den * b.den
    den_pos := Nat.mul_pos a.den_pos b.den_pos }

def RatCode.mul (a b : RatCode) : RatCode :=
  { num := a.num * b.num
    den := a.den * b.den
    den_pos := Nat.mul_pos a.den_pos b.den_pos }

def RatCode.neg (a : RatCode) : RatCode :=
  { num := -a.num, den := a.den, den_pos := a.den_pos }

def RatCode.abs (a : RatCode) : RatCode :=
  { num := Int.ofNat a.num.natAbs, den := a.den, den_pos := a.den_pos }

def RatCode.sub (a b : RatCode) : RatCode := a.add b.neg

def dyadic (k : Nat) : RatCode :=
  { num := 1, den := 2 ^ k, den_pos := Nat.pow_pos (by omega) }

/-- A fixed approximation procedure, with its finite Cauchy tests. -/
structure RealName where
  approx : Nat → RatCode
  regular : ∀ k l,
    ((approx k).sub (approx l)).abs.le ((dyadic k).add (dyadic l))

/-- This is a Prop-valued interface, not a decision procedure for real comparison. -/
structure PrecisionSpace (α : Type) where
  close : Nat → α → α → Prop
  refl : ∀ k x, close k x x
  symm : ∀ {k x y}, close k x y → close k y x
  mono : ∀ {k l x y}, k ≤ l → close l x y → close k x y
  triangle : ∀ {k x y z}, close (k+1) x y → close (k+1) y z → close k x z
  separated : ∀ {x y}, (∀ k, close k x y) → x = y

/-- Coarse product entourages: first k+1 coordinates, all at precision k.
They generate the same uniformity as the chapter's weighted sum, with
explicit shifts.  This definition is not itself the numerical sum. -/
def productClose {α : Nat → Type} (S : ∀ i, PrecisionSpace (α i))
    (k : Nat) (x y : ∀ i, α i) : Prop :=
  ∀ i, i ≤ k → (S i).close k (x i) (y i)

def productSpace {α : Nat → Type} (S : ∀ i, PrecisionSpace (α i)) :
    PrecisionSpace (∀ i, α i) where
  close := productClose S
  refl := by
    intro k x i _
    exact (S i).refl k (x i)
  symm := by
    intro k x y h i hi
    exact (S i).symm (h i hi)
  mono := by
    intro k l x y hkl h i hi
    exact (S i).mono hkl (h i (Nat.le_trans hi hkl))
  triangle := by
    intro k x y z hxy hyz i hi
    have hik : i ≤ k+1 := by omega
    exact (S i).triangle (hxy i hik) (hyz i hik)
  separated := by
    intro x y h
    funext i
    apply (S i).separated
    intro k
    have hi : i ≤ i+k := by omega
    have hk : k ≤ i+k := by omega
    exact (S i).mono hk (h (i+k) i hi)

/-- Supplied modulus, without an existential choice of modulus. -/
def UniformWith {α β : Type} (S : PrecisionSpace α) (T : PrecisionSpace β)
    (f : α → β) (μ : Nat → Nat) : Prop :=
  ∀ k x y, S.close (μ k) x y → T.close k (f x) (f y)

theorem uniform_id {α : Type} (S : PrecisionSpace α) :
    UniformWith S S id id := by
  intro k x y h
  exact h

theorem uniform_comp {α β γ : Type}
    (S : PrecisionSpace α) (T : PrecisionSpace β) (U : PrecisionSpace γ)
    (f : α → β) (g : β → γ) (μ ν : Nat → Nat)
    (hf : UniformWith S T f μ) (hg : UniformWith T U g ν) :
    UniformWith S U (fun x => g (f x)) (fun k => μ (ν k)) := by
  intro k x y h
  exact hg k (f x) (f y) (hf (ν k) x y h)

/-- A net includes a selector.  Arbitrary finite existential witnesses are
not converted to a selector by classical choice. -/
structure FiniteNet {α : Type} (S : PrecisionSpace α) (k : Nat) where
  size : Nat
  point : Fin size → α
  pick : α → Fin size
  covers : ∀ x, S.close k x (point (pick x))

theorem image_net_cover {α β : Type}
    (S : PrecisionSpace α) (T : PrecisionSpace β)
    (f : α → β) (μ : Nat → Nat)
    (hf : UniformWith S T f μ) (k : Nat) (net : FiniteNet S (μ k)) :
    ∀ x, T.close k (f x) (f (net.point (net.pick x))) := by
  intro x
  exact hf k x (net.point (net.pick x)) (net.covers x)

/-- An explicitly supplied Cauchy modulus. -/
def CauchyWith {α : Type} (S : PrecisionSpace α)
    (x : Nat → α) (m : Nat → Nat) : Prop :=
  ∀ k n l, m k ≤ n → m k ≤ l → S.close k (x n) (x l)

/-- Explicit convergence data, not bare existence of a limit. -/
def ConvergesWith {α : Type} (S : PrecisionSpace α)
    (x : Nat → α) (z : α) (c : Nat → Nat) : Prop :=
  ∀ k n, c k ≤ n → S.close k (x n) z

theorem limit_unique {α : Type} (S : PrecisionSpace α)
    (x : Nat → α) (z w : α) (c d : Nat → Nat)
    (hz : ConvergesWith S x z c) (hw : ConvergesWith S x w d) :
    z = w := by
  apply S.separated
  intro k
  let n := max (c (k+1)) (d (k+1))
  have hz' : S.close (k+1) (x n) z :=
    hz (k+1) n (Nat.le_max_left _ _)
  have hw' : S.close (k+1) (x n) w :=
    hw (k+1) n (Nat.le_max_right _ _)
  exact S.triangle (S.symm hz') hw'

/-- Finite requests to a weighted product at demanded precision k only need
k+2 coordinates, each requested at precision k+2. -/
def productCoordinateCount (k : Nat) : Nat := k + 2

def productCoordinatePrecision (k : Nat) : Nat := k + 2

def inverseEmbeddingExponent (locator : Nat → Nat) (k : Nat) : Nat :=
  locator (k+2) + k + 2

/-- The actual proof obligations below are intentionally data fields, not
unproved global theorem declarations.  A completed rational implementation
must construct such records from the chapter's algorithms. -/
structure ProductApproximationCertificate
    (partialSum : Nat → RatCode) (distance : RealName) where
  tailBound : ∀ n k,
    ((distance.approx k).sub (partialSum n)).abs.le
      ((dyadic n).add (dyadic k))

structure ApproximateMaximumCertificate (values : Nat → RealName)
    (candidate : Nat) (precision : Nat) where
  /-- Finite-demand upper bound, with the two approximation errors included. -/
  bound : ∀ x t,
    (values x).approx t |>.le
      (((values candidate).approx t).add
        ((dyadic precision).add ((dyadic t).add (dyadic t))))

/-
IMPLEMENTATION TARGETS (not claimed as checked theorems in this file)

1. Weighted geometric tail:
   for N <= L, sum_{i=N}^{L-1} 2^(-i-1) <= 2^(-N).
   Prove after multiplying by the positive denominator 2^L.

2. Countable net algorithm:
   N := k+2; enumerate product_{i<N} Fin(M_i(k+2)); use base points after N.
   Verify each selected coordinate inequality and add the tail bound.

3. Urysohn quotient:
   a,b >= 0; a+b >= delta; |a-a'|,|b-b'| <= d.
   Cross multiply denominators to prove
   |a/(a+b)-a'/(a'+b')| <= d/delta.
   Approximate division only after proving the numerical denominator >= delta/2.

4. Hilbert-cube inverse:
   i := locator(x,k+2); u_i := min(1,d(x,p_i));
   D < 2^(-(i+k+2)) implies |u_i(x)-u_i(y)| < 2^(-k-1),
   hence d(x,y) < 2^(-k).  Supply the locator; do not search over undecidable
   comparisons with real distances.

5. Uniform metric:
   eta := 2^(-k-3); net at max(mu_f(k+4),mu_g(k+4));
   Q := max rational distance approximations on that net.
   Prove Q-eta <= sup <= Q+2*eta as finite lower-witness / upper-bound tests.

6. Compact-open neighborhoods:
   use overlapping closed dyadic boxes centered at grid points, radius h.
   Approximate coordinates within h/4 and round rationally to select a box.
   Do not replace this by deciding on which side of a dyadic boundary an
   arbitrary named real lies.

7. iPRA endpoint:
   give PR syntax for every fixed procedure; formalize the QF loop invariants;
   compile to an explicit repository proof-predicate witness.  This file's
   semantic functions and checked Lean propositions do not supply that step.
-/


end GeneralTopologyIPRA.Metric

-- Complete theorem axiom audit for this standalone file.
#print axioms GeneralTopologyIPRA.Metric.uniform_id
#print axioms GeneralTopologyIPRA.Metric.uniform_comp
#print axioms GeneralTopologyIPRA.Metric.image_net_cover
#print axioms GeneralTopologyIPRA.Metric.limit_unique

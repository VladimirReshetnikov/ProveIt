import Mathlib

/-!
# Definitions for LeSaulnier--Vijay (2011)

This file formalizes the auxiliary language used in Timothy D. LeSaulnier and
Sujith Vijay, "On permutations avoiding arithmetic progressions", *Discrete
Mathematics* 311 (2011), 205--207.

A permutation of an arbitrary set `S : Set Nat` is represented by an injective
natural-number rank on `S`.  Sorting by these ranks gives an ordinary finite
permutation when `S` is finite and a one-sided enumeration when `S` is
infinite.  This avoids having separate definitions for the two cases.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace LeanProofs.LeSaulnierVijay2011

/-! ## Arithmetic progressions in permutations -/

/-- The values `x 0, ..., x (k - 1)` form a nonconstant arithmetic
progression whose signed common difference satisfies `stepProperty`.

The common difference lives in `Int` so that decreasing progressions are
represented without truncated natural-number subtraction. -/
def IsArithmeticProgressionWithStep {k : Nat} (stepProperty : Int -> Prop)
    (x : Fin k -> Nat) : Prop :=
  exists a d : Int, d != 0 /\ stepProperty d /\
    forall i, (x i : Int) = a + ((i : Nat) : Int) * d

/-- A nonconstant arithmetic progression of natural numbers. -/
def IsArithmeticProgression {k : Nat} (x : Fin k -> Nat) : Prop :=
  IsArithmeticProgressionWithStep (fun _ => True) x

/-- A nonconstant arithmetic progression with odd (possibly negative) common
difference. -/
def IsOddArithmeticProgression {k : Nat} (x : Fin k -> Nat) : Prop :=
  IsArithmeticProgressionWithStep Odd x

/-- A sequence contains a `k`-term arithmetic progression as a subsequence. -/
def HasAPSubsequence {I : Type*} [LinearOrder I] (k : Nat) (sequence : I -> Nat) : Prop :=
  exists indices : Fin k -> I, StrictMono indices /\
    IsArithmeticProgression (fun i => sequence (indices i))

/-- A sequence contains a `k`-term arithmetic progression with odd common
difference as a subsequence. -/
def HasOddAPSubsequence {I : Type*} [LinearOrder I]
    (k : Nat) (sequence : I -> Nat) : Prop :=
  exists indices : Fin k -> I, StrictMono indices /\
    IsOddArithmeticProgression (fun i => sequence (indices i))

/-- `rank` represents a permutation of `S` when distinct members of `S` have
distinct positions.  Unused ranks are harmless: deleting the gaps does not
change the induced order. -/
def IsPermutationRanking (S : Set Nat) (rank : Nat -> Nat) : Prop :=
  Set.InjOn rank S

/-- Two rankings induce the same permutation order on `S`. -/
def SameOrderOn (S : Set Nat) (rank₁ rank₂ : Nat -> Nat) : Prop :=
  forall x, x ∈ S -> forall y, y ∈ S ->
    (rank₁ x < rank₁ y <-> rank₂ x < rank₂ y)

/-- A `k`-term arithmetic progression occurs in the order induced by `rank`. -/
def HasAPInRanking (k : Nat) (S : Set Nat) (rank : Nat -> Nat) : Prop :=
  exists x : Fin k -> Nat, (forall i, x i ∈ S) /\
    StrictMono (fun i => rank (x i)) /\ IsArithmeticProgression x

/-- A `k`-term arithmetic progression with odd common difference occurs in
the order induced by `rank`. -/
def HasOddAPInRanking (k : Nat) (S : Set Nat) (rank : Nat -> Nat) : Prop :=
  exists x : Fin k -> Nat, (forall i, x i ∈ S) /\
    StrictMono (fun i => rank (x i)) /\ IsOddArithmeticProgression x

/-- `rank` gives a `k`-avoiding permutation of `S`. -/
def IsKAvoidingRanking (k : Nat) (S : Set Nat) (rank : Nat -> Nat) : Prop :=
  IsPermutationRanking S rank /\ ¬ HasAPInRanking k S rank

/-- `rank` gives a permutation of `S` avoiding `k`-term progressions with odd
common difference. -/
def IsOddKAvoidingRanking (k : Nat) (S : Set Nat) (rank : Nat -> Nat) : Prop :=
  IsPermutationRanking S rank /\ ¬ HasOddAPInRanking k S rank

/-- A set is `k`-avoidable if some permutation of it avoids all `k`-term
arithmetic progressions. -/
def IsKAvoidable (k : Nat) (S : Set Nat) : Prop :=
  exists rank : Nat -> Nat, IsKAvoidingRanking k S rank

/-- A set has a permutation avoiding all `k`-term arithmetic progressions
with odd common difference. -/
def IsOddKAvoidable (k : Nat) (S : Set Nat) : Prop :=
  exists rank : Nat -> Nat, IsOddKAvoidingRanking k S rank

/-- The set of positive integers, represented inside `Nat`. -/
def positiveIntegers : Set Nat :=
  Set.Ioi 0

/-! ## Finite permutations and the counting function `M` -/

/-- The entry in position `i` of a permutation of `{1, ..., n}`. -/
def finitePermutationValue {n : Nat} (sigma : Equiv.Perm (Fin n)) (i : Fin n) : Nat :=
  (sigma i : Nat) + 1

/-- A permutation of `{1, ..., n}` is `k`-avoiding. -/
def IsFiniteKAvoiding {n : Nat} (k : Nat) (sigma : Equiv.Perm (Fin n)) : Prop :=
  ¬ HasAPSubsequence k (finitePermutationValue sigma)

/-- A permutation of `{1, ..., n}` contains no `k`-term AP with odd common
difference. -/
def IsFiniteOddKAvoiding {n : Nat} (k : Nat) (sigma : Equiv.Perm (Fin n)) : Prop :=
  ¬ HasOddAPSubsequence k (finitePermutationValue sigma)

/-- The paper's `M(n)`: the number of 3-avoiding permutations of
`{1, ..., n}`. -/
noncomputable def M (n : Nat) : Nat := by
  classical
  exact Fintype.card {sigma : Equiv.Perm (Fin n) // IsFiniteKAvoiding 3 sigma}

/-- The even members of `{1, ..., 2n}` used in the parity construction for
the recurrences for `M`. -/
def evenIntervalPart (n : Nat) : Finset Nat :=
  (Finset.Icc 1 (2 * n)).filter Even

/-- The odd members of `{1, ..., 2n}` used in the parity construction for
the recurrences for `M`. -/
def oddIntervalPart (n : Nat) : Finset Nat :=
  (Finset.Icc 1 (2 * n)).filter Odd

/-! ## Density parameters -/

/-- `S(n) = |S ∩ [1,n]|`. -/
noncomputable def countingFunction (S : Set Nat) (n : Nat) : Nat := by
  classical
  exact ((Finset.Icc 1 n).filter fun m => m ∈ S).card

/-- The normalized counting function `S(n) / n`. -/
def densityRatio (S : Set Nat) (n : Nat) : Real :=
  countingFunction S n / (n : Real)

/-- The upper asymptotic density, expressed as the infimum of all eventual
upper bounds for `S(n) / n`. -/
noncomputable def upperDensity (S : Set Nat) : Real :=
  sInf {b : Real | exists N : Nat, forall n : Nat, N <= n -> densityRatio S n <= b}

/-- The lower asymptotic density, expressed as the supremum of all eventual
lower bounds for `S(n) / n`. -/
noncomputable def lowerDensity (S : Set Nat) : Real :=
  sSup {b : Real | exists N : Nat, forall n : Nat, N <= n -> b <= densityRatio S n}

/-- The supremum of the upper densities of `k`-avoidable sets. -/
noncomputable def alpha (k : Nat) : Real :=
  sSup {d : Real | exists S : Set Nat, S ⊆ positiveIntegers /\
    IsKAvoidable k S /\ upperDensity S = d}

/-- The supremum of the lower densities of `k`-avoidable sets. -/
noncomputable def beta (k : Nat) : Real :=
  sSup {d : Real | exists S : Set Nat, S ⊆ positiveIntegers /\
    IsKAvoidable k S /\ lowerDensity S = d}

/-! ## Sets used in the constructions -/

/-- The block `S_i^(a) = {a^(2i), ..., a^(2i+1)}` from Theorem 3. -/
def geometricBlock (a i : Nat) : Finset Nat :=
  Finset.Icc (a ^ (2 * i)) (a ^ (2 * i + 1))

/-- The set `S^(a)`, the union of the even-indexed geometric blocks. -/
def geometricSet (a : Nat) : Set Nat :=
  {n | exists i : Nat, n ∈ geometricBlock a i}

/-- Every entry of an earlier block precedes every entry of a later block in
the order induced by `rank`. -/
def BlocksInOrder (blocks : Nat -> Finset Nat) (rank : Nat -> Nat) : Prop :=
  forall i j : Nat, i < j -> forall x, x ∈ blocks i ->
    forall y, y ∈ blocks j -> rank x < rank y

/-- The upper endpoint `q_k` of the `k`th block in the 3-avoiding density
construction. -/
def q : Nat -> Nat
  | 0 => 2
  | k + 1 => 3 * q k - 1

/-- The lower endpoint `p_k` of the `k`th block in the 3-avoiding density
construction. -/
def p : Nat -> Nat
  | 0 => 1
  | k + 1 => 2 * q k

/-- The interval `T_k = {p_k, ..., q_k}`. -/
def TBlock (k : Nat) : Finset Nat :=
  Finset.Icc (p k) (q k)

/-- The set `T`, the union of all of the intervals `T_k`. -/
def TSet : Set Nat :=
  {n | exists k : Nat, n ∈ TBlock k}

/-- The even block permuted by `sigma_i` in the construction for Theorem 2. -/
def theorem2EvenBlock (i : Nat) : Finset Nat := by
  classical
  exact (Finset.Icc ((4 ^ i + 2) / 3) ((4 ^ (i + 1) - 4) / 3)).filter Even

/-- The odd block permuted by `pi_i` in the construction for Theorem 2. -/
def theorem2OddBlock (i : Nat) : Finset Nat := by
  classical
  exact (Finset.Icc ((4 ^ i + 2) / 6) ((4 ^ (i + 1) - 10) / 6)).filter Odd

end LeanProofs.LeSaulnierVijay2011

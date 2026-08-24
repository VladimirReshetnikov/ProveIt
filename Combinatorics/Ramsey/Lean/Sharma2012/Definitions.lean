import Mathlib

/-!
# Definitions for Sharma's progression-free permutations

This file formalizes the auxiliary language in Arun Sharma,
"Enumerating permutations that avoid three term arithmetic progressions",
*Electronic Journal of Combinatorics* 16 (2009), R63.

The paper treats a permutation interchangeably as a word and as a linear
ordering.  We consequently use lists for its structural definitions and use
permutations of `Fin n` only when a finite type is needed to define `theta n`.
-/

set_option autoImplicit false

noncomputable section

open Finset Filter

namespace LeanProofs.Sharma2012

/-! ## Permutations and three-term progressions -/

/-- The paper's segment `[n] = {1, ..., n}`. -/
def segment (n : Nat) : Finset Nat :=
  Finset.Icc 1 n

/-- A list contains every member of a finite set exactly once. -/
def Permutes (S : Finset Nat) (word : List Nat) : Prop :=
  word.Nodup /\ word.toFinset = S

/-- A list contains every member of `[n]` exactly once. -/
def PermutesSegment (n : Nat) (word : List Nat) : Prop :=
  Permutes (segment n) word

/-- `x` occurs strictly to the left of `y` in a word. -/
def OccursLeftOf (word : List Nat) (x y : Nat) : Prop :=
  exists i j : Nat, i < j /\ word[i]? = some x /\ word[j]? = some y

/-- `x` occurs immediately to the left of `y` in a word. -/
def ImmediatelyLeftOf (word : List Nat) (x y : Nat) : Prop :=
  exists i : Nat, word[i]? = some x /\ word[i + 1]? = some y

/-- The first entry of a word is `x`. -/
def StartsWith (word : List Nat) (x : Nat) : Prop :=
  word.head? = some x

/-- The final entry of a word is `x`. -/
def EndsWith (word : List Nat) (x : Nat) : Prop :=
  word.getLast? = some x

/-- A word contains a `k`-term arithmetic progression as a subsequence.

The strictly monotone index map records subsequence order.  The two branches
record an increasing or decreasing progression with positive common
difference, exactly as in the Introduction.
-/
def ContainsAP (k : Nat) (word : List Nat) : Prop :=
  exists indices : Fin k -> Nat, StrictMono indices /\
    exists a d : Nat, 0 < d /\
      ((forall i : Fin k,
          word[indices i]? = some (a + (i : Nat) * d)) \/
       (forall i : Fin k,
          word[indices i]? = some (a + (k - 1 - (i : Nat)) * d)))

/-- A word is `k`-free. -/
def KFree (k : Nat) (word : List Nat) : Prop :=
  ¬ ContainsAP k word

/-- A word contains a three-term arithmetic progression. -/
def ContainsThreeAP (word : List Nat) : Prop :=
  ContainsAP 3 word

/-- A word avoids three-term arithmetic progressions. -/
def ThreeFree (word : List Nat) : Prop :=
  KFree 3 word

/-- A `Theta` word on a finite set. -/
def IsThetaOn (S : Finset Nat) (word : List Nat) : Prop :=
  Permutes S word /\ ThreeFree word

/-- A `Theta` word is a three-free permutation of `[n]`. -/
def IsTheta (n : Nat) (word : List Nat) : Prop :=
  IsThetaOn (segment n) word

/-- The word on `[n]` represented by a permutation of `Fin n`. -/
def permutationWord {n : Nat} (sigma : Equiv.Perm (Fin n)) : List Nat :=
  List.ofFn fun i => (sigma i : Nat) + 1

/-- A finite permutation is progression-free. -/
def IsThetaPermutation {n : Nat} (sigma : Equiv.Perm (Fin n)) : Prop :=
  ThreeFree (permutationWord sigma)

/-- `Theta(n)`, as a finite type. -/
abbrev ThetaPermutation (n : Nat) :=
  {sigma : Equiv.Perm (Fin n) // IsThetaPermutation sigma}

/-- The number `theta(n)` of three-free permutations of `[n]`. -/
noncomputable def theta (n : Nat) : Nat :=
  by
    classical
    exact Fintype.card (ThetaPermutation n)

/-! ## Notation 1.1 and Definitions 2.1--2.3 -/

/-- The affine image `(a P + b) / c` from Notation 1.1.

Rational values accurately record the notation without silently imposing a
divisibility hypothesis that the paper leaves implicit.
-/
noncomputable def affineImage (a b c : Int) (P : Finset Int) : Finset Rat := by
  classical
  exact P.image fun x => (a * x + b : Rat) / c

/-- The entrywise affine image `(a alpha + b) / c` from Notation 1.1. -/
def affineWord (a b c : Int) (alpha : List Int) : List Rat :=
  alpha.map fun x => (a * x + b : Rat) / c

/-- The concatenated word `(alpha, beta)` from Notation 1.1. -/
def concatenate {X : Type*} (alpha beta : List X) : List X :=
  alpha ++ beta

/-- The trace of a word on entries satisfying `p`. -/
def trace (p : Nat -> Bool) (word : List Nat) : List Nat :=
  word.filter p

/-- The trace on odd entries. -/
def oddTrace (word : List Nat) : List Nat :=
  trace (fun x => decide (Odd x)) word

/-- The trace on even entries. -/
def evenTrace (word : List Nat) : List Nat :=
  trace (fun x => decide (Even x)) word

/-- The complementary permutation `gamma*`, obtained by sending `x` to
`n + 1 - x`. -/
def complement (n : Nat) (word : List Nat) : List Nat :=
  word.map fun x => n + 1 - x

/-- The lower half `[1, floor(n/2)]` of `[n]`. -/
def lowerHalf (n : Nat) : Finset Nat :=
  Finset.Icc 1 (n / 2)

/-- The upper half `[floor(n/2) + 1, n]` of `[n]`. -/
def upperHalf (n : Nat) : Finset Nat :=
  Finset.Icc (n / 2 + 1) n

/-- Two entries lie in the same half of `[n]`. -/
def SameHalf (n x y : Nat) : Prop :=
  (x ∈ lowerHalf n /\ y ∈ lowerHalf n) \/
    (x ∈ upperHalf n /\ y ∈ upperHalf n)

/-- Definition 2.2: reversal of a permutation word. -/
def reversal (word : List Nat) : List Nat :=
  word.reverse

/-- Definition 2.3: the longest initial block lying in the same half as its
first entry. -/
noncomputable def prologue (n : Nat) (word : List Nat) : List Nat := by
  classical
  exact match word with
    | [] => []
    | x :: xs => x :: xs.takeWhile fun y => decide (SameHalf n x y)

/-- Definition 2.3: the epilogue is the prologue of the reversal. -/
noncomputable def epilogue (n : Nat) (word : List Nat) : List Nat :=
  prologue n (reversal word)

/-! ## Theta-12 words, interleavings, and commutation -/

/-- A word starts with an odd entry. -/
def StartsOdd (word : List Nat) : Prop :=
  exists x : Nat, StartsWith word x /\ Odd x

/-- A word starts with an even entry. -/
def StartsEven (word : List Nat) : Prop :=
  exists x : Nat, StartsWith word x /\ Even x

/-- Notation 2.1: a `Theta_12` permutation. -/
def IsTheta12 (n : Nat) (word : List Nat) : Prop :=
  IsTheta n word /\ StartsOdd word

/-- Notation 2.1: a `Theta_21` permutation. -/
def IsTheta21 (n : Nat) (word : List Nat) : Prop :=
  IsTheta n word /\ StartsEven word

/-- Definition 2.4: the finite interleaving class `gamma_o tensor gamma_e`.

Its members are encoded by permutations of `Fin n`, which makes the
cardinality assertions in Lemma 2.5 and Corollary 2.7.1 literal finite-set
cardinalities.
-/
noncomputable def interleavingClass (n : Nat) (gammaOdd gammaEven : List Nat) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter fun sigma =>
    let gamma := permutationWord sigma
    IsTheta12 n gamma /\ oddTrace gamma = gammaOdd /\ evenTrace gamma = gammaEven

/-- The even-first class `gamma_e tensor gamma_o`, defined similarly in
Definition 2.4. -/
noncomputable def reverseInterleavingClass
    (n : Nat) (gammaEven gammaOdd : List Nat) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter fun sigma =>
    let gamma := permutationWord sigma
    IsTheta21 n gamma /\ evenTrace gamma = gammaEven /\ oddTrace gamma = gammaOdd

/-- Definition 2.5: an odd `x` and even `y` commute if some `Theta_12`
permutation places `y` to the left of `x`. -/
def Commute (n x y : Nat) : Prop :=
  exists gamma : List Nat, IsTheta12 n gamma /\ OccursLeftOf gamma y x

/-- The paper's negative formulation: every `Theta_12` permutation places
`x` to the left of `y`. -/
def DoNotCommute (n x y : Nat) : Prop :=
  forall gamma : List Nat, IsTheta12 n gamma -> OccursLeftOf gamma x y

/-- The standing hypotheses introduced in Notation 2.2(3).  The explicit
`n >= 32` records the range announced immediately before Propositions
2.8--2.10 and used throughout their applications. -/
def StandingInterleavingHypotheses (n : Nat) (gamma : List Nat) : Prop :=
  32 <= n /\ IsTheta12 n gamma /\
    exists b1 c1 : Nat,
      EndsWith (oddTrace gamma) b1 /\ StartsWith (evenTrace gamma) c1 /\
      Commute n b1 c1 /\ b1 ∈ lowerHalf n /\ c1 ∈ upperHalf n

/-- Replace the two values `x` and `y` by one another.  Under the hypotheses
of Proposition 2.7 they are adjacent, so this is precisely their swap. -/
def swapValues (x y : Nat) (word : List Nat) : List Nat :=
  word.map fun z => if z = x then y else if z = y then x else z

/-- The word `(2 gamma, 2 gamma - 1)` used in Proposition 2.6. -/
def doubledEvenOdd (word : List Nat) : List Nat :=
  word.map (fun x => 2 * x) ++ word.map (fun x => 2 * x - 1)

/-! ## Congruence notation -/

/-- The first `k` entries of `word` are mutually congruent modulo `m`. -/
def PrefixCongruent (word : List Nat) (k m : Nat) : Prop :=
  k <= word.length /\
    forall i, i < k -> forall j, j < k -> forall x y : Nat,
      word[i]? = some x -> word[j]? = some y -> Nat.ModEq m x y

/-- Definition 2.6: the degree of binary congruence, i.e. the exponent of `2`
in the absolute difference.  Statements using it explicitly require distinct
arguments, as does the paper. -/
noncomputable def binaryCongruenceDegree (a b : Nat) : Nat :=
  (a.dist b).factorization 2

/-- The dyadic scale `q = 2^(floor(log_2 n) - 4)` from Notation 2.2.
The later results only use it for `n >= 32`, where no truncated subtraction
occurs in the exponent. -/
def dyadicQ (n : Nat) : Nat :=
  2 ^ (Nat.log 2 n - 4)

/-- The real `n`th-root growth rate of `theta`. -/
noncomputable def exponentialRate (n : Nat) : Real :=
  Real.rpow (theta n : Real) (n : Real)⁻¹

end LeanProofs.Sharma2012

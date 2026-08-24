import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.LiminfLimsup

/-!
# Definitions for Davis--Entringer--Graham--Simmons (1977)

This file formalizes the language used in J. A. Davis, R. C. Entringer,
R. L. Graham, and G. J. Simmons, "On permutations containing no long
arithmetic progressions", *Acta Arithmetica* 34 (1977), 81--90.

The paper numbers the positive integers from `1`.  Accordingly, finite
permutations are permutations of `Fin n` whose displayed value is shifted by
one, while infinite permutations take values in the subtype `PositiveNat`.
An arithmetic progression is represented in `Int`; allowing its nonzero
common difference to have either sign captures both increasing and decreasing
progressions with one definition.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Filter Finset

namespace LeanProofs.DavisEntringerGrahamSimmons1977

/-! ## Permutations and monotone arithmetic progressions -/

/-- The positive natural numbers, the set denoted `Z^+` in the paper. -/
abbrev PositiveNat := {n : Nat // 0 < n}

/-- A finite permutation of the paper's interval `[1,n]`.

The underlying `Fin n` value `j` represents the paper value `j + 1`.
-/
abbrev FinitePermutation (n : Nat) := Equiv.Perm (Fin n)

/-- A singly-infinite permutation of the positive integers. -/
abbrev SinglyInfinitePermutation := Nat ≃ PositiveNat

/-- A doubly-infinite permutation of the positive integers. -/
abbrev DoublyInfinitePermutation := Int ≃ PositiveNat

/-- A doubly-infinite permutation of all the integers, used in the last
concluding remark. -/
abbrev IntegerPermutation := Int ≃ Int

/-- A nonconstant arithmetic progression, written in its displayed order. -/
def IsArithmeticProgression {k : Nat} (x : Fin k -> Int) : Prop :=
  exists a d : Int, d != 0 /\ forall i, x i = a + (i : Nat) * d

/-- A sequence contains a monotone `k`-term arithmetic progression as a
subsequence.  The selected positions increase strictly.  The common
difference in `IsArithmeticProgression` may be positive or negative. -/
def HasMonotoneAP {I : Type*} [Preorder I] (x : I -> Int) (k : Nat) : Prop :=
  exists pos : Fin k -> I, StrictMono pos /\
    IsArithmeticProgression (fun i => x (pos i))

/-- The increasing-only version used by the stronger observation in Fact 3. -/
def HasIncreasingAP {I : Type*} [Preorder I] (x : I -> Int) (k : Nat) : Prop :=
  exists pos : Fin k -> I, StrictMono pos /\ exists a d : Int, 0 < d /\
    forall i, x (pos i) = a + (i : Nat) * d

/-- The integer-valued sequence displayed by a finite permutation. -/
def finitePermutationSequence {n : Nat} (p : FinitePermutation n) (i : Fin n) : Int :=
  (p i : Nat) + 1

/-- A finite permutation has no monotone `k`-term arithmetic progression. -/
def FiniteAPFree {n : Nat} (p : FinitePermutation n) (k : Nat) : Prop :=
  ¬ HasMonotoneAP (finitePermutationSequence p) k

/-- The paper's set `Mcal(n)` of 3-term-AP-free permutations of `[1,n]`. -/
def progressionFreePermutations (n : Nat) : Set (FinitePermutation n) :=
  {p | FiniteAPFree p 3}

/-- The paper's counting function `M(n)`. -/
noncomputable def M (n : Nat) : Nat := by
  classical
  exact Fintype.card {p : FinitePermutation n // FiniteAPFree p 3}

/-- The integer-valued sequence displayed by a singly-infinite permutation. -/
def singlyPermutationSequence (p : SinglyInfinitePermutation) (i : Nat) : Int :=
  (p i : Nat)

/-- The paper's set `Scal_k`. -/
def S (k : Nat) : Set SinglyInfinitePermutation :=
  {p | ¬ HasMonotoneAP (singlyPermutationSequence p) k}

/-- The integer-valued sequence displayed by a doubly-infinite permutation. -/
def doublyPermutationSequence (p : DoublyInfinitePermutation) (i : Int) : Int :=
  (p i : Nat)

/-- The paper's set `Dcal_k`. -/
def D (k : Nat) : Set DoublyInfinitePermutation :=
  {p | ¬ HasMonotoneAP (doublyPermutationSequence p) k}

/-- The position `A(n)` of a positive integer in a doubly-infinite
permutation, as used in Folkman's proof of Fact 5. -/
def doublyIndex (p : DoublyInfinitePermutation) (n : PositiveNat) : Int :=
  p.symm n

/-- Add a natural offset to a positive integer. -/
def positiveAdd (a : PositiveNat) (d : Nat) : PositiveNat :=
  ⟨a + d, Nat.add_pos_left a.property d⟩

/-- An integer permutation has no monotone `k`-term arithmetic progression. -/
def IntegerAPFree (p : IntegerPermutation) (k : Nat) : Prop :=
  ¬ HasMonotoneAP p k

/-! ## Finite blocks -/

/-- A finite block of positive integers. -/
abbrev Block := List Nat

/-- The sequence of values displayed by a finite block. -/
def blockSequence (B : Block) (i : Fin B.length) : Int :=
  B.get i

/-- A finite block has no monotone `k`-term arithmetic progression. -/
def BlockAPFree (B : Block) (k : Nat) : Prop :=
  ¬ HasMonotoneAP (blockSequence B) k

/-- The total length of all blocks before block `k`. -/
def blockPrefixLength (blocks : Nat -> Block) (k : Nat) : Nat :=
  (range k).sum fun i => (blocks i).length

/-- A singly-infinite permutation is obtained by concatenating the indicated
stream of finite blocks. -/
def IsSinglyBlockConcatenation (p : SinglyInfinitePermutation)
    (blocks : Nat -> Block) : Prop :=
  forall (k j : Nat) (hj : j < (blocks k).length),
    singlyPermutationSequence p (blockPrefixLength blocks k + j) =
      blockSequence (blocks k) ⟨j, hj⟩

/-- A doubly-infinite permutation is obtained by concatenating blocks indexed
by the integers.  The auxiliary function records the first sequence-position
of each block. -/
def IsDoublyBlockConcatenation (p : DoublyInfinitePermutation)
    (blocks : Int -> Block) : Prop :=
  exists start : Int -> Int, start 0 = 0 /\
    (forall i : Int, start (i + 1) = start i + (blocks i).length) /\
    forall (i : Int) (j : Nat) (hj : j < (blocks i).length),
      doublyPermutationSequence p (start i + j) = blockSequence (blocks i) ⟨j, hj⟩

/-- A block is an ordering of every integer in the closed interval `[a,b]`. -/
def IsIntervalOrdering (B : Block) (a b : Nat) : Prop :=
  B.Nodup /\ B.toFinset = Finset.Icc a b

/-- Doubling every entry of a block. -/
def twiceBlock (B : Block) : Block :=
  B.map fun x => 2 * x

/-- Doubling every entry of a block and then adding one. -/
def twiceBlockPlusOne (B : Block) : Block :=
  B.map fun x => 2 * x + 1

/-- The two parity blocks in the elementary finite construction. -/
def parityLift (evenOrder oddOrder : Block) : Block :=
  twiceBlock evenOrder ++ (oddOrder.map fun x => 2 * x - 1)

/-- The parity construction with the odd block placed first. -/
def parityLiftOddFirst (evenOrder oddOrder : Block) : Block :=
  (oddOrder.map fun x => 2 * x - 1) ++ twiceBlock evenOrder

/-! ## The decimal-scale construction for Fact 4 -/

/-- The paper's left endpoint parameter `a_k`. -/
def tenAStart (k : Nat) : Nat :=
  2 * (range k).sum fun i => 10 ^ i

/-- The paper's left endpoint parameter `b_k`. -/
def tenBStart (k : Nat) : Nat :=
  tenAStart k + 10 ^ k

/-- The interval `A_k`. -/
def tenA (k : Nat) : Finset Nat :=
  Finset.Icc (tenAStart k + 1) (tenAStart k + 10 ^ k)

/-- The interval `B_k`. -/
def tenB (k : Nat) : Finset Nat :=
  Finset.Icc (tenBStart k + 1) (tenBStart k + 10 ^ k)

/-- A choice of AP-free orderings `A_k^*` and `B_k^*` for every decimal
scale in the construction of Fact 4. -/
def IsTenBlockChoice (choice : Nat -> Block × Block) : Prop :=
  forall k,
    IsIntervalOrdering (choice k).1 (tenAStart k + 1) (tenAStart k + 10 ^ k) /\
    BlockAPFree (choice k).1 3 /\
    IsIntervalOrdering (choice k).2 (tenBStart k + 1) (tenBStart k + 10 ^ k) /\
    BlockAPFree (choice k).2 3

/-- The successive finite blocks `B_0^*, A_0^*, B_1^*, A_1^*, ...`
in the construction of Fact 4. -/
def tenBlockStream (choice : Nat -> Block × Block) (i : Nat) : Block :=
  if Even i then (choice (i / 2)).2 else (choice (i / 2)).1

/-! ## The finite tree in the second proof of Fact 5 -/

/-- The position of a value in a block.  Tree vertices are permutations, so
the first occurrence is the unique occurrence there. -/
def blockIndex (B : Block) (x : Nat) : Nat :=
  B.idxOf x

/-- A value lies in the subblock spanned by `1`, `2`, and `3`. -/
def InSpanOfOneTwoThree (B : Block) (x : Nat) : Prop :=
  min (blockIndex B 1) (min (blockIndex B 2) (blockIndex B 3)) <= blockIndex B x /\
    blockIndex B x <= max (blockIndex B 1) (max (blockIndex B 2) (blockIndex B 3))

/-- A tree vertex is special when the subblock spanned by `{1,2,3}`
contains the three values of some other 3-term arithmetic progression. -/
def IsSpecialVertex (B : Block) : Prop :=
  exists a d : Nat, 0 < d /\ (a != 1 \/ d != 1) /\
    InSpanOfOneTwoThree B a /\ InSpanOfOneTwoThree B (a + d) /\
      InSpanOfOneTwoThree B (a + 2 * d)

/-- The directed tree `T` from the computational proof of Fact 5. -/
inductive IsTreeVertex : Block -> Prop
  | root132 : IsTreeVertex [1, 3, 2]
  | root213 : IsTreeVertex [2, 1, 3]
  | root231 : IsTreeVertex [2, 3, 1]
  | root312 : IsTreeVertex [3, 1, 2]
  | extend {B B' : Block} : IsTreeVertex B -> ¬ IsSpecialVertex B ->
      IsIntervalOrdering B' 1 B'.length -> BlockAPFree B' 3 ->
      B.Sublist B' -> B'.length = B.length + 1 -> IsTreeVertex B'

/-- A terminal vertex of `T` has no child. -/
def IsTerminalVertex (B : Block) : Prop :=
  IsTreeVertex B /\ ¬ IsSpecialVertex B /\
    ¬ (exists B' : Block, IsTreeVertex B' /\ B.Sublist B' /\
      B'.length = B.length + 1)

/-! ## The dyadic-block construction for Fact 6 -/

/-- The recursively defined block `B_i` from the proof of Fact 6. -/
def dyadicBlock : Nat -> Block
  | 0 => [1]
  | i + 1 =>
      let evenPart := (twiceBlock (dyadicBlock i)).reverse
      let oddPart := (twiceBlockPlusOne (dyadicBlock i)).reverse
      if Even i then evenPart ++ oddPart else oddPart ++ evenPart

/-- Which dyadic block occurs at a given block-position in
`..., B_4, B_2, B_0, B_1, B_3, ...`. -/
def dyadicBlockIndex : Int -> Nat
  | Int.ofNat 0 => 0
  | Int.ofNat (n + 1) => 2 * n + 1
  | Int.negSucc n => 2 * (n + 1)

/-- The doubly-infinite arrangement of dyadic blocks used in Fact 6. -/
def dyadicBlockArrangement (i : Int) : Block :=
  dyadicBlock (dyadicBlockIndex i)

/-! ## The three-set construction in concluding remark 3 -/

/-- The length of the `(k+1)`-st consecutive interval in concluding
remark 3.  Thus `concludingIntervalLength 0 = 100`. -/
def concludingIntervalLength : Nat -> Nat
  | 0 => 100
  | k + 1 => 3 * concludingIntervalLength k / 2

/-- The first value in the `(k+1)`-st consecutive interval. -/
def concludingIntervalStart (k : Nat) : Nat :=
  1 + (range k).sum concludingIntervalLength

/-- The `(k+1)`-st consecutive interval `A_(k+1)` in concluding remark 3. -/
def concludingInterval (k : Nat) : Finset Nat :=
  Finset.Icc (concludingIntervalStart k)
    (concludingIntervalStart k + concludingIntervalLength k - 1)

/-- One of the three sets formed by taking every third concluding interval. -/
def concludingPart (r : Fin 3) : Set PositiveNat :=
  {x | exists k : Nat, k % 3 = r /\ (x : Nat) ∈ concludingInterval k}

/-! ## Arithmetic progressions modulo `n` -/

/-- The residue displayed at a position of a permutation of `[1,n]`. -/
def finiteModValue {n : Nat} (p : FinitePermutation n) (i : Fin n) : ZMod n :=
  (p i : Nat) + 1

/-- A permutation contains a monotone `k`-term arithmetic progression
modulo `n` in Nathanson's sense. -/
def HasMonotoneModAP {n : Nat} (p : FinitePermutation n) (k : Nat) : Prop :=
  exists pos : Fin k -> Fin n, StrictMono pos /\ exists a d : ZMod n, d != 0 /\
    forall i, finiteModValue p (pos i) = a + (i : Nat) * d

/-- A permutation has no monotone `k`-term arithmetic progression modulo
its interval length. -/
def ModularAPFree {n : Nat} (p : FinitePermutation n) (k : Nat) : Prop :=
  ¬ HasMonotoneModAP p k

/-- Being a power of two, including `2^0 = 1`. -/
def IsPowerOfTwo (n : Nat) : Prop :=
  exists r : Nat, n = 2 ^ r

/-! ## AP-free enumerable sets and their densities -/

/-- The integer-valued enumeration induced by an equivalence with a subset
of the positive integers. -/
def subsetEnumerationSequence {A : Set PositiveNat} (e : Nat ≃ A) (i : Nat) : Int :=
  ((e i).1 : Nat)

/-- A set of positive integers can be singly permuted without a monotone
`k`-term arithmetic progression. -/
def HasAPFreeEnumeration (A : Set PositiveNat) (k : Nat) : Prop :=
  exists e : Nat ≃ A, ¬ HasMonotoneAP (subsetEnumerationSequence e) k

/-- The family `mathscr A` in concluding remark 4. -/
def AdmissibleSubset (A : Set PositiveNat) : Prop :=
  HasAPFreeEnumeration A 3

/-- Membership in a set of positive naturals, viewed as a predicate on all
naturals. -/
def natMemPositiveSet (A : Set PositiveNat) (n : Nat) : Prop :=
  exists h : 0 < n, (show PositiveNat from ⟨n, h⟩) ∈ A

/-- The number of elements of `A` in the paper's interval `[1,n]`. -/
noncomputable def countUpTo (A : Set PositiveNat) (n : Nat) : Nat := by
  classical
  exact ((Finset.Icc 1 n).filter (natMemPositiveSet A)).card

/-- The density ratio `|A intersect [1,n]| / n`. -/
noncomputable def densityAt (A : Set PositiveNat) (n : Nat) : Real :=
  countUpTo A n / n

/-- The lower asymptotic density of a subset of the positive integers. -/
noncomputable def lowerDensity (A : Set PositiveNat) : Real :=
  Filter.liminf (densityAt A) Filter.atTop

/-- The upper asymptotic density of a subset of the positive integers. -/
noncomputable def upperDensity (A : Set PositiveNat) : Real :=
  Filter.limsup (densityAt A) Filter.atTop

/-- The first supremum asked for in concluding remark 4. -/
noncomputable def maximalLowerDensity : Real :=
  sSup (Set.range fun A : {A : Set PositiveNat // AdmissibleSubset A} => lowerDensity A)

/-- The second supremum asked for in concluding remark 4. -/
noncomputable def maximalUpperDensity : Real :=
  sSup (Set.range fun A : {A : Set PositiveNat // AdmissibleSubset A} => upperDensity A)

end LeanProofs.DavisEntringerGrahamSimmons1977

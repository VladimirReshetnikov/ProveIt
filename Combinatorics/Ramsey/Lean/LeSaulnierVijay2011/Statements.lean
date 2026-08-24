import LeSaulnierVijay2011.Definitions

/-!
# LeSaulnier--Vijay (2011): formal statement catalogue

This file records the numbered theorems, the concluding conjecture, and the
auxiliary results explicitly stated or invoked in Timothy D. LeSaulnier and
Sujith Vijay, "On permutations avoiding arithmetic progressions", *Discrete
Mathematics* 311 (2011), 205--207.

Following the repository's statement-catalogue convention, unresolved results
are definitions whose values are propositions; this file asserts none of them.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace LeanProofs.LeSaulnierVijay2011

/-! ## Previously known counting results -/

/-- The Davis--Entringer--Graham--Simmons bounds quoted at the start of the
paper.  Natural-number division gives the floor and ceiling in the printed
upper bound. -/
def davis_counting_bounds : Prop :=
  forall n : Nat, 1 <= n ->
    2 ^ (n - 1) <= M n /\
      M n <= Nat.factorial ((n + 1) / 2) * Nat.factorial ((n + 2) / 2)

/-- Sharma's quoted exponential upper bound. -/
def sharma_upper_bound : Prop :=
  forall n : Nat, 11 <= n ->
    (M n : Real) <= ((27 : Real) / 10) ^ n / 21

/-- Sharma's quoted lower bound: `M(n) / (2^n n^k)` tends to infinity for
each fixed `k`. -/
def sharma_superpolynomial_lower_bound : Prop :=
  forall k : Nat,
    Tendsto (fun n : Nat => (M n : Real) / ((2 : Real) ^ n * (n : Real) ^ k))
      atTop atTop

/-! ## Theorem 1 -/

/-- The constant `c = 2132^(1/10)` in Theorem 1. -/
noncomputable def theorem1Constant : Real :=
  Real.rpow 2132 ((1 : Real) / 10)

/-- **Theorem 1.** The improved exponential lower bound for `M(n)`. -/
def theorem_1 : Prop :=
  forall n : Nat, 8 <= n ->
    ((1 : Real) / 2) * theorem1Constant ^ n <= M n

/-- The even recurrence from Davis et al. used in the proof of Theorem 1. -/
def M_even_recurrence : Prop :=
  forall n : Nat, 1 <= n -> 2 * (M n) ^ 2 <= M (2 * n)

/-- The odd recurrence from Davis et al. used in the proof of Theorem 1. -/
def M_odd_recurrence : Prop :=
  forall n : Nat, 1 <= n -> 2 * M n * M (n + 1) <= M (2 * n + 1)

/-- The finite values quoted from Davis et al. to initialize the induction in
Theorem 1.  The published journal PDF's `73,904` is corrected to `74,904`, the
value in the cited Davis et al. table (and obtained by direct enumeration). -/
def M_initial_values : Prop :=
  M 8 = 282 /\ M 9 = 496 /\ M 10 = 1066 /\ M 11 = 2460 /\
    M 12 = 6128 /\ M 13 = 12840 /\ M 14 = 29380 /\ M 15 = 74904

/-- The negative answer to the ratio-limit question discussed immediately
before Theorem 1. -/
def M_ratio_does_not_tend_to_two : Prop :=
  ¬ Tendsto (fun n : Nat => (M (n + 1) : Real) / M n) atTop (nhds 2)

/-! ## Infinite permutations and Theorem 2 -/

/-- The previously known observation of Davis et al.: every permutation of
the positive integers contains a 3-term arithmetic progression. -/
def every_permutation_of_positives_has_three_AP : Prop :=
  forall rank : Nat -> Nat, IsPermutationRanking positiveIntegers rank ->
    HasAPInRanking 3 positiveIntegers rank

/-- The previously known construction of a 5-avoiding permutation of the
positive integers. -/
def positive_integers_are_five_avoidable : Prop :=
  IsKAvoidable 5 positiveIntegers

/-- The open problem, noted before Theorem 2, of whether the positive integers
have a 4-avoiding permutation. -/
def positive_integers_are_four_avoidable : Prop :=
  IsKAvoidable 4 positiveIntegers

/-- The finite forcing claim used in the proof of Theorem 2.  Every
permutation of `{1, ..., 11}` beginning with `2, 1` contains an odd-difference
3-term AP. -/
def theorem_2_finite_claim : Prop :=
  forall sigma : Equiv.Perm (Fin 11),
    finitePermutationValue sigma 0 = 2 -> finitePermutationValue sigma 1 = 1 ->
      HasOddAPSubsequence 3 (finitePermutationValue sigma)

/-- **Theorem 2.** Every permutation of the positive integers contains an
odd-difference 3-term AP, while some permutation avoids every odd-difference
4-term AP. -/
def theorem_2 : Prop :=
  (forall rank : Nat -> Nat, IsPermutationRanking positiveIntegers rank ->
      HasOddAPInRanking 3 positiveIntegers rank) /\
    IsOddKAvoidable 4 positiveIntegers

/-- The cardinalities of the even and odd blocks in the explicit construction
for the second half of Theorem 2. -/
def theorem_2_block_cardinalities : Prop :=
  forall i : Nat, 1 <= i ->
    (theorem2EvenBlock i).card = 2 ^ (2 * i - 1) /\
      (theorem2OddBlock i).card = 4 ^ (i - 1)

/-- The alternating even and odd blocks in the proof of Theorem 2 cover the
positive integers.  Together with the block permutations, this is the
paper's assertion that their concatenation is a permutation. -/
def theorem_2_blocks_cover_positive_integers : Prop :=
  forall n : Nat, n ∈ positiveIntegers <->
    exists i : Nat, 1 <= i /\
      (n ∈ theorem2EvenBlock i \/ n ∈ theorem2OddBlock i)

/-- The blocks in the alternating construction are pairwise disjoint.  With
the preceding coverage statement, this records the full set-theoretic content
of the claim that their concatenation is a permutation. -/
def theorem_2_blocks_pairwise_disjoint : Prop :=
  (forall i j : Nat, 1 <= i -> 1 <= j -> i != j ->
      Disjoint (theorem2EvenBlock i) (theorem2EvenBlock j) /\
        Disjoint (theorem2OddBlock i) (theorem2OddBlock j)) /\
    forall i j : Nat, 1 <= i -> 1 <= j ->
      Disjoint (theorem2EvenBlock i) (theorem2OddBlock j)

/-- The numerical separation behind the last step of Theorem 2's
construction: an odd entry from an earlier block is less than half every even
entry in a later block. -/
def theorem_2_odd_even_separation : Prop :=
  forall i j x y : Nat, 1 <= i -> i < j ->
    x ∈ theorem2OddBlock i -> y ∈ theorem2EvenBlock j -> 2 * x < y

/-! ## Densities and Theorem 3 -/

/-- The consequence of the known 5-avoidability result noted after the
definitions of `alpha` and `beta`. -/
def alpha_beta_of_five_or_more : Prop :=
  forall k : Nat, 5 <= k -> alpha k = 1 /\ beta k = 1

/-- The block construction in the proof of Theorem 3 makes every
`S^(a)` 4-avoidable. -/
def geometricSet_is_four_avoidable : Prop :=
  forall a : Nat, 2 <= a -> IsKAvoidable 4 (geometricSet a)

/-- The upper- and lower-density calculations for `S^(a)`. -/
def geometricSet_densities : Prop :=
  forall a : Nat, 2 <= a ->
    upperDensity (geometricSet a) = (a : Real) / (a + 1) /\
      lowerDensity (geometricSet a) = 1 / (a + 1 : Nat)

/-- The endpoint identity for the interval construction `T_k`. -/
def p_closed_form : Prop :=
  forall k : Nat, 1 <= k -> p k = 3 ^ k + 1 /\ p k = 2 * q (k - 1)

/-- The set `T` constructed in the proof of Theorem 3 is 3-avoidable. -/
def TSet_is_three_avoidable : Prop :=
  IsKAvoidable 3 TSet

/-- The density calculation for the set `T`. -/
def TSet_densities : Prop :=
  upperDensity TSet = (1 : Real) / 2 /\ lowerDensity TSet = (1 : Real) / 4

/-- **Theorem 3.** The four bounds for the extremal density parameters. -/
def theorem_3 : Prop :=
  alpha 4 = 1 /\ (1 : Real) / 2 <= alpha 3 /\
    (1 : Real) / 3 <= beta 4 /\ (1 : Real) / 4 <= beta 3

/-! ## Concluding questions and conjecture -/

/-- The Erdos--Graham question: can the positive integers be partitioned into
two 3-avoidable sets? -/
def erdos_graham_partition_question : Prop :=
  exists A B : Set Nat, IsKAvoidable 3 A /\ IsKAvoidable 3 B /\
    Disjoint A B /\ A ∪ B = positiveIntegers

/-- The still-open inequality singled out in the last sentence of the paper. -/
def beta_three_strictly_less_than_one : Prop :=
  beta 3 < 1

/-- The concluding conjecture that both lower bounds in Theorem 3 are
optimal. -/
def conjecture : Prop :=
  alpha 3 = (1 : Real) / 2 /\ beta 3 = (1 : Real) / 4

end LeanProofs.LeSaulnierVijay2011

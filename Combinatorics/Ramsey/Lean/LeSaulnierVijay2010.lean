import LeSaulnierVijay2011.Definitions

/-!
# LeSaulnier--Vijay (2010): formal statement catalogue

This file records the statements in arXiv:1004.1740v1, Timothy D.
LeSaulnier and Sujith Vijay, "On Permutations Avoiding Arithmetic
Progressions".  The arXiv preprint and its 2011 journal version use almost
all the same auxiliary language, so this catalogue reuses the corrected
definition layer in `LeSaulnierVijay2011.Definitions` and adds the preprint's
signed-integer variant of `k`-avoidability locally.

Following the repository convention, results not yet proved in Lean are
definitions whose values are propositions.  Thus this file records their
precise statements without adding axioms or admitted proofs.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace LeanProofs.LeSaulnierVijay2010

open LeanProofs.LeSaulnierVijay2011

/-! ## Results quoted in the introduction -/

/-- The small value used to illustrate the definition of `M`.  The
preprint's representative `(1,2,4,3)` is a typo (it contains `(1,2,3)`);
the corrected list still has ten permutations in total. -/
def M_four_value : Prop :=
  M 4 = 10

/-- The corrected exhaustive list behind the example `M(4) = 10`.  The five
representatives in the paper and their reversals are written out explicitly
to avoid hiding the correction to `(1,2,4,3)`. -/
def M_four_representatives : Prop :=
  forall sigma : Equiv.Perm (Fin 4), IsFiniteKAvoiding 3 sigma <->
    finitePermutationValue sigma = ![1, 3, 4, 2] \/
    finitePermutationValue sigma = ![2, 4, 3, 1] \/
    finitePermutationValue sigma = ![1, 3, 2, 4] \/
    finitePermutationValue sigma = ![4, 2, 3, 1] \/
    finitePermutationValue sigma = ![2, 1, 4, 3] \/
    finitePermutationValue sigma = ![3, 4, 1, 2] \/
    finitePermutationValue sigma = ![2, 4, 1, 3] \/
    finitePermutationValue sigma = ![3, 1, 4, 2] \/
    finitePermutationValue sigma = ![4, 2, 1, 3] \/
    finitePermutationValue sigma = ![3, 1, 2, 4]

/-- The Davis--Entringer--Graham--Simmons lower and upper bounds quoted in
the opening paragraph.  Natural-number division expresses the printed floor
and ceiling. -/
def davis_counting_bounds : Prop :=
  forall n : Nat, 1 <= n ->
    2 ^ (n - 1) <= M n /\
      M n <= Nat.factorial ((n + 1) / 2) * Nat.factorial ((n + 2) / 2)

/-- Sharma's exponential upper bound quoted in the opening paragraph. -/
def sharma_upper_bound : Prop :=
  forall n : Nat, 11 <= n ->
    (M n : Real) <= ((27 : Real) / 10) ^ n / 21

/-- Sharma's quoted super-polynomial improvement over the factor `2^n`. -/
def sharma_superpolynomial_lower_bound : Prop :=
  forall k : Nat,
    Tendsto (fun n : Nat => (M n : Real) / ((2 : Real) ^ n * (n : Real) ^ k))
      atTop atTop

/-! ## Theorem 1 -/

/-- The constant `c = 2132^(1/10)` from Theorem 1. -/
noncomputable def theorem1Constant : Real :=
  Real.rpow 2132 ((1 : Real) / 10)

/-- **Theorem 1.** The improved exponential lower bound on the number of
3-avoiding permutations. -/
def theorem_1 : Prop :=
  forall n : Nat, 8 <= n ->
    ((1 : Real) / 2) * theorem1Constant ^ n <= (M n : Real)

/-- The even recurrence from Davis et al. used in the proof of Theorem 1. -/
def M_even_recurrence : Prop :=
  forall n : Nat, 1 <= n -> 2 * (M n) ^ 2 <= M (2 * n)

/-- The odd recurrence from Davis et al. used in the proof of Theorem 1. -/
def M_odd_recurrence : Prop :=
  forall n : Nat, 1 <= n -> 2 * M n * M (n + 1) <= M (2 * n + 1)

/-- The finite values quoted to initialize the induction in Theorem 1.  The
preprint's `73,904` is corrected to `74,904`, the value in the cited Davis et
al. table and the value obtained by direct enumeration. -/
def M_initial_values : Prop :=
  M 8 = 282 /\ M 9 = 496 /\ M 10 = 1066 /\ M 11 = 2460 /\
    M 12 = 6128 /\ M 13 = 12840 /\ M 14 = 29380 /\ M 15 = 74904

/-- The negative answer to the ratio-limit question preceding Theorem 1. -/
def M_ratio_does_not_tend_to_two : Prop :=
  ¬ Tendsto (fun n : Nat => (M (n + 1) : Real) / M n) atTop (nhds 2)

/-! ## Infinite permutations and Theorem 2 -/

/-- The observation of Davis et al. that every permutation of the positive
integers contains a 3-term arithmetic progression. -/
def every_permutation_of_positives_has_three_AP : Prop :=
  forall rank : Nat -> Nat, IsPermutationRanking positiveIntegers rank ->
    HasAPInRanking 3 positiveIntegers rank

/-- The Davis et al. construction of a 5-avoiding permutation of the positive
integers. -/
def positive_integers_are_five_avoidable : Prop :=
  IsKAvoidable 5 positiveIntegers

/-- The open problem preceding Theorem 2: are the positive integers
4-avoidable? -/
def positive_integers_are_four_avoidable : Prop :=
  IsKAvoidable 4 positiveIntegers

/-- The finite forcing claim used in the proof of Theorem 2.  The preprint's
contradictory adjective "3AP-free" is removed: the ensuing argument proves
the stronger statement for every permutation beginning with `2, 1`. -/
def theorem_2_finite_claim : Prop :=
  forall sigma : Equiv.Perm (Fin 11),
    finitePermutationValue sigma 0 = 2 -> finitePermutationValue sigma 1 = 1 ->
      HasOddAPSubsequence 3 (finitePermutationValue sigma)

/-- **Theorem 2.** Odd-difference 3-term progressions are unavoidable in a
permutation of the positive integers, whereas odd-difference 4-term
progressions are avoidable. -/
def theorem_2 : Prop :=
  (forall rank : Nat -> Nat, IsPermutationRanking positiveIntegers rank ->
      HasOddAPInRanking 3 positiveIntegers rank) /\
    IsOddKAvoidable 4 positiveIntegers

/-- The corrected cardinalities of the even and odd blocks in the explicit
construction for the second half of Theorem 2. -/
def theorem_2_block_cardinalities : Prop :=
  forall i : Nat, 1 <= i ->
    (theorem2EvenBlock i).card = 2 ^ (2 * i - 1) /\
      (theorem2OddBlock i).card = 2 ^ (2 * i - 2)

/-- The corrected endpoints make the alternating even and odd blocks cover
all positive integers. -/
def theorem_2_blocks_cover_positive_integers : Prop :=
  forall n : Nat, n ∈ positiveIntegers <->
    exists i : Nat, 1 <= i /\
      (n ∈ theorem2EvenBlock i \/ n ∈ theorem2OddBlock i)

/-- The blocks in the alternating construction are pairwise disjoint.  With
the preceding coverage statement, this records the full set-theoretic
content of the claim that their concatenation is a permutation. -/
def theorem_2_blocks_pairwise_disjoint : Prop :=
  (forall i j : Nat, 1 <= i -> 1 <= j -> i != j ->
      Disjoint (theorem2EvenBlock i) (theorem2EvenBlock j) /\
        Disjoint (theorem2OddBlock i) (theorem2OddBlock j)) /\
    forall i j : Nat, 1 <= i -> 1 <= j ->
      Disjoint (theorem2EvenBlock i) (theorem2OddBlock j)

/-- The numerical separation used in the last step of Theorem 2: an odd
entry from an earlier odd block is less than half every even entry in a later
even block.  These are precisely the odd-before-even pairs in the alternating
concatenation. -/
def theorem_2_odd_even_separation : Prop :=
  forall i j x y : Nat, 1 <= i -> i < j ->
    x ∈ theorem2OddBlock i -> y ∈ theorem2EvenBlock j -> 2 * x < y

/-- A rank orders the even and odd blocks as in
`sigma_1 pi_1 sigma_2 pi_2 ...`. -/
def Theorem2BlocksInOrder (rank : Nat -> Nat) : Prop :=
  forall i : Nat, 1 <= i ->
    (forall x, x ∈ theorem2EvenBlock i -> forall y, y ∈ theorem2OddBlock i ->
      rank x < rank y) /\
    (forall x, x ∈ theorem2OddBlock i ->
      forall y, y ∈ theorem2EvenBlock (i + 1) -> rank x < rank y)

/-- The full concatenation claim in the second half of Theorem 2: ordering
3-avoiding permutations of the displayed blocks alternately produces an
odd-difference 4-avoiding permutation of the positive integers. -/
def theorem_2_block_concatenation_is_odd_four_avoiding : Prop :=
  forall rank : Nat -> Nat, IsPermutationRanking positiveIntegers rank ->
    Theorem2BlocksInOrder rank ->
    (forall i : Nat, 1 <= i ->
      IsKAvoidingRanking 3 (theorem2EvenBlock i : Set Nat) rank /\
        IsKAvoidingRanking 3 (theorem2OddBlock i : Set Nat) rank) ->
    IsOddKAvoidingRanking 4 positiveIntegers rank

/-! ## Density parameters and Theorem 3 -/

/-- An integer-valued progression occurs in the permutation order induced by
`rank`.  This signed variant records the preprint's definition for arbitrary
subsets of the integers, rather than only the positive sets used later. -/
def HasIntegerAPInRanking (k : Nat) (S : Set Int) (rank : Int -> Nat) : Prop :=
  exists x : Fin k -> Int, (forall i, x i ∈ S) /\
    StrictMono (fun i => rank (x i)) /\
      exists a d : Int, d != 0 /\
        forall i, x i = a + ((i : Nat) : Int) * d

/-- The preprint's notion that a subset of the integers is `k`-free: some
permutation ranking avoids every `k`-term arithmetic progression. -/
def IsIntegerKAvoidable (k : Nat) (S : Set Int) : Prop :=
  exists rank : Int -> Nat, Set.InjOn rank S /\
    ¬ HasIntegerAPInRanking k S rank

/-- Every entry of an earlier block precedes every entry of a later block in
the order induced by `rank`. -/
def BlocksInOrder (blocks : Nat -> Finset Nat) (rank : Nat -> Nat) : Prop :=
  forall i j : Nat, i < j -> forall x, x ∈ blocks i ->
    forall y, y ∈ blocks j -> rank x < rank y

/-- The consequence of the known 5-avoidability construction recorded just
after the definitions of `alpha` and `beta`. -/
def alpha_beta_of_five_or_more : Prop :=
  forall k : Nat, 5 <= k -> alpha k = 1 /\ beta k = 1

/-- The geometric-block construction in the proof makes `S^(a)`
4-avoidable. -/
def geometricSet_is_four_avoidable : Prop :=
  forall a : Nat, 2 <= a -> IsKAvoidable 4 (geometricSet a)

/-- The two density calculations for the geometric-block construction. -/
def geometricSet_densities : Prop :=
  forall a : Nat, 2 <= a ->
    upperDensity (geometricSet a) = (a : Real) / (a + 1) /\
      lowerDensity (geometricSet a) = 1 / (a + 1 : Nat)

/-- The gap between distinct geometric blocks used in the 4-avoidability
argument: an entry of a later block is at least twice every entry of an
earlier block. -/
def geometricBlock_cross_gap : Prop :=
  forall a i j x y : Nat, 2 <= a -> i < j ->
    x ∈ geometricBlock a i -> y ∈ geometricBlock a j -> 2 * x <= y

/-- The explicit concatenation claim in the first half of Theorem 3.  Any
block-ordered concatenation of 3-avoiding permutations of the geometric
blocks is 4-avoiding. -/
def geometricBlock_concatenation_is_four_avoiding : Prop :=
  forall (a : Nat) (rank : Nat -> Nat), 2 <= a ->
    IsPermutationRanking (geometricSet a) rank ->
    BlocksInOrder (geometricBlock a) rank ->
    (forall i : Nat,
      IsKAvoidingRanking 3 (geometricBlock a i : Set Nat) rank) ->
    IsKAvoidingRanking 4 (geometricSet a) rank

/-- The recursively defined set `T` is 3-avoidable. -/
def TSet_is_three_avoidable : Prop :=
  IsKAvoidable 3 TSet

/-- The endpoint identity underlying the density calculation for `T`. -/
def p_closed_form : Prop :=
  forall k : Nat, 1 <= k -> p k = 3 ^ k + 1 /\ p k = 2 * q (k - 1)

/-- The upper and lower densities of the set `T`. -/
def TSet_densities : Prop :=
  upperDensity TSet = (1 : Real) / 2 /\ lowerDensity TSet = (1 : Real) / 4

/-- Entries in different `T`-blocks have the factor-two separation used in
the first case of the 3-avoidability argument. -/
def TBlock_cross_gap : Prop :=
  forall k l x y : Nat, k < l ->
    x ∈ TBlock k -> y ∈ TBlock l -> 2 * x <= y

/-- The corrected same-block gap estimate in the proof that `T` is
3-avoidable.  The preprint prints `q_k` in both comparisons, but the valid
intermediate bound is `q_(k-1)`, as in the revised journal version. -/
def TBlock_same_block_gap : Prop :=
  forall k l x1 x2 x3 : Nat, 1 <= k -> l < k ->
    x1 ∈ TBlock l -> x2 ∈ TBlock k -> x3 ∈ TBlock k -> x2 < x3 ->
      x3 - x2 < q (k - 1) /\ q (k - 1) <= x2 - x1

/-- The explicit concatenation claim in the second half of Theorem 3.  Any
block-ordered concatenation of 3-avoiding permutations of the intervals
`T_k` is itself 3-avoiding. -/
def TBlock_concatenation_is_three_avoiding : Prop :=
  forall rank : Nat -> Nat, IsPermutationRanking TSet rank ->
    BlocksInOrder TBlock rank ->
    (forall k : Nat, IsKAvoidingRanking 3 (TBlock k : Set Nat) rank) ->
    IsKAvoidingRanking 3 TSet rank

/-- **Theorem 3.** The four extremal density bounds. -/
def theorem_3 : Prop :=
  alpha 4 = 1 /\ (1 : Real) / 2 <= alpha 3 /\
    (1 : Real) / 3 <= beta 4 /\ (1 : Real) / 4 <= beta 3

/-! ## Concluding question and conjecture -/

/-- The Erdos--Graham question asking whether the positive integers can be
partitioned into two 3-avoidable sets. -/
def erdos_graham_partition_question : Prop :=
  exists A B : Set Nat, IsKAvoidable 3 A /\ IsKAvoidable 3 B /\
    Disjoint A B /\ A ∪ B = positiveIntegers

/-- The density obstruction stated immediately after the Erdos--Graham
question. -/
def alpha_beta_sum_obstructs_partition : Prop :=
  alpha 3 + beta 3 < 1 -> ¬ erdos_graham_partition_question

/-- The strict density inequality that the authors say they believe.  It is
also a consequence of their sharper numerical conjecture below. -/
def conjectured_alpha_beta_sum_bound : Prop :=
  alpha 3 + beta 3 < 1

/-- The inequality that the authors could not establish. -/
def beta_three_strictly_less_than_one : Prop :=
  beta 3 < 1

/-- The concluding conjecture that the two lower bounds for `alpha 3` and
`beta 3` are optimal. -/
def conjecture : Prop :=
  alpha 3 = (1 : Real) / 2 /\ beta 3 = (1 : Real) / 4

end LeanProofs.LeSaulnierVijay2010

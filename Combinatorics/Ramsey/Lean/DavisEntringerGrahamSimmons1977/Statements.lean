import DavisEntringerGrahamSimmons1977.Definitions

/-!
# Davis--Entringer--Graham--Simmons (1977): formal statement catalogue

Every numbered fact in "On permutations containing no long arithmetic
progressions" is represented by a `Prop`-valued definition below.  The file
also records the recurrence inequalities, construction claims, computational
tree bound, cited modular results, and concluding assertions that are stated
without fact numbers.  These definitions record statements but assert none of
them.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.DavisEntringerGrahamSimmons1977

/-! ## Permutations of finite intervals -/

/-- Deleting entries cannot create a monotone arithmetic progression. -/
def deletion_preserves_ap_freeness : Prop :=
  forall (A B : Block) (k : Nat), B.Sublist A -> BlockAPFree A k -> BlockAPFree B k

/-- The parity construction from the opening paragraph preserves avoidance
of monotone 3-term progressions, in either order of the parity blocks.  The
positivity hypotheses faithfully record that the paper's input blocks consist
of positive integers; they are also necessary because `2 * 0 - 1` truncates in
`Nat`. -/
def parity_construction_is_ap_free : Prop :=
  forall (A A' : Block),
    (forall x : Nat, x ∈ A -> 0 < x) ->
    (forall x : Nat, x ∈ A' -> 0 < x) ->
    BlockAPFree A 3 -> BlockAPFree A' 3 ->
    BlockAPFree (parityLift A A') 3 /\ BlockAPFree (parityLiftOddFirst A A') 3

/-- When its input blocks order `[1,m]`, the parity construction orders
`[1,2m]`, as asserted in the opening construction. -/
def parity_construction_orders_interval : Prop :=
  forall (m : Nat) (A A' : Block),
    IsIntervalOrdering A 1 m -> IsIntervalOrdering A' 1 m ->
      IsIntervalOrdering (parityLift A A') 1 (2 * m) /\
        IsIntervalOrdering (parityLiftOddFirst A A') 1 (2 * m)

/-- The initial existence assertion `M(n) > 0` for every finite interval. -/
def finite_ap_free_permutation_exists : Prop :=
  forall n : Nat, 0 < n -> exists p : FinitePermutation n, FiniteAPFree p 3

/-- The even recurrence used in the proof of Fact 1. -/
def even_count_recurrence : Prop :=
  forall n : Nat, 0 < n -> 2 * M n ^ 2 <= M (2 * n)

/-- The odd recurrence used in the proof of Fact 1. -/
def odd_count_recurrence : Prop :=
  forall n : Nat, 0 < n -> 2 * M (n + 1) * M n <= M (2 * n + 1)

/-- The two initial values used to solve the recurrences. -/
def initial_count_values : Prop :=
  M 2 = 2 /\ M 3 = 4

/-- **Fact 1 / equation (1).** -/
def fact_1 : Prop :=
  forall n : Nat, 1 <= n -> 2 ^ (n - 1) <= M n

/-- **Table 1.** The exact values of `M(n)` for `1 <= n <= 20`. -/
def table_1 : Prop :=
  List.ofFn (fun i : Fin 20 => M ((i : Nat) + 1)) =
    [1, 2, 4, 10, 20, 48, 104, 282, 496, 1066,
      2460, 6128, 12840, 29380, 74904, 212728, 368016, 659296, 1371056, 2937136]

/-- The quantitative consequence of `M(16) = 212728` displayed after
Table 1.  The decimal `2.248` is represented exactly. -/
def power_of_two_count_lower_bound : Prop :=
  forall t : Nat, 4 <= t ->
    (1 / 2 : Real) * (2248 / 1000 : Real) ^ (2 ^ t) < (M (2 ^ t) : Real)

/-- The one-step insertion upper bound proved en route to Fact 2. -/
def insertion_count_upper_bound : Prop :=
  forall n : Nat, 0 < n -> M (n + 1) <= ((n + 3) / 2) * M n

/-- **Fact 2 / equation (2).** -/
def fact_2 : Prop :=
  forall n : Nat, 1 <= n ->
    M (2 * n - 1) <= Nat.factorial n ^ 2 /\
      M (2 * n) <= (n + 1) * Nat.factorial n ^ 2

/-! ## Permutations of the positive integers -/

/-- The proof of Fact 3 actually produces an increasing 3-term progression. -/
def fact_3_increasing_form : Prop :=
  forall p : SinglyInfinitePermutation,
    HasIncreasingAP (singlyPermutationSequence p) 3

/-- **Fact 3.** `Scal_3` is empty. -/
def fact_3 : Prop :=
  S 3 = ∅

/-- The intervals `A_k` and `B_k` form a disjoint partition of the positive
integers, and both have cardinality `10^k`. -/
def decimal_intervals_partition : Prop :=
  (forall k : Nat, (tenA k).card = 10 ^ k /\ (tenB k).card = 10 ^ k /\
    Disjoint (tenA k) (tenB k)) /\
  (forall x : PositiveNat, ∃! q : Nat × Bool,
    if q.2 then (x : Nat) ∈ tenA q.1 else (x : Nat) ∈ tenB q.1)

/-- AP-free orderings can be chosen for every interval used in Fact 4. -/
def decimal_block_choices_exist : Prop :=
  exists choice : Nat -> Block × Block, IsTenBlockChoice choice

/-- Concatenating the chosen decimal-scale blocks really gives a permutation
of all positive integers. -/
def decimal_concatenation_exists : Prop :=
  forall choice : Nat -> Block × Block, IsTenBlockChoice choice ->
    exists p : SinglyInfinitePermutation,
      IsSinglyBlockConcatenation p (tenBlockStream choice)

/-- The construction in the proof of Fact 4 has no monotone 5-term
arithmetic progression. -/
def decimal_construction_avoids_five : Prop :=
  forall (choice : Nat -> Block × Block) (p : SinglyInfinitePermutation),
    IsTenBlockChoice choice -> IsSinglyBlockConcatenation p (tenBlockStream choice) ->
      p ∈ S 5

/-- **Fact 4.** `Scal_5` is nonempty. -/
def fact_4 : Prop :=
  S 5 != ∅

/-- The paper's principal open question: is every singly-infinite
permutation forced to contain a monotone 4-term progression? -/
def conjecture_singly_four_term : Prop :=
  S 4 = ∅

/-! ## Doubly-infinite permutations of the positive integers -/

/-- Equations (4) and (4'): adjacent values along any positive arithmetic
progression alternate their order in a 3-term-AP-free doubly-infinite
permutation. -/
def folkman_alternating_order : Prop :=
  forall p : DoublyInfinitePermutation, p ∈ D 3 -> forall (a d : PositiveNat),
    (doublyIndex p a < doublyIndex p (positiveAdd a d) <-> forall m : Nat,
      doublyIndex p (positiveAdd a (2 * m * d)) <
          doublyIndex p (positiveAdd a ((2 * m + 1) * d)) /\
        doublyIndex p (positiveAdd a ((2 * m + 1) * d)) >
          doublyIndex p (positiveAdd a ((2 * m + 2) * d))) /\
    (doublyIndex p a > doublyIndex p (positiveAdd a d) <-> forall m : Nat,
      doublyIndex p (positiveAdd a (2 * m * d)) >
          doublyIndex p (positiveAdd a ((2 * m + 1) * d)) /\
        doublyIndex p (positiveAdd a ((2 * m + 1) * d)) <
          doublyIndex p (positiveAdd a ((2 * m + 2) * d)))

/-- Equation (6), the induction claim in Folkman's proof. -/
def folkman_odd_order_claim : Prop :=
  forall p : DoublyInfinitePermutation, p ∈ D 3 ->
    doublyIndex p ⟨1, Nat.one_pos⟩ < doublyIndex p ⟨2, Nat.zero_lt_succ 1⟩ ->
    forall (a d : PositiveNat), Odd (a : Nat) -> Odd (d : Nat) ->
      doublyIndex p a < doublyIndex p (positiveAdd a d)

/-- **Fact 5.** `Dcal_3` is empty. -/
def fact_5 : Prop :=
  D 3 = ∅

/-- The corrected computational assertion in the second proof of Fact 5: the tree
`T` has no vertex of size greater than 20. -/
def computational_tree_bound : Prop :=
  forall B : Block, IsTreeVertex B -> B.length <= 20

/-- The basic inductive property of the blocks in the Fact 6 construction. -/
def dyadic_block_properties : Prop :=
  forall i : Nat,
    IsIntervalOrdering (dyadicBlock i) (2 ^ i) (2 ^ (i + 1) - 1) /\
      BlockAPFree (dyadicBlock i) 3

/-- The arranged dyadic blocks concatenate to a doubly-infinite permutation
of the positive integers. -/
def dyadic_concatenation_exists : Prop :=
  exists p : DoublyInfinitePermutation,
    IsDoublyBlockConcatenation p dyadicBlockArrangement

/-- The explicit dyadic construction in the proof of Fact 6 avoids monotone
4-term arithmetic progressions. -/
def dyadic_construction_avoids_four : Prop :=
  forall p : DoublyInfinitePermutation,
    IsDoublyBlockConcatenation p dyadicBlockArrangement -> p ∈ D 4

/-- **Fact 6.** `Dcal_4` is nonempty. -/
def fact_6 : Prop :=
  D 4 != ∅

/-! ## Concluding remarks -/

/-- Nathanson's result, concluding remark 2(i): outside powers of two every
permutation contains a monotone 3-term progression modulo `n`. -/
def nathanson_non_power_of_two : Prop :=
  forall n : Nat, 0 < n -> ¬ IsPowerOfTwo n ->
    forall p : FinitePermutation n, HasMonotoneModAP p 3

/-- Nathanson's result, concluding remark 2(ii): at powers of two a
3-term-progression-free permutation modulo `n` exists. -/
def nathanson_power_of_two : Prop :=
  forall r : Nat, exists p : FinitePermutation (2 ^ r), ModularAPFree p 3

/-- The elementary observation following Nathanson's result: ordinary
3-term avoidance implies modular 5-term avoidance. -/
def ordinary_three_free_implies_modular_five_free : Prop :=
  forall (n : Nat) (p : FinitePermutation n),
    FiniteAPFree p 3 -> ModularAPFree p 5

/-- The unresolved modular four-term existence question for a given modulus. -/
def modular_four_term_avoidance_question (n : Nat) : Prop :=
  exists p : FinitePermutation n, ModularAPFree p 4

/-- The consecutive intervals in concluding remark 3 partition the positive
integers and obey the displayed length recurrence. -/
def concluding_intervals_partition : Prop :=
  (concludingInterval 0 = Finset.Icc 1 100) /\
  (forall k : Nat,
    concludingIntervalLength (k + 1) = 3 * concludingIntervalLength k / 2) /\
  (forall x : PositiveNat, ∃! k : Nat, (x : Nat) ∈ concludingInterval k)

/-- Concluding remark 3: the positive integers split into three sets, each
of which admits a 3-term-AP-free permutation. -/
def three_set_partition : Prop :=
  exists A B C : Set PositiveNat,
    A ∪ B ∪ C = Set.univ /\ Disjoint A B /\ Disjoint A C /\ Disjoint B C /\
      HasAPFreeEnumeration A 3 /\ HasAPFreeEnumeration B 3 /\
        HasAPFreeEnumeration C 3

/-- The specific every-third-interval construction asserted in concluding
remark 3. -/
def three_set_interval_construction : Prop :=
  (⋃ r : Fin 3, concludingPart r) = Set.univ /\
    (forall r s : Fin 3, r != s -> Disjoint (concludingPart r) (concludingPart s)) /\
    forall r : Fin 3, HasAPFreeEnumeration (concludingPart r) 3

/-- The unresolved two-set version of concluding remark 3. -/
def two_set_partition_question : Prop :=
  exists A B : Set PositiveNat, A ∪ B = Set.univ /\ Disjoint A B /\
    HasAPFreeEnumeration A 3 /\ HasAPFreeEnumeration B 3

/-- Concluding remark 5: there is a permutation of all integers with no
monotone 7-term arithmetic progression. -/
def integer_seven_term_construction : Prop :=
  exists p : IntegerPermutation, IntegerAPFree p 7

end LeanProofs.DavisEntringerGrahamSimmons1977

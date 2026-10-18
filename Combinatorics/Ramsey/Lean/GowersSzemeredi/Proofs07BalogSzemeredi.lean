import GowersSzemeredi.Proofs07DRC

/-!
# The quantitative Balog--Szemeredi reduction

This module develops Proposition 7.3, whose assembled form
`proposition_7_3_holds` is in `Proofs07BalogSzemerediSide`.  We use popular
*sums* rather than the popular differences in the paper; additive energy has the
same fibre-square description, while the resulting graph is automatically
symmetric.  The dependent-random-choice input is `lemma_7_4_holds`.

`proposition_7_3_holds` is in `Proofs07BalogSzemerediSide`, outside the final
route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise Combinatorics.Additive
open Finset

namespace LeanProofs.GowersSzemeredi

private def sumRep {G : Type*} [DecidableEq G] [Add G]
    (A : Finset G) (x : G) : Nat :=
  ((A ×ˢ A).filter fun ab => ab.1 + ab.2 = x).card

private noncomputable def popularSums {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real) : Finset G :=
  (A + A).filter fun x => c * A.card / 2 ≤ sumRep A x

private noncomputable def popularNeighbors {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real) (a : G) : Finset G :=
  A.filter fun b => a + b ∈ popularSums A c

private lemma sumRep_le_card {G : Type*} [DecidableEq G] [AddCommGroup G]
    (A : Finset G) (x : G) : sumRep A x ≤ A.card := by
  unfold sumRep
  let f : {ab // ab ∈ (A ×ˢ A).filter fun ab => ab.1 + ab.2 = x} → A :=
    fun ab => ⟨ab.1.1, (Finset.mem_product.mp (Finset.mem_filter.mp ab.2).1).1⟩
  have hf : Function.Injective f := by
    intro ab cd h
    apply Subtype.ext
    have hfst : ab.1.1 = cd.1.1 := congrArg Subtype.val h
    have hab := (Finset.mem_filter.mp ab.2).2
    have hcd := (Finset.mem_filter.mp cd.2).2
    apply Prod.ext hfst
    apply add_left_cancel (a := ab.1.1)
    calc
      ab.1.1 + ab.1.2 = x := hab
      _ = cd.1.1 + cd.1.2 := hcd.symm
      _ = ab.1.1 + cd.1.2 := by rw [hfst]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

private lemma sum_sumRep {G : Type*} [DecidableEq G] [AddCommGroup G]
    (A : Finset G) :
    ∑ x ∈ A + A, sumRep A x = A.card ^ 2 := by
  unfold sumRep
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilter :
      ((A ×ˢ A).filter fun ab => ab.1 + ab.2 ∈ A + A) = A ×ˢ A := by
    apply Finset.filter_eq_self.2
    intro ab hab
    exact add_mem_add (Finset.mem_product.mp hab).1 (Finset.mem_product.mp hab).2
  rw [hfilter, Finset.card_product, pow_two]

private lemma energy_eq_sum_sumRep_sq {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) :
    Finset.addEnergy A A = ∑ x ∈ A + A, sumRep A x ^ 2 := by
  simpa only [sumRep] using Finset.addEnergy_eq_sum_sq' A A

private lemma energy_le_card_cube {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) :
    Finset.addEnergy A A ≤ A.card ^ 3 := by
  rw [energy_eq_sum_sumRep_sq]
  calc
    ∑ x ∈ A + A, sumRep A x ^ 2 ≤
        ∑ x ∈ A + A, A.card * sumRep A x := by
      apply Finset.sum_le_sum
      intro x _
      rw [pow_two]
      exact Nat.mul_le_mul_right _ (sumRep_le_card A x)
    _ = A.card * ∑ x ∈ A + A, sumRep A x := by
      rw [Finset.mul_sum]
    _ = A.card ^ 3 := by rw [sum_sumRep]; ring

private lemma popularSums_card_lower {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real) (hc : 0 < c)
    (henergy : c * (A.card : Real) ^ 3 ≤ Finset.addEnergy A A) :
    c * A.card / 2 ≤ (popularSums A c).card := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [popularSums]
  have hm : (0 : Real) < A.card := by exact_mod_cast hA.card_pos
  rw [energy_eq_sum_sumRep_sq] at henergy
  push_cast at henergy
  -- a popular sum contributes at most `|A|^2`, an unpopular one at most `c |A| / 2` times `r(x)`
  have h := henergy.trans (Finset.sum_le_sum fun x _ =>
    show (sumRep A x : Real) ^ 2 ≤ (if c * A.card / 2 ≤ (sumRep A x : Real) then
      (A.card : Real) ^ 2 else 0) + c * A.card / 2 * sumRep A x by
    have hr : (sumRep A x : Real) ≤ A.card := by exact_mod_cast sumRep_le_card A x
    have hr0 : (0 : Real) ≤ sumRep A x := Nat.cast_nonneg _
    split_ifs with hx
    · linarith [mul_le_mul hr hr hr0 hm.le,
        mul_nonneg (by positivity : (0 : Real) ≤ c * A.card / 2) hr0]
    · linarith [mul_le_mul_of_nonneg_right (not_le.mp hx).le hr0])
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, ← Finset.mul_sum,
    nsmul_eq_mul, ← Nat.cast_sum, sum_sumRep, Nat.cast_pow] at h
  unfold popularSums
  nlinarith [sq_pos_of_pos hm]

private lemma sum_popularNeighbors_card {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real) :
    ∑ a ∈ A, (popularNeighbors A c a).card =
      ∑ x ∈ popularSums A c, sumRep A x := by
  have hleft :
      (∑ a ∈ A, (popularNeighbors A c a).card) =
        ((A ×ˢ A).filter fun ab => ab.1 + ab.2 ∈ popularSums A c).card := by
    simp only [popularNeighbors, Finset.card_filter]
    rw [Finset.sum_product]
  rw [hleft]
  symm
  unfold sumRep
  rw [Finset.sum_card_fiberwise_eq_card_filter]

private lemma popular_edge_count_lower {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real) (hc : 0 < c)
    (henergy : c * (A.card : Real) ^ 3 ≤ Finset.addEnergy A A) :
    c ^ 2 * (A.card : Real) ^ 2 / 4 ≤
      ∑ a ∈ A, ((popularNeighbors A c a).card : Real) := by
  rw [← Nat.cast_sum, sum_popularNeighbors_card]
  push_cast
  -- each of the at least `c |A| / 2` popular sums has at least `c |A| / 2` representations
  have hsum := Finset.card_nsmul_le_sum (popularSums A c) (fun x => (sumRep A x : Real))
    (c * A.card / 2) fun x hx => (Finset.mem_filter.mp hx).2
  rw [nsmul_eq_mul] at hsum
  nlinarith [mul_le_mul_of_nonneg_right (popularSums_card_lower A c hc henergy)
    (by positivity : (0 : Real) ≤ c * A.card / 2)]

private def bsgDelta (c : Real) : Real := c ^ 2 / 8

private noncomputable def highDegreeCenters {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real) : Finset G :=
  A.filter fun a => bsgDelta c * A.card ≤ (popularNeighbors A c a).card

private lemma highDegreeCenters_card_lower {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real) (hc : 0 < c)
    (henergy : c * (A.card : Real) ^ 3 ≤ Finset.addEnergy A A) :
    bsgDelta c * A.card ≤ (highDegreeCenters A c).card := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [bsgDelta, highDegreeCenters]
  have hm : (0 : Real) < A.card := by exact_mod_cast hA.card_pos
  have hδ : 0 < bsgDelta c * A.card := mul_pos (div_pos (pow_pos hc 2) (by norm_num)) hm
  -- a high-degree center has at most `|A|` neighbours, any other fewer than `δ |A|`
  have h := (popular_edge_count_lower A c hc henergy).trans (Finset.sum_le_sum fun a _ =>
    show ((popularNeighbors A c a).card : Real) ≤ (if bsgDelta c * A.card ≤
      ((popularNeighbors A c a).card : Real) then (A.card : Real) else 0) +
        bsgDelta c * A.card by
    have : ((popularNeighbors A c a).card : Real) ≤ A.card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    split_ifs <;> linarith)
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul] at h
  unfold highDegreeCenters
  unfold bsgDelta at h ⊢
  nlinarith

private def centerAt {G : Type*} [DecidableEq G] (V : Finset G)
    (i : Fin V.card) : G :=
  (V.equivFin.symm i).1

private lemma centerAt_mem {G : Type*} [DecidableEq G] (V : Finset G)
    (i : Fin V.card) : centerAt V i ∈ V :=
  (V.equivFin.symm i).2

private lemma centerAt_injective {G : Type*} [DecidableEq G] (V : Finset G) :
    Function.Injective (centerAt V) := by
  intro i j hij
  exact V.equivFin.symm.injective (Subtype.ext hij)

private noncomputable def indexedNeighborhood {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real)
    (V : Finset G) (i : Fin V.card) : Finset G :=
  popularNeighbors A c (centerAt V i)

private lemma indexedNeighborhood_card_lower {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real)
    (V : Finset G)
    (hV : ∀ a, a ∈ V →
      bsgDelta c * A.card ≤ (popularNeighbors A c a).card)
    (i : Fin V.card) :
    bsgDelta c * A.card ≤ (indexedNeighborhood A c V i).card := by
  exact hV _ (centerAt_mem V i)

private def goodIntersection {X I : Type*} [DecidableEq X]
    (A : I → Finset X) (threshold : Real) (i j : I) : Prop :=
  threshold ≤ ((A i ∩ A j).card : Real)

private noncomputable def goodDegree {X I : Type*} [DecidableEq X]
    [DecidableEq I] (A : I → Finset X) (K : Finset I)
    (threshold : Real) (i : I) : Nat := by
  classical
  exact (K.filter fun j => goodIntersection A threshold i j).card

private noncomputable def highGoodDegree {X I : Type*} [DecidableEq X]
    [DecidableEq I] (A : I → Finset X) (K : Finset I)
    (threshold : Real) : Finset I := by
  classical
  exact K.filter fun i => (4 : Real) / 5 * K.card ≤ goodDegree A K threshold i

private noncomputable def goodPairCount {X I : Type*} [DecidableEq X]
    [DecidableEq I] (A : I → Finset X) (K : Finset I)
    (threshold : Real) : Nat := by
  classical
  exact ((K ×ˢ K).filter fun (ij : I × I) =>
    goodIntersection A threshold ij.1 ij.2).card

private lemma sum_goodDegree_eq_pairCount {X I : Type*} [DecidableEq X]
    [DecidableEq I] (A : I → Finset X) (K : Finset I)
    (threshold : Real) :
    ∑ i ∈ K, goodDegree A K threshold i =
      goodPairCount A K threshold := by
  simp only [goodDegree, goodPairCount, Finset.card_filter]
  rw [Finset.sum_product]

private lemma highGoodDegree_card_lower {X I : Type*} [DecidableEq X]
    [DecidableEq I] (A : I → Finset X) (K : Finset I)
    (threshold : Real)
    (hdense : (9 : Real) / 10 * (K.card : Real) ^ 2 ≤
      (goodPairCount A K threshold : Real)) :
    (K.card : Real) / 2 ≤ (highGoodDegree A K threshold).card := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hK
  · simp
  have hsum : (goodPairCount A K threshold : Real) =
      ∑ i ∈ K, (goodDegree A K threshold i : Real) := by
    exact_mod_cast (sum_goodDegree_eq_pairCount A K threshold).symm
  -- a degree is at most `|K|`, and below `4 |K| / 5` off `highGoodDegree`
  have h := (hdense.trans_eq hsum).trans (Finset.sum_le_sum fun i _ =>
    show (goodDegree A K threshold i : Real) ≤ (if (4 : Real) / 5 * K.card ≤
      goodDegree A K threshold i then (K.card : Real) / 5 else 0) + 4 / 5 * K.card by
    have : (goodDegree A K threshold i : Real) ≤ K.card := by
      unfold goodDegree
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    split_ifs <;> linarith)
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul] at h
  unfold highGoodDegree
  have hk : (0 : Real) < K.card := by exact_mod_cast hK.card_pos
  nlinarith

private lemma bsg_delta_pos (c : Real) (hc : 0 < c) : 0 < bsgDelta c := by
  unfold bsgDelta
  positivity

private lemma exists_bsg_drc_core {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real) (hc : 0 < c)
    (henergy : c * (A.card : Real) ^ 3 ≤ Finset.addEnergy A A) :
    let V := highDegreeCenters A c
    let F := indexedNeighborhood A c V
    ∃ K : Finset (Fin V.card),
      bsgDelta c * A.card ≤ V.card ∧
      (2 : Real) ^ (-(1 : Real) / 2) * bsgDelta c ^ 5 * V.card ≤ K.card ∧
      (9 : Real) / 10 * (K.card : Real) ^ 2 ≤
        goodPairCount F K (bsgDelta c ^ 2 * A.card / 2) := by
  dsimp only
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact ⟨∅, by simp, by simp [highDegreeCenters], by simp⟩
  -- `c ≤ 1` since the energy is at most `|A| ^ 3`, so `δ = c ^ 2 / 8 ≤ 1` and Lemma 7.4 applies
  have hm : (0 : Real) < A.card := by exact_mod_cast hA.card_pos
  have hc1 : c ≤ 1 := by
    have : (Finset.addEnergy A A : Real) ≤ (A.card : Real) ^ 3 := by
      exact_mod_cast energy_le_card_cube A
    nlinarith [pow_pos hm 3]
  have hdelta1 : bsgDelta c ≤ 1 := by
    unfold bsgDelta
    nlinarith [sq_nonneg c, mul_nonneg hc.le (sub_nonneg.mpr hc1)]
  obtain ⟨K, hKcard, hKgood⟩ := (lemma_7_4_holds G A.card _ A
    (indexedNeighborhood A c (highDegreeCenters A c)) (bsgDelta c) rfl
    (fun _ => Finset.filter_subset _ _) (bsg_delta_pos c hc) hdelta1).2
    (indexedNeighborhood_card_lower A c (highDegreeCenters A c)
      fun _ ha => (Finset.mem_filter.mp ha).2)
  exact ⟨K, highDegreeCenters_card_lower A c hc henergy, hKcard, by
    simpa only [goodPairCount, goodIntersection, largeIntersectionPairCount] using hKgood⟩

private noncomputable def sumRepPairs {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (x : G) : Finset (G × G) := by
  classical
  exact (A ×ˢ A).filter fun ab => ab.1 + ab.2 = x

@[simp] private lemma card_sumRepPairs {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (x : G) :
    (sumRepPairs A x).card = sumRep A x := rfl

private noncomputable def fourReps {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (x : G) : Finset (Fin 4 → G) := by
  classical
  exact (Fintype.piFinset fun _ : Fin 4 => A).filter fun q =>
    q 0 + q 1 - q 2 - q 3 = x

private abbrev QuadWitness (G : Type*) := Σ _b : G, (G × G) × (G × G)

private noncomputable def quadWitnesses {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real) (u v : G) :
    Finset (QuadWitness G) :=
  (popularNeighbors A c u ∩ popularNeighbors A c v).sigma fun b =>
    sumRepPairs A (u + b) ×ˢ sumRepPairs A (v + b)

private def quadWitnessTuple {G : Type*} [DecidableEq G] [AddCommGroup G]
    (w : QuadWitness G) : Fin 4 → G :=
  ![w.2.1.1, w.2.1.2, w.2.2.1, w.2.2.2]

private lemma quadWitnessTuple_mem {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real) (u v : G)
    (w : QuadWitness G) (hwmem : w ∈ quadWitnesses A c u v) :
    quadWitnessTuple w ∈ fourReps A (u - v) := by
  obtain ⟨b, ⟨p1, p2⟩, ⟨q1, q2⟩⟩ := w
  simp only [quadWitnesses, sumRepPairs, Finset.mem_sigma, Finset.mem_product,
    Finset.mem_filter] at hwmem
  obtain ⟨-, ⟨⟨hp1, hp2⟩, hp⟩, ⟨hq1, hq2⟩, hq⟩ := hwmem
  refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩
  · fin_cases i <;> simp [quadWitnessTuple, hp1, hp2, hq1, hq2]
  · show p1 + p2 - q1 - q2 = u - v
    rw [sub_sub, hp, hq, add_sub_add_right_eq_sub]

private lemma quadWitnessTuple_injOn {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real) (u v : G) :
    Set.InjOn quadWitnessTuple (quadWitnesses A c u v : Set (QuadWitness G)) := by
  rintro ⟨b, ⟨p1, p2⟩, ⟨q1, q2⟩⟩ hw ⟨b', ⟨p1', p2'⟩, ⟨q1', q2'⟩⟩ hw' h
  obtain ⟨rfl, rfl, rfl, rfl⟩ : p1 = p1' ∧ p2 = p2' ∧ q1 = q1' ∧ q2 = q2' :=
    ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3⟩
  -- the centre is determined by `p1 + p2 = u + b`
  obtain rfl : b = b' := add_left_cancel
    ((Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_sigma.mp hw).2).1).2.symm.trans
      (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_sigma.mp hw').2).1).2)
  rfl

private lemma quadWitnesses_card_lower {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real) (hc : 0 < c) (u v : G) :
    ((popularNeighbors A c u ∩ popularNeighbors A c v).card : Real) *
        (c * A.card / 2) ^ 2 ≤ (quadWitnesses A c u v).card := by
  rw [quadWitnesses, Finset.card_sigma]
  push_cast
  calc
    _ = ∑ _b ∈ popularNeighbors A c u ∩ popularNeighbors A c v,
        (c * A.card / 2) ^ 2 := by simp [mul_comm]
    _ ≤ ∑ b ∈ popularNeighbors A c u ∩ popularNeighbors A c v,
        ((sumRepPairs A (u + b)).card : Real) *
          (sumRepPairs A (v + b)).card := by
      apply Finset.sum_le_sum
      intro b hb
      have hbu := (Finset.mem_inter.mp hb).1
      have hbv := (Finset.mem_inter.mp hb).2
      have hru : c * A.card / 2 ≤ (sumRepPairs A (u + b)).card := by
        simpa only [card_sumRepPairs] using
          (Finset.mem_filter.mp (Finset.mem_filter.mp hbu).2).2
      have hrv : c * A.card / 2 ≤ (sumRepPairs A (v + b)).card := by
        simpa only [card_sumRepPairs] using
          (Finset.mem_filter.mp (Finset.mem_filter.mp hbv).2).2
      rw [pow_two]
      exact mul_le_mul hru hrv (by positivity) (by positivity)
    _ = _ := by norm_num

private lemma fourReps_card_lower_of_good {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c delta : Real)
    (hc : 0 < c) (u v : G)
    (hgood : delta ^ 2 * A.card / 2 ≤
      ((popularNeighbors A c u ∩ popularNeighbors A c v).card : Real)) :
    delta ^ 2 * c ^ 2 * (A.card : Real) ^ 3 / 8 ≤
      (fourReps A (u - v)).card := by
  have hcard : ((quadWitnesses A c u v).card : Real) ≤ (fourReps A (u - v)).card := by
    exact_mod_cast Finset.card_le_card_of_injOn quadWitnessTuple
      (quadWitnessTuple_mem A c u v) (quadWitnessTuple_injOn A c u v)
  linarith [quadWitnesses_card_lower A c hc u v,
    mul_le_mul_of_nonneg_right hgood (sq_nonneg (c * (A.card : Real) / 2))]

private noncomputable def goodIndexNeighbors {X I : Type*} [DecidableEq X]
    [DecidableEq I] (A : I → Finset X) (K : Finset I)
    (threshold : Real) (i : I) : Finset I := by
  classical
  exact K.filter fun j => goodIntersection A threshold i j

private lemma common_goodIndexNeighbors_card_lower {X I : Type*}
    [DecidableEq X] [DecidableEq I] (A : I → Finset X)
    (K : Finset I) (threshold : Real)
    {i j : I} (hi : i ∈ highGoodDegree A K threshold)
    (hj : j ∈ highGoodDegree A K threshold) :
    (3 : Real) / 5 * K.card ≤
      ((goodIndexNeighbors A K threshold i ∩
        goodIndexNeighbors A K threshold j).card : Real) := by
  classical
  -- `|Gi ∩ Gj| = |Gi| + |Gj| - |Gi ∪ Gj| ≥ 4 |K| / 5 + 4 |K| / 5 - |K|`
  set Gi := goodIndexNeighbors A K threshold i
  set Gj := goodIndexNeighbors A K threshold j
  have hGi : (4 : Real) / 5 * K.card ≤ Gi.card := (Finset.mem_filter.mp hi).2
  have hGj : (4 : Real) / 5 * K.card ≤ Gj.card := (Finset.mem_filter.mp hj).2
  have hU : ((Gi ∪ Gj).card : Real) ≤ K.card := Nat.cast_le.mpr <|
    Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))
  have hI : ((Gi ∪ Gj).card : Real) + (Gi ∩ Gj).card = Gi.card + Gj.card := by
    exact_mod_cast Finset.card_union_add_card_inter Gi Gj
  linarith

private noncomputable def eightReps {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (x : G) : Finset (Fin 8 → G) := by
  classical
  exact (Fintype.piFinset fun _ : Fin 8 => A).filter fun q =>
    (q 0 + q 1 - q 2 - q 3) - (q 4 + q 5 - q 6 - q 7) = x

private abbrev OctWitness (I G : Type*) := Σ _t : I, (Fin 4 → G) × (Fin 4 → G)

private noncomputable def octWitnesses {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c delta : Real)
    (V : Finset G) (K : Finset (Fin V.card)) (i j : Fin V.card) :
    Finset (OctWitness (Fin V.card) G) :=
  let F := indexedNeighborhood A c V
  let threshold := delta ^ 2 * A.card / 2
  (goodIndexNeighbors F K threshold i ∩
      goodIndexNeighbors F K threshold j).sigma fun t =>
    fourReps A (centerAt V i - centerAt V t) ×ˢ
      fourReps A (centerAt V j - centerAt V t)

private def octWitnessTuple {I G : Type*}
    (w : OctWitness I G) : Fin 8 → G :=
  Fin.append w.2.1 w.2.2

private lemma octWitnessTuple_mem {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c delta : Real)
    (V : Finset G) (K : Finset (Fin V.card)) (i j : Fin V.card)
    (w : OctWitness (Fin V.card) G)
    (hwmem : w ∈ octWitnesses A c delta V K i j) :
    octWitnessTuple w ∈ eightReps A (centerAt V i - centerAt V j) := by
  obtain ⟨t, q, r⟩ := w
  simp only [octWitnesses, fourReps, Finset.mem_sigma, Finset.mem_product, Finset.mem_filter,
    Fintype.mem_piFinset] at hwmem
  obtain ⟨-, ⟨hqA, hq⟩, hrA, hr⟩ := hwmem
  refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun a => ?_, ?_⟩
  · refine Fin.addCases (m := 4) (n := 4) (fun x => ?_) (fun x => ?_) a <;>
      simp only [octWitnessTuple, Fin.append_left, Fin.append_right, hqA, hrA]
  · show q 0 + q 1 - q 2 - q 3 - (r 0 + r 1 - r 2 - r 3) = centerAt V i - centerAt V j
    rw [hq, hr, sub_sub_sub_cancel_right]

private lemma octWitnessTuple_injOn {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c delta : Real)
    (V : Finset G) (K : Finset (Fin V.card)) (i j : Fin V.card) :
    Set.InjOn octWitnessTuple
      (octWitnesses A c delta V K i j : Set (OctWitness (Fin V.card) G)) := by
  rintro ⟨t, q, r⟩ hw ⟨t', q', r'⟩ hw' h
  obtain rfl : q = q' := funext fun a => by
    simpa only [octWitnessTuple, Fin.append_left] using congrFun h (Fin.castAdd 4 a)
  obtain rfl : r = r' := funext fun a => by
    simpa only [octWitnessTuple, Fin.append_right] using congrFun h (Fin.natAdd 4 a)
  -- the centre is determined by `q 0 + q 1 - q 2 - q 3 = centerAt V i - centerAt V t`
  obtain rfl : t = t' := centerAt_injective V (sub_right_inj.mp
    ((Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_sigma.mp hw).2).1).2.symm.trans
      (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_sigma.mp hw').2).1).2))
  rfl

private lemma octWitnesses_card_lower {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c delta : Real) (hc : 0 < c)
    (V : Finset G) (K : Finset (Fin V.card)) (i j : Fin V.card) :
    let F := indexedNeighborhood A c V
    let threshold := delta ^ 2 * A.card / 2
    ((goodIndexNeighbors F K threshold i ∩
      goodIndexNeighbors F K threshold j).card : Real) *
        (delta ^ 2 * c ^ 2 * (A.card : Real) ^ 3 / 8) ^ 2 ≤
      (octWitnesses A c delta V K i j).card := by
  classical
  dsimp only
  -- every common good neighbour `t` carries two fibres of `fourReps`
  rw [octWitnesses, Finset.card_sigma, Nat.cast_sum, ← nsmul_eq_mul]
  refine Finset.card_nsmul_le_sum _ _ _ fun t ht => ?_
  rw [Finset.card_product, Nat.cast_mul, pow_two]
  exact mul_le_mul
    (fourReps_card_lower_of_good A c delta hc (centerAt V i) (centerAt V t)
      (Finset.mem_filter.mp (Finset.mem_inter.mp ht).1).2)
    (fourReps_card_lower_of_good A c delta hc (centerAt V j) (centerAt V t)
      (Finset.mem_filter.mp (Finset.mem_inter.mp ht).2).2) (by positivity) (by positivity)

private lemma bsg_K_card_lower (Acard : Nat) (delta : Real)
    (hdelta : 0 ≤ delta) {Vcard Kcard : Nat}
    (hV : delta * Acard ≤ Vcard)
    (hK : (2 : Real) ^ (-(1 : Real) / 2) * delta ^ 5 * Vcard ≤ Kcard) :
    (2 : Real) ^ (-(1 : Real) / 2) * delta ^ 6 * Acard ≤ Kcard := by
  have hcoef : 0 ≤ (2 : Real) ^ (-(1 : Real) / 2) * delta ^ 5 := by positivity
  calc
    (2 : Real) ^ (-(1 : Real) / 2) * delta ^ 6 * Acard =
        ((2 : Real) ^ (-(1 : Real) / 2) * delta ^ 5) *
          (delta * Acard) := by ring
    _ ≤ ((2 : Real) ^ (-(1 : Real) / 2) * delta ^ 5) * Vcard :=
      mul_le_mul_of_nonneg_left hV hcoef
    _ ≤ Kcard := hK

private lemma eightReps_card_lower_of_core {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c delta : Real)
    (hc : 0 < c)
    (V : Finset G) (K : Finset (Fin V.card))
    (hK : (2 : Real) ^ (-(1 : Real) / 2) * delta ^ 6 * A.card ≤ K.card)
    {i j : Fin V.card}
    (hi : i ∈ highGoodDegree (indexedNeighborhood A c V) K
      (delta ^ 2 * A.card / 2))
    (hj : j ∈ highGoodDegree (indexedNeighborhood A c V) K
      (delta ^ 2 * A.card / 2)) :
    (2 : Real) ^ (-(1 : Real) / 2) * delta ^ 10 * c ^ 4 *
        (A.card : Real) ^ 7 / 120 ≤
      (eightReps A (centerAt V i - centerAt V j)).card := by
  have hW := common_goodIndexNeighbors_card_lower _ K _ hi hj
  have hoct := octWitnesses_card_lower A c delta hc V K i j
  dsimp only at hoct
  refine le_trans ?_ (hoct.trans (by
    exact_mod_cast Finset.card_le_card_of_injOn octWitnessTuple
      (octWitnessTuple_mem A c delta V K i j) (octWitnessTuple_injOn A c delta V K i j)))
  have hR := sq_nonneg (delta ^ 2 * c ^ 2 * (A.card : Real) ^ 3 / 8)
  linarith [mul_le_mul_of_nonneg_right hW hR, mul_le_mul_of_nonneg_right hK hR,
    (by positivity : (0 : Real) ≤ (2 : Real) ^ (-(1 : Real) / 2) * c ^ 4 *
      (A.card : Real) ^ 7 * delta ^ 10)]

private lemma sum_eightReps_card_le {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A S : Finset G) :
    ∑ x ∈ S, (eightReps A x).card ≤ A.card ^ 8 := by
  unfold eightReps
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  calc
    _ ≤ (Fintype.piFinset fun _ : Fin 8 => A).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = A.card ^ 8 := by simp

/-- The group-valued form of Proposition 7.3 used for modular graphs. -/
theorem proposition_7_3_group_holds {G : Type*} [DecidableEq G]
    [AddCommGroup G] (A : Finset G) (c : Real) (hc : 0 < c)
    (henergy : c * (A.card : Real) ^ 3 ≤ Finset.addEnergy A A) :
    ∃ A'' : Finset G,
      A'' ⊆ A ∧
      (2 : Real) ^ (-(20 : Real)) * c ^ 12 * A.card ≤ A''.card ∧
      ((A'' - A'').card : Real) ≤
        (2 : Real) ^ (38 : Nat) * c ^ (-(24 : Real)) * A.card := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact ⟨∅, by simp, by simp, by simp⟩
  have hm : (0 : Real) < A.card := by exact_mod_cast hA.card_pos
  let V := highDegreeCenters A c
  obtain ⟨K, hVcard, hKcard, hKdense⟩ := exists_bsg_drc_core A c hc henergy
  let L := highGoodDegree (indexedNeighborhood A c V) K (bsgDelta c ^ 2 * A.card / 2)
  have hL : (K.card : Real) / 2 ≤ L.card := highGoodDegree_card_lower _ K _ hKdense
  have hdelta := bsg_delta_pos c hc
  have hK := bsg_K_card_lower A.card _ hdelta.le hVcard hKcard
  have hhalf : (1 / 2 : Real) ≤ (2 : Real) ^ (-(1 : Real) / 2) :=
    (show (1 / 2 : Real) = 2 ^ (-1 : Real) by norm_num).trans_le
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  refine ⟨L.image (centerAt V), Finset.image_subset_iff.2 fun i _ =>
    (Finset.mem_filter.mp (centerAt_mem V i)).1, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (centerAt_injective V),
      show (2 : Real) ^ (-(20 : Real)) = 1 / 1048576 by norm_num]
    unfold bsgDelta at hK
    linarith [mul_le_mul_of_nonneg_right hhalf
      (by positivity : (0 : Real) ≤ (c ^ 2 / 8) ^ 6 * A.card)]
  -- every difference has many representations, while there are only `|A|^8` in total
  · set D := L.image (centerAt V) - L.image (centerAt V)
    have hsum := Finset.card_nsmul_le_sum D (fun x => ((eightReps A x).card : Real))
      ((2 : Real) ^ (-(1 : Real) / 2) * bsgDelta c ^ 10 * c ^ 4 * (A.card : Real) ^ 7 / 120)
      fun x hx => by
        obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
        exact eightReps_card_lower_of_core A c _ hc V K hK hi hj
    have hup : ∑ x ∈ D, ((eightReps A x).card : Real) ≤ A.card ^ 8 := by
      exact_mod_cast sum_eightReps_card_le A D
    rw [nsmul_eq_mul, bsgDelta] at hsum
    rw [Real.rpow_neg hc.le, Real.rpow_ofNat, mul_right_comm, ← div_eq_mul_inv,
      le_div_iff₀ (pow_pos hc 24)]
    refine le_of_mul_le_mul_right ?_ (pow_pos hm 7)
    linarith [mul_le_mul_of_nonneg_right hhalf
      (by positivity : (0 : Real) ≤ D.card * c ^ 24 * A.card ^ 7), pow_pos hm 8]

end LeanProofs.GowersSzemeredi

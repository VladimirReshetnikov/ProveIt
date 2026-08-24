import GowersSzemeredi.Sections06_07
import Mathlib.Algebra.Order.Chebyshev

/-!
# Proof of Gowers's dependent-random-choice lemma

This module proves Lemma 7.4 by counting ordered five-tuples in the finite
ambient set.  The statement module records the necessary density hypothesis
`delta <= 1`, implicit in the paper.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

private abbrev DRCIndex := Fin 5

private noncomputable def drcSamples {X : Type*} [DecidableEq X]
    (V : Finset X) : Finset (DRCIndex -> X) :=
  Fintype.piFinset fun _ : DRCIndex => V

private noncomputable def drcCore {X : Type*} [DecidableEq X] {n : Nat}
    (A : Fin n -> Finset X) (t : DRCIndex -> X) : Finset (Fin n) :=
  Finset.univ.filter fun i => forall r, t r ∈ A i

private noncomputable def drcBadPairCount {X : Type*} [DecidableEq X] {n : Nat}
    (A : Fin n -> Finset X) (K : Finset (Fin n)) (m : Nat)
    (delta : Real) : Nat :=
  ((K ×ˢ K).filter fun ij =>
    ((((A ij.1 ∩ A ij.2).card : Nat) : Real) < delta ^ 2 * m / 2)).card

private noncomputable def drcScore {X : Type*} [DecidableEq X] {n : Nat}
    (A : Fin n -> Finset X) (t : DRCIndex -> X) (m : Nat)
    (delta : Real) : Real :=
  ((drcCore A t).card : Real) ^ 2 -
    10 * (drcBadPairCount A (drcCore A t) m delta : Real)

private noncomputable def incidenceDegree {X : Type*} [DecidableEq X]
    {n : Nat} (A : Fin n -> Finset X) (x : X) : Nat :=
  Finset.univ.filter (fun i => x ∈ A i) |>.card

private lemma drcSamples_card {X : Type*} [DecidableEq X] (V : Finset X) :
    (drcSamples V).card = V.card ^ 5 := by
  simp [drcSamples, DRCIndex]

private lemma drcCore_card_sq {X : Type*} [DecidableEq X] {n : Nat}
    (A : Fin n -> Finset X) (t : DRCIndex -> X) :
    ((drcCore A t).card : Real) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n,
        if (forall r, t r ∈ A i ∩ A j) then 1 else 0 := by
  classical
  simp only [drcCore, card_filter]
  push_cast
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_one]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : forall r, t r ∈ A i
  · by_cases hj : forall r, t r ∈ A j
    · have hij : forall r, t r ∈ A i ∩ A j := fun r => by simp [hi r, hj r]
      rw [if_pos hij]
      simp [hi, hj]
    · have hn : ¬ (forall r, t r ∈ A i ∩ A j) := by
        intro h
        exact hj fun r => (Finset.mem_inter.mp (h r)).2
      rw [if_neg hn]
      simp [hi, hj]
  · have hn : ¬ (forall r, t r ∈ A i ∩ A j) := by
      intro h
      exact hi fun r => (Finset.mem_inter.mp (h r)).1
    rw [if_neg hn]
    simp [hi]

private lemma incidenceDegree_sq {X : Type*} [DecidableEq X] {n : Nat}
    (A : Fin n -> Finset X) (x : X) :
    (incidenceDegree A x : Real) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n,
        if x ∈ A i ∩ A j then 1 else 0 := by
  simpa [incidenceDegree, drcCore] using
    (drcCore_card_sq A (fun _ : DRCIndex => x))

private lemma sum_incidenceDegree {X : Type*} [DecidableEq X] {n : Nat}
    (V : Finset X) (A : Fin n -> Finset X) (hA : forall i, A i ⊆ V) :
    ∑ x ∈ V, (incidenceDegree A x : Real) =
      ∑ i : Fin n, ((A i).card : Real) := by
  classical
  simp_rw [incidenceDegree, Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ x ∈ V, if x ∈ A i then (1 : Real) else 0) =
        ((V ∩ A i).card : Real) := by simp
    _ = ((A i).card : Real) := by rw [Finset.inter_eq_right.mpr (hA i)]

private lemma sum_intersection_eq_sum_degree_sq {X : Type*} [DecidableEq X]
    {n : Nat} (V : Finset X) (A : Fin n -> Finset X)
    (hA : forall i, A i ⊆ V) :
    (∑ i : Fin n, ∑ j : Fin n,
        (((A i ∩ A j).card : Nat) : Real)) =
      ∑ x ∈ V, (incidenceDegree A x : Real) ^ 2 := by
  classical
  have hinter (i j : Fin n) :
      (((A i ∩ A j).card : Nat) : Real) =
        ∑ x ∈ V, if x ∈ A i ∩ A j then (1 : Real) else 0 := by
    have hfilter : V.filter (fun x => x ∈ A i ∩ A j) = A i ∩ A j := by
      ext x
      simp only [mem_filter]
      constructor
      · exact fun hx => hx.2
      · intro hx
        exact ⟨hA i (Finset.mem_inter.mp hx).1, hx⟩
    rw [Finset.sum_boole]
    norm_cast
    exact congrArg Finset.card hfilter.symm
  simp_rw [hinter]
  calc
    (∑ i : Fin n, ∑ j : Fin n, ∑ x ∈ V,
        if x ∈ A i ∩ A j then (1 : Real) else 0) =
        ∑ i : Fin n, ∑ x ∈ V, ∑ j : Fin n,
          if x ∈ A i ∩ A j then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ x ∈ V, ∑ i : Fin n, ∑ j : Fin n,
          if x ∈ A i ∩ A j then (1 : Real) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ V, (incidenceDegree A x : Real) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (incidenceDegree_sq A x).symm

private lemma drcSamples_filter_inter {X : Type*} [DecidableEq X] {n : Nat}
    (V : Finset X) (A : Fin n -> Finset X) (hA : forall i, A i ⊆ V)
    (i j : Fin n) :
    (drcSamples V).filter (fun t => forall r, t r ∈ A i ∩ A j) =
      drcSamples (A i ∩ A j) := by
  classical
  ext t
  simp only [mem_filter, drcSamples, Fintype.mem_piFinset]
  constructor
  · exact fun h r => h.2 r
  · intro h
    refine ⟨?_, h⟩
    intro r
    exact hA i (Finset.mem_inter.mp (h r)).1

private lemma sum_drcCore_card_sq {X : Type*} [DecidableEq X] {n : Nat}
    (V : Finset X) (A : Fin n -> Finset X) (hA : forall i, A i ⊆ V) :
    ∑ t ∈ drcSamples V, ((drcCore A t).card : Real) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n,
        (((A i ∩ A j).card : Nat) : Real) ^ 5 := by
  classical
  simp_rw [drcCore_card_sq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ t ∈ drcSamples V,
        if (forall r, t r ∈ A i ∩ A j) then (1 : Real) else 0) =
        (((drcSamples V).filter
          (fun t => forall r, t r ∈ A i ∩ A j)).card : Nat) := by
      simp
    _ = ((drcSamples (A i ∩ A j)).card : Real) := by
      rw [drcSamples_filter_inter V A hA i j]
    _ = (((A i ∩ A j).card : Nat) : Real) ^ 5 := by
      rw [drcSamples_card]
      norm_cast

private lemma drcBadPairCount_eq_sum {X : Type*} [DecidableEq X] {n : Nat}
    (A : Fin n -> Finset X) (K : Finset (Fin n)) (m : Nat)
    (delta : Real) :
    (drcBadPairCount A K m delta : Real) =
      ∑ i ∈ K, ∑ j ∈ K,
        if ((((A i ∩ A j).card : Nat) : Real) < delta ^ 2 * m / 2)
          then 1 else 0 := by
  classical
  unfold drcBadPairCount
  rw [Finset.card_filter]
  push_cast
  rw [Finset.sum_product]

private lemma sum_drcBadPairCount {X : Type*} [DecidableEq X] {n : Nat}
    (V : Finset X) (A : Fin n -> Finset X) (hA : forall i, A i ⊆ V)
    (m : Nat) (delta : Real) :
    ∑ t ∈ drcSamples V, (drcBadPairCount A (drcCore A t) m delta : Real) =
      ∑ i : Fin n, ∑ j : Fin n,
        if ((((A i ∩ A j).card : Nat) : Real) < delta ^ 2 * m / 2)
          then (((A i ∩ A j).card : Nat) : Real) ^ 5 else 0 := by
  classical
  simp_rw [drcBadPairCount_eq_sum]
  -- Expand membership in the random core and exchange the three finite sums.
  simp_rw [drcCore, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hspread (t : DRCIndex -> X) :
      (if (forall r, t r ∈ A i) then
          ∑ j : Fin n,
            if (forall r, t r ∈ A j) then
              if ((((A i ∩ A j).card : Nat) : Real) < delta ^ 2 * m / 2)
                then (1 : Real) else 0
            else 0
        else 0) =
        ∑ j : Fin n,
          if (forall r, t r ∈ A i) then
            if (forall r, t r ∈ A j) then
              if ((((A i ∩ A j).card : Nat) : Real) < delta ^ 2 * m / 2)
                then (1 : Real) else 0
            else 0
          else 0 := by
    rw [Finset.sum_ite_irrel]
    simp
  simp_rw [hspread]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hbad :
      ((((A i ∩ A j).card : Nat) : Real) < delta ^ 2 * m / 2)
  · simp only [hbad, if_true]
    calc
      (∑ t ∈ drcSamples V,
          if (forall r, t r ∈ A i) then
            if (forall r, t r ∈ A j) then (1 : Real) else 0
          else 0) =
          ∑ t ∈ drcSamples V,
            if (forall r, t r ∈ A i ∩ A j) then (1 : Real) else 0 := by
        apply Finset.sum_congr rfl
        intro t _
        by_cases hi : forall r, t r ∈ A i
        · by_cases hj : forall r, t r ∈ A j
          · have hij : forall r, t r ∈ A i ∩ A j :=
              fun r => by simp [hi r, hj r]
            rw [if_pos hi, if_pos hj, if_pos hij]
          · have hn : ¬ (forall r, t r ∈ A i ∩ A j) := by
              intro h
              exact hj fun r => (Finset.mem_inter.mp (h r)).2
            rw [if_pos hi, if_neg hj, if_neg hn]

        · have hn : ¬ (forall r, t r ∈ A i ∩ A j) := by
            intro h
            exact hi fun r => (Finset.mem_inter.mp (h r)).1
          rw [if_neg hi, if_neg hn]
      _ = (((A i ∩ A j).card : Nat) : Real) ^ 5 := by
        calc
          _ = (((drcSamples V).filter
              (fun t => forall r, t r ∈ A i ∩ A j)).card : Real) := by simp
          _ = ((drcSamples (A i ∩ A j)).card : Real) := by
            rw [drcSamples_filter_inter V A hA i j]
          _ = _ := by rw [drcSamples_card]; norm_cast
  · simp [hbad]

private lemma intersection_fifth_moment_lower {X : Type*} [DecidableEq X]
    {n m : Nat} (A : Fin n -> Finset X) (delta : Real)
    (hdelta : 0 < delta)
    (hsum : delta ^ 2 * m * (n : Real) ^ 2 <=
      ∑ i : Fin n, ∑ j : Fin n,
        (((A i ∩ A j).card : Nat) : Real)) :
    delta ^ 10 * (m : Real) ^ 5 * (n : Real) ^ 2 <=
      ∑ i : Fin n, ∑ j : Fin n,
        (((A i ∩ A j).card : Nat) : Real) ^ 5 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  have hnR : (0 : Real) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let P : Finset (Fin n × Fin n) := Finset.univ ×ˢ Finset.univ
  let f : Fin n × Fin n -> Real := fun ij =>
    (((A ij.1 ∩ A ij.2).card : Nat) : Real)
  have hpow := pow_sum_le_card_mul_sum_pow
    (s := P) (f := f) (fun _ _ => by positivity) 4
  have hsumP :
      delta ^ 2 * m * (n : Real) ^ 2 <= ∑ ij ∈ P, f ij := by
    dsimp [P, f]
    rw [Fintype.sum_prod_type]
    exact hsum
  have hPcard : (P.card : Real) = (n : Real) ^ 2 := by
    simp [P, pow_two]
  have hmomentP :
      ∑ ij ∈ P, f ij ^ 5 =
        ∑ i : Fin n, ∑ j : Fin n,
          (((A i ∩ A j).card : Nat) : Real) ^ 5 := by
    dsimp [P, f]
    rw [Fintype.sum_prod_type]
  have hraise := pow_le_pow_left₀ (by positivity :
      0 <= delta ^ 2 * (m : Real) * (n : Real) ^ 2) hsumP 5
  have hcombined :
      (delta ^ 2 * (m : Real) * (n : Real) ^ 2) ^ 5 <=
        ((n : Real) ^ 2) ^ 4 *
          (∑ i : Fin n, ∑ j : Fin n,
            (((A i ∩ A j).card : Nat) : Real) ^ 5) := by
    calc
      _ <= (∑ ij ∈ P, f ij) ^ 5 := hraise
      _ <= (P.card : Real) ^ 4 * ∑ ij ∈ P, f ij ^ 5 := hpow
      _ = _ := by
        rw [hPcard, hmomentP]
  have hmul :
      ((n : Real) ^ 2) ^ 4 *
          (delta ^ 10 * (m : Real) ^ 5 * (n : Real) ^ 2) <=
        ((n : Real) ^ 2) ^ 4 *
          (∑ i : Fin n, ∑ j : Fin n,
            (((A i ∩ A j).card : Nat) : Real) ^ 5) := by
    calc
      _ = (delta ^ 2 * (m : Real) * (n : Real) ^ 2) ^ 5 := by ring
      _ <= _ := hcombined
  exact le_of_mul_le_mul_left hmul (by positivity)

private lemma bad_fifth_moment_upper {X : Type*} [DecidableEq X]
    {n m : Nat} (A : Fin n -> Finset X) (delta : Real)
    (hdelta : 0 < delta) :
    (∑ i : Fin n, ∑ j : Fin n,
        if ((((A i ∩ A j).card : Nat) : Real) < delta ^ 2 * m / 2)
          then (((A i ∩ A j).card : Nat) : Real) ^ 5 else 0) <=
      delta ^ 10 * (m : Real) ^ 5 * (n : Real) ^ 2 / 32 := by
  calc
    _ <= ∑ _i : Fin n, ∑ _j : Fin n,
        (delta ^ 2 * (m : Real) / 2) ^ 5 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hbad :
          ((((A i ∩ A j).card : Nat) : Real) < delta ^ 2 * m / 2)
      · rw [if_pos hbad]
        exact pow_le_pow_left₀ (by positivity) (le_of_lt hbad) 5
      · rw [if_neg hbad]
        positivity
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

private lemma large_add_bad_eq_sq {X : Type*} [DecidableEq X] {n : Nat}
    (A : Fin n -> Finset X) (K : Finset (Fin n)) (m : Nat)
    (delta : Real) :
    (largeIntersectionPairCount A K (delta ^ 2 * m / 2) : Real) +
        (drcBadPairCount A K m delta : Real) = (K.card : Real) ^ 2 := by
  classical
  let p : Fin n × Fin n -> Prop := fun ij =>
    delta ^ 2 * (m : Real) / 2 <=
      (((A ij.1 ∩ A ij.2).card : Nat) : Real)
  have h := Finset.card_filter_add_card_filter_not
    (s := K ×ˢ K) p
  have hR := congrArg (fun q : Nat => (q : Real)) h
  simpa [largeIntersectionPairCount, drcBadPairCount, p, not_le,
    Finset.card_product, pow_two] using hR

private lemma exists_drc_sample {X : Type*} [DecidableEq X] {n m : Nat}
    (V : Finset X) (A : Fin n -> Finset X) (hV : V.card = m)
    (hA : forall i, A i ⊆ V) (delta : Real) (hdelta : 0 < delta)
    (hsum : delta ^ 2 * m * (n : Real) ^ 2 <=
      ∑ i : Fin n, ∑ j : Fin n,
        (((A i ∩ A j).card : Nat) : Real))
    (hm : 0 < m) :
    exists t, t ∈ drcSamples V /\
      (11 : Real) / 16 * delta ^ 10 * (n : Real) ^ 2 <=
        drcScore A t m delta := by
  classical
  have hcore :
      delta ^ 10 * (m : Real) ^ 5 * (n : Real) ^ 2 <=
        ∑ t ∈ drcSamples V, ((drcCore A t).card : Real) ^ 2 := by
    rw [sum_drcCore_card_sq V A hA]
    exact intersection_fifth_moment_lower A delta hdelta hsum
  have hbad :
      (∑ t ∈ drcSamples V,
          (drcBadPairCount A (drcCore A t) m delta : Real)) <=
        delta ^ 10 * (m : Real) ^ 5 * (n : Real) ^ 2 / 32 := by
    rw [sum_drcBadPairCount V A hA m delta]
    exact bad_fifth_moment_upper A delta hdelta
  have hscore :
      (11 : Real) / 16 * delta ^ 10 * (m : Real) ^ 5 * (n : Real) ^ 2 <=
        ∑ t ∈ drcSamples V, drcScore A t m delta := by
    simp_rw [drcScore]
    rw [Finset.sum_sub_distrib]
    simp_rw [← Finset.mul_sum]
    have hD : 0 <= delta ^ 10 * (m : Real) ^ 5 * (n : Real) ^ 2 := by
      positivity
    nlinarith
  have hsamples : (drcSamples V).Nonempty := by
    rw [← Finset.card_pos, drcSamples_card, hV]
    positivity
  have havg :
      ∑ _t ∈ drcSamples V,
          ((11 : Real) / 16 * delta ^ 10 * (n : Real) ^ 2) <=
        ∑ t ∈ drcSamples V, drcScore A t m delta := by
    calc
      _ = (11 : Real) / 16 * delta ^ 10 * (m : Real) ^ 5 *
          (n : Real) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [drcSamples_card, hV]
        push_cast
        ring
      _ <= _ := hscore
  obtain ⟨t, ht, htle⟩ := Finset.exists_le_of_sum_le hsamples havg
  exact ⟨t, ht, htle⟩

private lemma hasDenseIntersectionCore_of_score {X : Type*} [DecidableEq X]
    {n m : Nat} (A : Fin n -> Finset X) (delta : Real)
    (hdelta : 0 < delta) (t : DRCIndex -> X)
    (hscore : (11 : Real) / 16 * delta ^ 10 * (n : Real) ^ 2 <=
      drcScore A t m delta) :
    HasDenseIntersectionCore m A delta := by
  classical
  let K := drcCore A t
  let q : Real := K.card
  let b : Real := drcBadPairCount A K m delta
  have hb : 0 <= b := by positivity
  have hmain_nonneg :
      0 <= (11 : Real) / 16 * delta ^ 10 * (n : Real) ^ 2 := by
    positivity
  have hq_sq :
      (11 : Real) / 16 * delta ^ 10 * (n : Real) ^ 2 <= q ^ 2 := by
    dsimp [drcScore, K, q, b] at hscore ⊢
    nlinarith
  have ha_sq : (((2 : Real) ^ (-(1 : Real) / 2)) ^ (2 : Nat)) = 1 / 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
    norm_num [Real.rpow_neg_one]
  let d : Real := (2 : Real) ^ (-(1 : Real) / 2) * delta ^ 5 * n
  have hd : 0 <= d := by
    dsimp [d]
    positivity
  have hq : 0 <= q := by positivity
  have hd_sq : d ^ 2 <= q ^ 2 := by
    calc
      d ^ 2 = (1 : Real) / 2 * delta ^ 10 * (n : Real) ^ 2 := by
        dsimp [d]
        rw [mul_pow, mul_pow, ha_sq]
        ring
      _ <= (11 : Real) / 16 * delta ^ 10 * (n : Real) ^ 2 := by
        have hz : 0 <= delta ^ 10 * (n : Real) ^ 2 := by positivity
        nlinarith
      _ <= q ^ 2 := hq_sq
  have hsize : d <= q := (sq_le_sq₀ hd hq).mp hd_sq
  have hbad_le : 10 * b <= q ^ 2 := by
    dsimp [drcScore, K, q, b] at hscore ⊢
    nlinarith
  have hpartition := large_add_bad_eq_sq A K m delta
  refine ⟨K, ?_, ?_⟩
  · simpa [d, q] using hsize
  · dsimp [q, b] at hbad_le
    have hpartitionR :
        (largeIntersectionPairCount A K (delta ^ 2 * m / 2) : Real) +
          (drcBadPairCount A K m delta : Real) = (K.card : Real) ^ 2 :=
      hpartition
    nlinarith

private lemma intersection_sum_lower_of_card_lower {X : Type*} [DecidableEq X]
    {n m : Nat} (V : Finset X) (A : Fin n -> Finset X)
    (hV : V.card = m) (hA : forall i, A i ⊆ V)
    (delta : Real) (hdelta : 0 < delta) (hm : 0 < m)
    (hcard : forall i, delta * m <= (A i).card) :
    delta ^ 2 * m * (n : Real) ^ 2 <=
      ∑ i : Fin n, ∑ j : Fin n,
        (((A i ∩ A j).card : Nat) : Real) := by
  classical
  have hincidence :
      delta * (m : Real) * (n : Real) <=
        ∑ x ∈ V, (incidenceDegree A x : Real) := by
    calc
      delta * (m : Real) * (n : Real) =
          ∑ _i : Fin n, delta * (m : Real) := by simp; ring
      _ <= ∑ i : Fin n, ((A i).card : Real) := by
        apply Finset.sum_le_sum
        intro i _
        exact hcard i
      _ = ∑ x ∈ V, (incidenceDegree A x : Real) :=
        (sum_incidenceDegree V A hA).symm
  have hcauchy :
      (∑ x ∈ V, (incidenceDegree A x : Real)) ^ 2 <=
        (m : Real) * ∑ x ∈ V, (incidenceDegree A x : Real) ^ 2 := by
    simpa [hV] using (sq_sum_le_card_mul_sum_sq
      (s := V) (f := fun x => (incidenceDegree A x : Real)))
  have hraise := pow_le_pow_left₀ (by positivity :
      0 <= delta * (m : Real) * (n : Real)) hincidence 2
  have hcombined :
      (delta * (m : Real) * (n : Real)) ^ 2 <=
        (m : Real) *
          (∑ i : Fin n, ∑ j : Fin n,
            (((A i ∩ A j).card : Nat) : Real)) := by
    calc
      _ <= (∑ x ∈ V, (incidenceDegree A x : Real)) ^ 2 := hraise
      _ <= (m : Real) * ∑ x ∈ V,
          (incidenceDegree A x : Real) ^ 2 := hcauchy
      _ = _ := by rw [← sum_intersection_eq_sum_degree_sq V A hA]
  have hmul :
      (m : Real) * (delta ^ 2 * (m : Real) * (n : Real) ^ 2) <=
        (m : Real) *
          (∑ i : Fin n, ∑ j : Fin n,
            (((A i ∩ A j).card : Nat) : Real)) := by
    calc
      _ = (delta * (m : Real) * (n : Real)) ^ 2 := by ring
      _ <= _ := hcombined
  exact le_of_mul_le_mul_left hmul (by exact_mod_cast hm)

private lemma hasDenseIntersectionCore_zero {X : Type*} [DecidableEq X]
    {n : Nat} (A : Fin n -> Finset X) (delta : Real)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    HasDenseIntersectionCore 0 A delta := by
  classical
  refine ⟨Finset.univ, ?_, ?_⟩
  · have ha : (2 : Real) ^ (-(1 : Real) / 2) <= 1 :=
      le_of_lt (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
    have ha0 : 0 <= (2 : Real) ^ (-(1 : Real) / 2) := by positivity
    have hd5 : delta ^ 5 <= 1 := pow_le_one₀ (le_of_lt hdelta) hdelta_one
    have hd50 : 0 <= delta ^ 5 := by positivity
    have hcoeff : (2 : Real) ^ (-(1 : Real) / 2) * delta ^ 5 <= 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hd5)]
    simpa using mul_le_mul_of_nonneg_right hcoeff (by positivity : (0 : Real) <= n)
  · unfold largeIntersectionPairCount
    simp only [Nat.cast_zero, mul_zero, zero_div]
    change (9 : Real) / 10 *
      ((Finset.univ : Finset (Fin n)).card : Real) ^ 2 <=
      (((((Finset.univ : Finset (Fin n)) ×ˢ Finset.univ).filter
        fun ij : Fin n × Fin n =>
        (0 : Real) <= (((A ij.1 ∩ A ij.2).card : Nat) : Real)).card : Nat) : Real)
    rw [Finset.filter_eq_self.2 (fun _ _ => by positivity)]
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin,
      Nat.cast_mul, pow_two]
    have hn0 : 0 <= (n : Real) ^ 2 := sq_nonneg _
    nlinarith

/-- The dependent-random-choice argument of Gowers's Lemma 7.4. -/
theorem lemma_7_4_holds : lemma_7_4 := by
  unfold lemma_7_4
  intro X _ m n V A delta hV hA hdelta hdelta_one
  have hmain :
      (delta ^ 2 * m * (n : Real) ^ 2 <=
        ∑ i : Fin n, ∑ j : Fin n,
          (((A i ∩ A j).card : Nat) : Real)) ->
        HasDenseIntersectionCore m A delta := by
    intro hsum
    by_cases hm0 : m = 0
    · simpa [hm0] using
        (hasDenseIntersectionCore_zero A delta hdelta hdelta_one)
    · have hm : 0 < m := Nat.pos_of_ne_zero hm0
      obtain ⟨t, _ht, hscore⟩ :=
        exists_drc_sample V A hV hA delta hdelta hsum hm
      exact hasDenseIntersectionCore_of_score A delta hdelta t hscore
  refine ⟨hmain, ?_⟩
  intro hcard
  apply hmain
  by_cases hm0 : m = 0
  · have hs : 0 <= ∑ i : Fin n, ∑ j : Fin n,
        (((A i ∩ A j).card : Nat) : Real) := by positivity
    simpa [hm0] using hs
  · exact intersection_sum_lower_of_card_lower V A hV hA delta hdelta
      (Nat.pos_of_ne_zero hm0) hcard

end LeanProofs.GowersSzemeredi

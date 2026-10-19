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
  simp only [drcCore, Finset.natCast_card_filter, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : ∀ r, t r ∈ A i <;> by_cases hj : ∀ r, t r ∈ A j <;> simp [hi, hj, forall_and]

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
  have hinter (i j : Fin n) : (((A i ∩ A j).card : Nat) : Real) =
      ∑ x ∈ V, if x ∈ A i ∩ A j then (1 : Real) else 0 := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (Finset.inter_subset_left.trans (hA i))]
  simp_rw [hinter, incidenceDegree_sq]
  rw [eq_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

private lemma drcSamples_filter_inter {X : Type*} [DecidableEq X] {n : Nat}
    (V : Finset X) (A : Fin n -> Finset X) (hA : forall i, A i ⊆ V)
    (i j : Fin n) :
    (drcSamples V).filter (fun t => forall r, t r ∈ A i ∩ A j) =
      drcSamples (A i ∩ A j) := by
  ext t
  simp only [mem_filter, drcSamples, Fintype.mem_piFinset]
  constructor
  · exact fun h r => h.2 r
  · intro h
    refine ⟨?_, h⟩
    exact fun r => hA i (Finset.mem_inter.mp (h r)).1

/-- Summing a weight over pairs of the random core: the pair `(i, j)` lies in the core of exactly
`|A i ∩ A j| ^ 5` samples. -/
private lemma sum_drcCore_weighted {X : Type*} [DecidableEq X] {n : Nat}
    (V : Finset X) (A : Fin n -> Finset X) (hA : forall i, A i ⊆ V)
    (g : Fin n -> Fin n -> Real) :
    ∑ t ∈ drcSamples V, ∑ i ∈ drcCore A t, ∑ j ∈ drcCore A t, g i j =
      ∑ i : Fin n, ∑ j : Fin n, (((A i ∩ A j).card : Nat) : Real) ^ 5 * g i j := by
  have hcore (t : DRCIndex -> X) : ∑ i ∈ drcCore A t, ∑ j ∈ drcCore A t, g i j =
      ∑ i : Fin n, ∑ j : Fin n, if forall r, t r ∈ A i ∩ A j then g i j else 0 := by
    rw [drcCore, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : forall r, t r ∈ A i <;> simp [hi, Finset.sum_filter, forall_and]
  simp_rw [hcore]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_comm.trans
    (Finset.sum_congr rfl fun j _ => ?_)
  rw [← Finset.sum_filter, drcSamples_filter_inter V A hA i j, Finset.sum_const,
    drcSamples_card, nsmul_eq_mul, Nat.cast_pow]

private lemma sum_drcCore_card_sq {X : Type*} [DecidableEq X] {n : Nat}
    (V : Finset X) (A : Fin n -> Finset X) (hA : forall i, A i ⊆ V) :
    ∑ t ∈ drcSamples V, ((drcCore A t).card : Real) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n,
        (((A i ∩ A j).card : Nat) : Real) ^ 5 := by
  simpa [sq] using sum_drcCore_weighted V A hA fun _ _ => 1

private lemma drcBadPairCount_eq_sum {X : Type*} [DecidableEq X] {n : Nat}
    (A : Fin n -> Finset X) (K : Finset (Fin n)) (m : Nat)
    (delta : Real) :
    (drcBadPairCount A K m delta : Real) =
      ∑ i ∈ K, ∑ j ∈ K,
        if ((((A i ∩ A j).card : Nat) : Real) < delta ^ 2 * m / 2)
          then 1 else 0 := by
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
  simp_rw [drcBadPairCount_eq_sum, sum_drcCore_weighted V A hA, mul_boole]

private lemma intersection_fifth_moment_lower {X : Type*} [DecidableEq X]
    {n m : Nat} (A : Fin n -> Finset X) (delta : Real)
    (hsum : delta ^ 2 * m * (n : Real) ^ 2 <=
      ∑ i : Fin n, ∑ j : Fin n,
        (((A i ∩ A j).card : Nat) : Real)) :
    delta ^ 10 * (m : Real) ^ 5 * (n : Real) ^ 2 <=
      ∑ i : Fin n, ∑ j : Fin n,
        (((A i ∩ A j).card : Nat) : Real) ^ 5 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  -- the power-mean inequality over the `n ^ 2` ordered pairs
  have hpow := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin n × Fin n)))
    (f := fun ij => (((A ij.1 ∩ A ij.2).card : Nat) : Real)) (fun _ _ => Nat.cast_nonneg _) 4
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Fintype.sum_prod_type, Nat.reduceAdd] at hpow
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : Real) < ((n : Real) * n) ^ 4)
  calc ((n : Real) * n) ^ 4 * (delta ^ 10 * (m : Real) ^ 5 * (n : Real) ^ 2)
      = (delta ^ 2 * m * (n : Real) ^ 2) ^ 5 := by ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hsum 5
    _ ≤ _ := hpow

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
  -- a bad pair `(i, j)` lies in the core of at most `(delta ^ 2 * m / 2) ^ 5` samples
  have hbad : ∑ t ∈ drcSamples V, (drcBadPairCount A (drcCore A t) m delta : Real) ≤
      ∑ _i : Fin n, ∑ _j : Fin n, (delta ^ 2 * (m : Real) / 2) ^ 5 := by
    rw [sum_drcBadPairCount V A hA m delta]
    gcongr with i _ j _
    split_ifs with h
    · exact pow_le_pow_left₀ (by positivity) h.le 5
    · positivity
  refine Finset.exists_le_of_sum_le
    (Finset.card_pos.mp (by rw [drcSamples_card, hV]; exact pow_pos hm 5)) ?_
  simp only [drcScore, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    drcSamples_card, hV, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    at hbad ⊢
  linarith [intersection_fifth_moment_lower A delta hsum, sum_drcCore_card_sq V A hA]

private lemma hasDenseIntersectionCore_of_score {X : Type*} [DecidableEq X]
    {n m : Nat} (A : Fin n -> Finset X) (delta : Real)
    (hdelta : 0 < delta) (t : DRCIndex -> X)
    (hscore : (11 : Real) / 16 * delta ^ 10 * (n : Real) ^ 2 <=
      drcScore A t m delta) :
    HasDenseIntersectionCore m A delta := by
  set K := drcCore A t
  have hscore' : (11 : Real) / 16 * delta ^ 10 * (n : Real) ^ 2 ≤
      (K.card : Real) ^ 2 - 10 * drcBadPairCount A K m delta := hscore
  have hX : (0 : Real) ≤ delta ^ 10 * (n : Real) ^ 2 := by positivity
  have hb : (0 : Real) ≤ drcBadPairCount A K m delta := Nat.cast_nonneg _
  -- the large and the bad pairs partition `K ×ˢ K`
  have hpart : (largeIntersectionPairCount A K (delta ^ 2 * m / 2) : Real) +
      drcBadPairCount A K m delta = (K.card : Real) ^ 2 := by
    have h := Finset.card_filter_add_card_filter_not (s := K ×ˢ K)
      fun ij => delta ^ 2 * (m : Real) / 2 ≤ (((A ij.1 ∩ A ij.2).card : Nat) : Real)
    simpa [largeIntersectionPairCount, drcBadPairCount, not_le, sq] using
      congrArg (Nat.cast (R := Real)) h
  have ha : ((2 : Real) ^ (-(1 : Real) / 2)) ^ 2 = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num [Real.rpow_neg_one]
  refine ⟨K, (sq_le_sq₀ (by positivity) (by positivity)).mp ?_, by linarith⟩
  rw [mul_pow, mul_pow, ha]
  linarith

private lemma intersection_sum_lower_of_card_lower {X : Type*} [DecidableEq X]
    {n m : Nat} (V : Finset X) (A : Fin n -> Finset X)
    (hV : V.card = m) (hA : forall i, A i ⊆ V)
    (delta : Real) (hdelta : 0 < delta) (hm : 0 < m)
    (hcard : forall i, delta * m <= (A i).card) :
    delta ^ 2 * m * (n : Real) ^ 2 <=
      ∑ i : Fin n, ∑ j : Fin n,
        (((A i ∩ A j).card : Nat) : Real) := by
  -- the incidence degrees sum to at least `n * (delta * m)`; apply Cauchy-Schwarz over `V`
  have h1 : (n : Real) * (delta * m) ≤ ∑ x ∈ V, (incidenceDegree A x : Real) := by
    rw [sum_incidenceDegree V A hA]
    simpa using Finset.card_nsmul_le_sum Finset.univ _ _ fun i _ => hcard i
  have h2 : (∑ x ∈ V, (incidenceDegree A x : Real)) ^ 2 ≤
      m * ∑ i : Fin n, ∑ j : Fin n, (((A i ∩ A j).card : Nat) : Real) := by
    rw [sum_intersection_eq_sum_degree_sq V A hA, ← hV]
    exact sq_sum_le_card_mul_sum_sq
  refine le_of_mul_le_mul_left ?_ (by exact_mod_cast hm : (0 : Real) < m)
  calc (m : Real) * (delta ^ 2 * m * (n : Real) ^ 2) = ((n : Real) * (delta * m)) ^ 2 := by
        ring
    _ ≤ (∑ x ∈ V, (incidenceDegree A x : Real)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    _ ≤ _ := h2

private lemma hasDenseIntersectionCore_zero {X : Type*} [DecidableEq X]
    {n : Nat} (A : Fin n -> Finset X) (delta : Real)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    HasDenseIntersectionCore 0 A delta := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · have ha : (2 : Real) ^ (-(1 : Real) / 2) <= 1 :=
      le_of_lt (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
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
    nlinarith

/-- The dependent-random-choice argument of Gowers's Lemma 7.4. -/
theorem lemma_7_4_holds : lemma_7_4 := by
  intro X _ m n V A delta hV hA hdelta hdelta_one
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h := hasDenseIntersectionCore_zero A delta hdelta hdelta_one
    exact ⟨fun _ => h, fun _ => h⟩
  have hmain := fun hsum => (exists_drc_sample V A hV hA delta hdelta hsum hm).elim
    fun t ht => hasDenseIntersectionCore_of_score A delta hdelta t ht.2
  exact ⟨hmain, fun hcard =>
    hmain (intersection_sum_lower_of_card_lower V A hV hA delta hdelta hm hcard)⟩

end LeanProofs.GowersSzemeredi

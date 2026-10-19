import GowersSzemeredi.Definitions

/-!
# Shared proof infrastructure for the Gowers catalogue

This module contains elementary facts about the concrete encodings used by the
statement catalogue.  They are deliberately independent of the numbered paper
results, so later companion proofs can use them without circularity.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] theorem countWhere_true {X : Type*} [Fintype X] :
    countWhere (fun _ : X => True) = Fintype.card X := by
  simp [countWhere]

@[simp] theorem countWhere_false {X : Type*} [Fintype X] :
    countWhere (fun _ : X => False) = 0 := by
  simp [countWhere]

theorem countWhere_congr {X : Type*} [Fintype X] {p q : X → Prop}
    (h : ∀ x, p x ↔ q x) : countWhere p = countWhere q := by
  simp only [countWhere]
  congr 1
  ext x
  simp [h x]

theorem countWhere_mono {X : Type*} [Fintype X] {p q : X → Prop}
    (h : ∀ x, p x → q x) : countWhere p ≤ countWhere q := by
  classical
  simp only [countWhere]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨Finset.mem_univ x, h x hx.2⟩

theorem countWhere_le_card {X : Type*} [Fintype X] (p : X → Prop) :
    countWhere p ≤ Fintype.card X := by
  classical
  simpa [countWhere] using
    Finset.card_le_card (Finset.filter_subset (s := Finset.univ) p)

theorem IsPartition.cell_subset {X : Type*} [DecidableEq X] {m : Nat}
    {P : Fin m → Finset X} {S : Finset X} (hP : IsPartition P S) (i : Fin m) :
    P i ⊆ S := by
  intro x hx
  exact (hP.1 x).2 ⟨i, hx⟩

/-- Refining every cell of a partition by a partition gives a partition
indexed by the sigma type. -/
theorem IsPartition.sigma {X : Type*} [DecidableEq X]
    {M : Nat} (L : Fin M -> Nat) (A : Fin M -> Finset X) (S : Finset X)
    (B : (i : Fin M) -> Fin (L i) -> Finset X)
    (hA : IsPartition A S) (hB : forall i, IsPartition (B i) (A i)) :
    (forall x, x ∈ S <->
      exists z : Sigma fun i : Fin M => Fin (L i), x ∈ B z.1 z.2) /\
      forall z w : Sigma fun i : Fin M => Fin (L i), z != w ->
        Disjoint (B z.1 z.2) (B w.1 w.2) := by
  refine ⟨fun x => (hA.1 x).trans ⟨fun ⟨i, hi⟩ => ?_, fun ⟨⟨i, j⟩, hij⟩ =>
    ⟨i, ((hB i).1 x).2 ⟨j, hij⟩⟩⟩, fun ⟨i, j⟩ ⟨i', j'⟩ hzw => ?_⟩
  · obtain ⟨j, hj⟩ := ((hB i).1 x).1 hi
    exact ⟨⟨i, j⟩, hj⟩
  · by_cases hi : i = i'
    · subst hi
      exact (hB i).2 j j' (by simpa using hzw)
    · exact Disjoint.mono ((hB i).cell_subset j) ((hB i').cell_subset j')
        (hA.2 i i' (bne_iff_ne.mpr hi))

/-- The cells of a finite partition account for the cardinality of the set
exactly once. -/
theorem IsPartition.sum_card {X : Type*} [DecidableEq X] {m : Nat}
    {P : Fin m → Finset X} {S : Finset X} (hP : IsPartition P S) :
    ∑ i, (P i).card = S.card := by
  have hdisj :
      ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ hij
    exact hP.2 i j (bne_iff_ne.mpr hij)
  have hunion : Finset.univ.biUnion P = S := by
    ext x
    simp only [mem_biUnion, mem_univ, true_and]
    exact (hP.1 x).symm
  rw [← hunion, Finset.card_biUnion hdisj]

@[simp] theorem sum_indicator {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    ∑ x : ZMod N, indicator A x = (A.card : Complex) := by
  simp [indicator]

@[simp] theorem sum_balanced {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    ∑ x : ZMod N, balanced A x = 0 := by
  simp only [balanced, sum_sub_distrib, sum_indicator, sum_const, card_univ,
    ZMod.card, nsmul_eq_mul, density]
  apply sub_eq_zero.mpr
  norm_cast
  exact (mul_div_cancel₀ (A.card : Real)
    (by exact_mod_cast NeZero.ne N : (N : Real) ≠ 0)).symm

theorem density_nonneg {N : Nat} (A : Finset (ZMod N)) : 0 ≤ density A :=
    div_nonneg (by positivity) (by positivity)

theorem density_le_one {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    density A ≤ 1 := by
  rw [density, div_le_one (by exact_mod_cast NeZero.pos N : (0 : Real) < N)]
  have hcard : A.card ≤ N := by
    simpa only [ZMod.card] using A.card_le_univ
  exact_mod_cast hcard

/-- The one-point progression `{x}`. -/
def singletonNatAP (x : Nat) : NatAP where
  start := x
  step := 1
  length := 1

@[simp] lemma singletonNatAP_carrier (x : Nat) :
    (singletonNatAP x).carrier = {x} := by
  ext y
  simp [singletonNatAP, NatAP.carrier]

lemma singletonNatAP_isProper (x : Nat) : (singletonNatAP x).IsProper := by
  constructor
  · simp [singletonNatAP]
  · rw [singletonNatAP_carrier]
    simp [singletonNatAP]

/-- The one-point progressions partition `[0, r)`. -/
lemma singletonNatAP_partition (r : Nat) :
    IsNatAPPartition (fun i : Fin r => singletonNatAP i) (Finset.range r) := by
  constructor
  · intro x
    simp only [Finset.mem_range, singletonNatAP_carrier, Finset.mem_singleton]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  · intro i j hij
    change Disjoint (singletonNatAP (i : Nat)).carrier
      (singletonNatAP (j : Nat)).carrier
    rw [singletonNatAP_carrier, singletonNatAP_carrier]
    exact Finset.disjoint_singleton.mpr fun h =>
      bne_iff_ne.mp hij (Fin.ext h)

end LeanProofs.GowersSzemeredi

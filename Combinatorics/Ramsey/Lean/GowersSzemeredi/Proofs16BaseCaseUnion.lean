import GowersSzemeredi.Proofs16BaseCaseAssembly
import GowersSzemeredi.ProofInfrastructure

/-!
# Proper finite-union closure for the repaired Lemma 16.3

This module adapts the finite-union refinement from Lemma 16.8 to
`ProperMultiplyLinear`.  Properness is carried as an invariant of every
refinement cell, and the singleton probes used in the quantitative argument
are genuine length-one boxes.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

private lemma isMultilinear_const {N k : Nat} (c : ZMod N) :
    IsMultilinear (fun _ : Point N k => c) := by
  classical
  let e0 : Fin k -> Bool := fun _ => false
  refine ⟨fun e => if e = e0 then c else 0, ?_⟩
  intro x
  rw [Finset.sum_eq_single e0]
  · simp [e0]
  · intro e _he hne
    simp [hne]
  · simp

private lemma singleton_box_partition {N k : Nat} [NeZero N]
    (P : Box N k) : IsBoxPartition (fun _ : Fin 1 => P) P := by
  constructor
  · intro x
    simp
  · intro i j hij
    exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
private def properPointSingletonBox {N d : Nat} (x : Point N d) : Box N d where
  axis := fun i => { start := x i, step := 1, length := 1 }
  commonDiff := 1
  axis_step := by intro i; rfl

@[simp] private lemma properPointSingletonBox_carrier {N d : Nat} [NeZero N]
    (x : Point N d) : (properPointSingletonBox x).carrier = {x} := by
  classical
  ext y
  simp only [Box.carrier, properPointSingletonBox, Finset.mem_filter,
    Finset.mem_univ, true_and, ModAP.carrier, Finset.mem_image,
    Finset.mem_singleton]
  constructor
  · intro h
    apply funext
    intro i
    let j := Classical.choose (h i)
    have hj := Classical.choose_spec (h i)
    have hj0 : (j : Nat) = 0 := by omega
    simpa [j, hj0] using hj.symm
  · rintro rfl i
    exact ⟨⟨0, by simp⟩, by simp⟩

private lemma properPointSingletonBox_isProper {N d : Nat} [NeZero N]
    (x : Point N d) : (properPointSingletonBox x).IsProper := by
  intro i
  rw [ModAP.IsProper]
  simp [properPointSingletonBox, ModAP.carrier]

private def IndexedPartition {X ι : Type*} [DecidableEq X] [Fintype ι]
    (A : ι → Finset X) (S : Finset X) : Prop :=
  (forall x, x ∈ S ↔ exists i, x ∈ A i) ∧
    forall i j, i ≠ j → Disjoint (A i) (A j)

private lemma indexedPartition_cell_subset {X ι : Type*} [DecidableEq X]
    [Fintype ι] {A : ι → Finset X} {S : Finset X}
    (hA : IndexedPartition A S) (i : ι) : A i ⊆ S := by
  intro x hx
  exact (hA.1 x).2 ⟨i, hx⟩

private lemma indexedPartition_sum_card {X ι : Type*} [DecidableEq X]
    [Fintype ι] {A : ι → Finset X} {S : Finset X}
    (hA : IndexedPartition A S) : ∑ i, (A i).card = S.card := by
  classical
  have hpair : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint A := by
    intro i _ j _ hij
    exact hA.2 i j hij
  have hunion : Finset.univ.biUnion A = S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact (hA.1 x).symm
  rw [← hunion, Finset.card_biUnion hpair]

private lemma indexedPartition_of_isPartition {X : Type*} [DecidableEq X]
    {m : Nat} {A : Fin m → Finset X} {S : Finset X}
    (hA : IsPartition A S) : IndexedPartition A S := by
  exact ⟨hA.1, fun i j hij => hA.2 i j (bne_iff_ne.mpr hij)⟩

private lemma isPartition_of_indexed {X : Type*} [DecidableEq X]
    {m : Nat} {A : Fin m → Finset X} {S : Finset X}
    (hA : IndexedPartition A S) : IsPartition A S := by
  exact ⟨hA.1, fun i j hij => hA.2 i j (bne_iff_ne.mp hij)⟩

private lemma partition_reindex {X ι κ : Type*} [DecidableEq X]
    [Fintype ι] [Fintype κ] (e : κ ≃ ι) (A : ι → Finset X)
    (S : Finset X) (hA : IndexedPartition A S) :
    IndexedPartition (fun j => A (e j)) S := by
  constructor
  · intro x
    rw [hA.1]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, by simpa⟩
    · rintro ⟨j, hj⟩
      exact ⟨e j, hj⟩
  · intro i j hij
    exact hA.2 (e i) (e j) (fun h => hij (e.injective h))

private lemma sigma_partition {X ι : Type*} [DecidableEq X] [Fintype ι]
    (m : ι → Nat) (A : ι → Finset X) (S : Finset X)
    (B : (i : ι) → Fin (m i) → Finset X)
    (hA : IndexedPartition A S) (hB : ∀ i, IsPartition (B i) (A i)) :
    IndexedPartition (fun z : Sigma fun i => Fin (m i) => B z.1 z.2) S := by
  constructor
  · intro x
    rw [hA.1]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨j, hj⟩ := (hB i).1 x |>.mp hi
      exact ⟨⟨i, j⟩, hj⟩
    · rintro ⟨⟨i, j⟩, hij⟩
      exact ⟨i, (hB i).1 x |>.mpr ⟨j, hij⟩⟩
  · intro z w hzw
    by_cases hi : z.1 = w.1
    · rcases z with ⟨i, j⟩
      rcases w with ⟨i', j'⟩
      dsimp only at hi ⊢
      subst i'
      have hj : j ≠ j' := by
        intro h
        subst j'
        exact hzw rfl
      exact (hB i).2 j j' (bne_iff_ne.mpr hj)
    · exact Disjoint.mono (IsPartition.cell_subset (hB z.1) z.2)
        (IsPartition.cell_subset (hB w.1) w.2)
        (hA.2 z.1 w.1 hi)

private lemma biUnion_card_lower {X ι : Type*} [DecidableEq X] [Fintype ι]
    (A H : ι → Finset X) (S : Finset X) (eta : Real)
    (hA : IndexedPartition A S) (hH : ∀ i, H i ⊆ A i)
    (hcard : ∀ i, (1 - eta) * (A i).card ≤ (H i).card) :
    (1 - eta) * (S.card : Real) ≤
      ((Finset.univ.biUnion H).card : Real) := by
  classical
  have hpair : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint H := by
    intro i _ j _ hij
    exact Disjoint.mono (hH i) (hH j)
      (hA.2 i j hij)
  have hsumA : ∑ i, (A i).card = S.card := indexedPartition_sum_card hA
  have hsumH : (Finset.univ.biUnion H).card = ∑ i, (H i).card := by
    exact Finset.card_biUnion hpair
  calc
    (1 - eta) * (S.card : Real) =
        ∑ i, (1 - eta) * ((A i).card : Real) := by
      rw [← Finset.mul_sum]
      congr 1
      exact_mod_cast hsumA.symm
    _ ≤ ∑ i, ((H i).card : Real) := by
      exact Finset.sum_le_sum fun i _ => hcard i
    _ = ((Finset.univ.biUnion H).card : Real) := by
      rw [hsumH, Nat.cast_sum]

private lemma inter_card_lower {X : Type*} [DecidableEq X]
    (S H K : Finset X) (a b : Real) (hH : H ⊆ S) (hK : K ⊆ S)
    (hHcard : (1 - a) * (S.card : Real) ≤ H.card)
    (hKcard : (1 - b) * (S.card : Real) ≤ K.card) :
    (1 - (a + b)) * (S.card : Real) ≤ ((H ∩ K).card : Real) := by
  have hunion : H ∪ K ⊆ S := Finset.union_subset hH hK
  have hunionCard : ((H ∪ K).card : Real) ≤ S.card := by
    exact_mod_cast Finset.card_le_card hunion
  have hEq : ((H ∩ K).card : Real) + ((H ∪ K).card : Real) =
      (H.card : Real) + (K.card : Real) := by
    exact_mod_cast Finset.card_inter_add_card_union H K
  nlinarith

private lemma mem_local_of_mem_cell_and_biUnion {X : Type*} [DecidableEq X]
    {m : Nat} (A H : Fin m → Finset X) (S : Finset X)
    (hA : IsPartition A S) (hH : ∀ i, H i ⊆ A i)
    {j : Fin m} {x : X} (hxA : x ∈ A j)
    (hxH : x ∈ Finset.univ.biUnion H) : x ∈ H j := by
  classical
  rw [Finset.mem_biUnion] at hxH
  obtain ⟨i, _hi, hxi⟩ := hxH
  by_contra hxj
  have hij : i ≠ j := by
    intro h
    subst i
    exact hxj hxi
  have hdis := hA.2 i j (bne_iff_ne.mpr hij)
  exact Finset.disjoint_left.mp hdis (hH i hxi) hxA

private structure ProperUnionRefinement {N d r : Nat} [NeZero N]
    (Gamma : Fin r → Finset (Point N d × ZMod N)) (P : Box N d)
    (eta c s : Real) (q0 t : Nat) (htr : t ≤ r) where
  M : Nat
  Q : Fin M → Box N d
  H : Finset (Point N d)
  mu : Fin M → Fin t → Fin q0 → Point N d → ZMod N
  H_subset : H ⊆ P.carrier
  H_card : (1 - (t : Real) * eta) * (P.carrier.card : Real) ≤ H.card
  partition : IsBoxPartition Q P
  proper : ∀ j, (Q j).IsProper
  width : ∀ j, (P.width : Real) ^ (c ^ ((t : Real) * s)) ≤ (Q j).width
  multilinear : ∀ j i a, IsMultilinear (mu j i a)
  cover : ∀ j x, x ∈ (Q j).carrier → x ∈ H →
    ∀ i : Fin t, ∀ y, (x, y) ∈ Gamma (Fin.castLE htr i) →
      ∃ a, y = mu j i a x

private def initialProperUnionRefinement {N d r : Nat} [NeZero N]
    (Gamma : Fin r → Finset (Point N d × ZMod N)) (P : Box N d)
    (hP : P.IsProper) (eta c s : Real) (q0 : Nat) :
    ProperUnionRefinement Gamma P eta c s q0 0 (Nat.zero_le r) where
  M := 1
  Q := fun _ => P
  H := P.carrier
  mu := fun _ i => Fin.elim0 i
  H_subset := Finset.Subset.rfl
  H_card := by simp
  partition := singleton_box_partition P
  proper := fun _ => hP
  width := by
    intro j
    simp
  multilinear := by
    intro j i
    exact Fin.elim0 i
  cover := by
    intro j x hxQ hxH i
    exact Fin.elim0 i

private noncomputable def extendProperUnionRefinement {N d r t q0 : Nat} [NeZero N]
    (Gamma : Fin r → Finset (Point N d × ZMod N)) (P : Box N d)
    (gamma eta s : Real) (htr : t ≤ r) (hlt : t < r)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hs : 0 < s)
    (D : ProperUnionRefinement Gamma P eta
      (multipleC (s⁻¹ * eta) gamma d) s q0 t htr)
    (hnext : ProperMultiplyLinear gamma s (Gamma ⟨t, hlt⟩))
    (hq0 : ∀ q : Nat,
      (q : Real) ≤ (multipleQ (s⁻¹ * eta) gamma d) ^ s → q ≤ q0) :
    ProperUnionRefinement Gamma P eta (multipleC (s⁻¹ * eta) gamma d) s
      q0 (t + 1) (by omega) := by
  classical
  choose m q H R nu hHsub hHcard hpart hproper hq hwidth hmulti hcover using
    fun j : Fin D.M => hnext eta heta hetaOne (D.Q j) (D.proper j)
  have hqNat : ∀ j, q j ≤ q0 := fun j => hq0 (q j) (hq j)
  let I := Sigma fun j : Fin D.M => Fin (m j)
  let e := Fintype.equivFin I
  let Q' : Fin (Fintype.card I) → Box N d := fun a =>
    let z := e.symm a
    R z.1 z.2
  let K : Finset (Point N d) := Finset.univ.biUnion H
  let H' := D.H ∩ K
  let mu' : Fin (Fintype.card I) → Fin (t + 1) → Fin q0 →
      Point N d → ZMod N := fun a i b =>
    let z := e.symm a
    if hi : (i : Nat) < t then
      D.mu z.1 ⟨i, hi⟩ b
    else if hb : (b : Nat) < q z.1 then
      nu z.1 z.2 ⟨b, hb⟩
    else 0
  refine ⟨Fintype.card I, Q', H', mu', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Finset.inter_subset_left.trans D.H_subset)
  · have hKsub : K ⊆ P.carrier := by
      intro x hx
      change x ∈ Finset.univ.biUnion H at hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨j, _hj, hxj⟩ := hx
      exact D.partition.cell_subset j (hHsub j hxj)
    have hKcard : (1 - eta) * (P.carrier.card : Real) ≤ K.card := by
      exact biUnion_card_lower (fun j => (D.Q j).carrier) H P.carrier eta
        (indexedPartition_of_isPartition D.partition) hHsub hHcard
    have hinter := inter_card_lower P.carrier D.H K ((t : Real) * eta) eta
      D.H_subset hKsub D.H_card hKcard
    dsimp only [H']
    convert hinter using 1
    all_goals push_cast
    all_goals ring
  · dsimp only [Q']
    exact isPartition_of_indexed <| partition_reindex e.symm
      (fun z : I => (R z.1 z.2).carrier) P.carrier
      (sigma_partition m (fun j => (D.Q j).carrier) P.carrier
        (fun j a => (R j a).carrier)
        (indexedPartition_of_isPartition D.partition) hpart)
  · intro a
    dsimp only [Q']
    exact hproper (e.symm a).1 (e.symm a).2
  · intro a
    let z := e.symm a
    have hOld := D.width z.1
    have hNew := hwidth z.1 z.2
    have hc : 0 ≤ multipleC (s⁻¹ * eta) gamma d := by
      unfold multipleC
      exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩).pow_nonneg _
    have ha : 0 ≤ multipleC (s⁻¹ * eta) gamma d ^ s :=
      Real.rpow_nonneg hc _
    have hbase : 0 ≤ (P.width : Real) ^
        (multipleC (s⁻¹ * eta) gamma d ^ ((t : Real) * s)) :=
      Real.rpow_nonneg (by exact_mod_cast Nat.zero_le P.width) _
    have hpow := Real.rpow_le_rpow hbase hOld ha
    dsimp only [Q', z]
    calc
      (P.width : Real) ^
          (multipleC (s⁻¹ * eta) gamma d ^ (((t + 1 : Nat) : Real) * s)) =
          ((P.width : Real) ^
            (multipleC (s⁻¹ * eta) gamma d ^ ((t : Real) * s))) ^
              (multipleC (s⁻¹ * eta) gamma d ^ s) := by
        rw [← Real.rpow_mul
          (by exact_mod_cast Nat.zero_le P.width : (0 : Real) ≤ P.width)]
        congr 2
        rw [← Real.rpow_add' hc (by positivity)]
        congr 1
        push_cast
        ring
      _ ≤ ((D.Q z.1).width : Real) ^
          (multipleC (s⁻¹ * eta) gamma d ^ s) := hpow
      _ ≤ (R z.1 z.2).width := hNew
  · intro a i b
    let z := e.symm a
    dsimp only [mu']
    split_ifs with hi hb
    · exact D.multilinear z.1 ⟨i, hi⟩ b
    · exact hmulti z.1 z.2 ⟨b, hb⟩
    · exact isMultilinear_const 0
  · intro a x hxQ hxH i y hxy
    let z := e.symm a
    have hxChild : x ∈ (R z.1 z.2).carrier := hxQ
    have hxParent : x ∈ (D.Q z.1).carrier :=
      hpart z.1 |>.cell_subset z.2 hxChild
    change x ∈ D.H ∩ K at hxH
    have hxH' : x ∈ D.H ∧ x ∈ K := by
      simpa only [Finset.mem_inter] using hxH
    have hxOldH : x ∈ D.H := hxH'.1
    by_cases hi : (i : Nat) < t
    · obtain ⟨b, hb⟩ := D.cover z.1 x hxParent hxOldH ⟨i, hi⟩ y (by
        have hii : Fin.castLE htr ⟨(i : Nat), hi⟩ =
            Fin.castLE (by omega : t + 1 ≤ r) i := by
          apply Fin.ext
          rfl
        rw [hii]
        exact hxy)
      exact ⟨b, by simpa [mu', z, hi] using hb⟩
    · have hit : (i : Nat) = t := by omega
      have hxK : x ∈ K := hxH'.2
      have hxLocal : x ∈ H z.1 :=
        mem_local_of_mem_cell_and_biUnion
          (fun j => (D.Q j).carrier) H P.carrier D.partition hHsub hxParent hxK
      obtain ⟨b, hb⟩ := hcover z.1 z.2 x hxChild hxLocal y (by
        have hii : Fin.castLE (by omega : t + 1 ≤ r) i = (⟨t, hlt⟩ : Fin r) := by
          apply Fin.ext
          exact hit
        simpa only [hii] using hxy)
      let b' : Fin q0 := Fin.castLE (hqNat z.1) b
      refine ⟨b', ?_⟩
      simpa [mu', z, hi, b', b.isLt] using hb

private noncomputable def iterateProperUnionRefinement {N d r t q0 : Nat} [NeZero N]
    (Gamma : Fin r → Finset (Point N d × ZMod N)) (P : Box N d)
    (hP : P.IsProper) (gamma eta s : Real) (heta : 0 < eta)
    (hetaOne : eta ≤ 1) (hs : 0 < s)
    (hGamma : ∀ i, ProperMultiplyLinear gamma s (Gamma i))
    (hq0 : ∀ q : Nat,
      (q : Real) ≤ (multipleQ (s⁻¹ * eta) gamma d) ^ s → q ≤ q0)
    (htr : t ≤ r) :
    ProperUnionRefinement Gamma P eta (multipleC (s⁻¹ * eta) gamma d) s
      q0 t htr := by
  induction t with
  | zero =>
      exact initialProperUnionRefinement Gamma P hP eta
        (multipleC (s⁻¹ * eta) gamma d) s q0
  | succ t ih =>
      exact extendProperUnionRefinement Gamma P gamma eta s (by omega) (by omega)
        heta hetaOne hs (ih (by omega)) (hGamma ⟨t, by omega⟩) hq0

private lemma abs_gamma_le_iteration_of_nonempty {N d : Nat} [NeZero N]
    {gamma s : Real} {Gamma : Finset (Point N d × ZMod N)}
    (hs : 0 < s) (hGamma : ProperMultiplyLinear gamma s Gamma)
    (hGammaNe : Gamma.Nonempty) : |gamma| ≤ s := by
  by_contra hnot
  have hsg : s < |gamma| := lt_of_not_ge hnot
  have hgammaAbs : 0 < |gamma| := hs.trans hsg
  let rho : Real := (1 + s / |gamma|) / 2
  have hrho : 0 < rho := by
    dsimp only [rho]
    positivity
  have hrhoOne : rho < 1 := by
    dsimp only [rho]
    have := (div_lt_one hgammaAbs).2 hsg
    linarith
  have hratio : 1 < |gamma * (s⁻¹ * rho)| := by
    rw [abs_mul, abs_mul, abs_inv, abs_of_pos hs, abs_of_pos hrho]
    dsimp only [rho]
    field_simp
    nlinarith
  let E : Nat := (2 : Nat) ^ ((2 : Nat) ^ (d + 8))
  have hEpos : 0 < E := by positivity
  have hEeven : Even E := Nat.even_pow.mpr ⟨even_two, by positivity⟩
  have hCgt : 1 < multipleC (s⁻¹ * rho) gamma d := by
    unfold multipleC
    change 1 < (gamma * (s⁻¹ * rho)) ^ E
    rw [← hEeven.pow_abs]
    exact one_lt_pow₀ hratio hEpos.ne'
  have hQnonneg : 0 ≤ multipleQ (s⁻¹ * rho) gamma d := by
    unfold multipleQ
    positivity
  have hQlt : multipleQ (s⁻¹ * rho) gamma d < 1 := by
    unfold multipleQ
    exact (inv_lt_one₀ (zero_lt_one.trans hCgt)).2 hCgt
  have hbound : (multipleQ (s⁻¹ * rho) gamma d) ^ s < 1 :=
    Real.rpow_lt_one hQnonneg hQlt hs
  obtain ⟨z, hz⟩ := hGammaNe
  obtain ⟨M, q, H, Q, mu, hHP, hHcard, hpartition, hQproper, hq,
      hwidth, hmultilinear, hcover⟩ := hGamma rho hrho hrhoOne.le
    (properPointSingletonBox z.1) (properPointSingletonBox_isProper z.1)
  have hPcard : (properPointSingletonBox z.1).carrier.card = 1 := by simp
  have hHpos : 0 < H.card := by
    have hreal : (0 : Real) < H.card := by
      rw [hPcard] at hHcard
      norm_num at hHcard
      linarith [hrhoOne]
    exact_mod_cast hreal
  obtain ⟨x, hxH⟩ := Finset.card_pos.mp hHpos
  have hxP := hHP hxH
  have hx : x = z.1 := by
    simpa only [properPointSingletonBox_carrier, Finset.mem_singleton] using hxP
  subst x
  obtain ⟨j, hxQ⟩ := (hpartition.1 z.1).mp (by simp)
  obtain ⟨i, hi⟩ := hcover j z.1 hxQ hxH z.2 hz
  have hqPos : 0 < q := by
    have := i.isLt
    omega
  have hqOne : (1 : Real) ≤ q := by exact_mod_cast hqPos
  nlinarith

private lemma gamma_ne_zero_of_nonempty {N d : Nat} [NeZero N]
    {gamma s : Real} {Gamma : Finset (Point N d × ZMod N)}
    (hs : 0 < s) (hGamma : ProperMultiplyLinear gamma s Gamma)
    (hGammaNe : Gamma.Nonempty) : gamma ≠ 0 := by
  intro hgamma
  subst gamma
  obtain ⟨z, hz⟩ := hGammaNe
  obtain ⟨M, q, H, Q, mu, hHP, hHcard, hpartition, hQproper, hq,
      hwidth, hmultilinear, hcover⟩ :=
    hGamma (1 / 2 : Real) (by norm_num) (by norm_num)
      (properPointSingletonBox z.1) (properPointSingletonBox_isProper z.1)
  have hPcard : (properPointSingletonBox z.1).carrier.card = 1 := by simp
  have hHpos : 0 < H.card := by
    have hreal : (0 : Real) < H.card := by
      rw [hPcard] at hHcard
      norm_num at hHcard
      linarith
    exact_mod_cast hreal
  obtain ⟨x, hxH⟩ := Finset.card_pos.mp hHpos
  have hxP := hHP hxH
  have hx : x = z.1 := by
    simpa only [properPointSingletonBox_carrier, Finset.mem_singleton] using hxP
  subst x
  obtain ⟨j, hxQ⟩ := (hpartition.1 z.1).mp (by simp)
  obtain ⟨i, hi⟩ := hcover j z.1 hxQ hxH z.2 hz
  have hqPos : 0 < q := by have := i.isLt; omega
  have hqOne : (1 : Real) ≤ q := by exact_mod_cast hqPos
  simp [multipleQ, multipleC, hs.ne'] at hq
  linarith

private lemma final_graph_count_bounds {d r q0 : Nat}
    {theta gamma s : Real} (hr : 0 < r) (htheta : 0 < theta)
    (hthetaOne : theta < 1) (hs : 1 ≤ s) (hgammaPos : 0 < |gamma|)
    (hgamma : |gamma| ≤ s)
    (hq0 : (q0 : Real) ≤
      (multipleQ (s⁻¹ * (theta / (r : Real))) gamma d) ^ s) :
    ((r * q0 : Nat) : Real) ≤
        (multipleQ (((r : Real) * s)⁻¹ * theta) gamma d) ^
          ((r : Real) * s) ∧
      ((q0 ^ r : Nat) : Real) ≤
        (multipleQ (((r : Real) * s)⁻¹ * theta) gamma d) ^
          ((r : Real) * s) := by
  have hsPos : 0 < s := zero_lt_one.trans_le hs
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  have harg : s⁻¹ * (theta / (r : Real)) =
      ((r : Real) * s)⁻¹ * theta := by
    field_simp
  rw [← harg]
  let E : Nat := (2 : Nat) ^ ((2 : Nat) ^ (d + 8))
  have hEpos : 0 < E := by positivity
  have hEtwo : 2 ≤ E := by
    dsimp only [E]
    exact Nat.le_pow (by positivity)
  have hEeven : Even E := Nat.even_pow.mpr ⟨even_two, by positivity⟩
  let u : Real := |gamma * (s⁻¹ * (theta / (r : Real)))|
  have huPos : 0 < u := by
    dsimp only [u]
    rw [abs_pos]
    exact mul_ne_zero (abs_pos.mp hgammaPos)
      (mul_ne_zero (inv_ne_zero hsPos.ne')
        (div_ne_zero htheta.ne' (by exact_mod_cast hr.ne')))
  have huBound : u ≤ (r : Real)⁻¹ := by
    dsimp only [u]
    rw [abs_mul, abs_mul, abs_inv, abs_div, abs_of_pos hsPos,
      abs_of_pos htheta, abs_of_pos hrReal]
    have hmul := mul_le_mul_of_nonneg_right hgamma (by positivity : 0 ≤ s⁻¹)
    have hsCancel : |gamma| * s⁻¹ ≤ 1 := by
      calc
        |gamma| * s⁻¹ ≤ s * s⁻¹ := hmul
        _ = 1 := by field_simp
    calc
      |gamma| * (s⁻¹ * (theta / (r : Real))) =
          (|gamma| * s⁻¹) * theta * (r : Real)⁻¹ := by ring
      _ ≤ 1 * 1 * (r : Real)⁻¹ := by gcongr
      _ = (r : Real)⁻¹ := by ring
  have hRinvNonneg : (0 : Real) ≤ (r : Real)⁻¹ := by positivity
  have hRinvOne : (r : Real)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ hrReal).2
    exact_mod_cast hr
  have hCbound : multipleC (s⁻¹ * (theta / (r : Real))) gamma d ≤
      ((r : Real)⁻¹) ^ 2 := by
    unfold multipleC
    change (gamma * (s⁻¹ * (theta / (r : Real)))) ^ E ≤ _
    rw [← hEeven.pow_abs]
    calc
      u ^ E ≤ ((r : Real)⁻¹) ^ E :=
        pow_le_pow_left₀ huPos.le huBound E
      _ ≤ ((r : Real)⁻¹) ^ 2 :=
        pow_le_pow_of_le_one hRinvNonneg hRinvOne hEtwo
  have hCpos : 0 < multipleC (s⁻¹ * (theta / (r : Real))) gamma d := by
    unfold multipleC
    change 0 < (gamma * (s⁻¹ * (theta / (r : Real)))) ^ E
    rw [← hEeven.pow_abs]
    positivity
  have hQlower : (r : Real) ^ 2 ≤
      multipleQ (s⁻¹ * (theta / (r : Real))) gamma d := by
    unfold multipleQ
    rw [le_inv_comm₀ (sq_pos_of_pos hrReal) hCpos]
    simpa [inv_pow] using hCbound
  let Qc := multipleQ (s⁻¹ * (theta / (r : Real))) gamma d
  let b := Qc ^ s
  have hQone : 1 ≤ Qc := by
    dsimp only [Qc]
    have hrOne : (1 : Real) ≤ r := by exact_mod_cast hr
    nlinarith [sq_nonneg ((r : Real) - 1)]
  have hbQ : Qc ≤ b := by
    dsimp only [b]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hQone hs
  have hbR : (r : Real) ≤ b := by
    have hrOne : (1 : Real) ≤ r := by exact_mod_cast hr
    change (r : Real) ^ 2 ≤ Qc at hQlower
    exact le_trans (by nlinarith [sq_nonneg ((r : Real) - 1)])
      (hQlower.trans hbQ)
  have hbOne : 1 ≤ b := le_trans (by exact_mod_cast hr) hbR
  have hq0b : (q0 : Real) ≤ b := hq0
  have hbpow : (r : Real) * b ≤ b ^ r := by
    by_cases hrOne : r = 1
    · subst r
      simp
    · have hrTwo : 2 ≤ r := by omega
      calc
        (r : Real) * b ≤ b * b := by gcongr
        _ = b ^ 2 := by ring
        _ ≤ b ^ r := pow_le_pow_right₀ hbOne hrTwo
  have htarget : b ^ r = Qc ^ ((r : Real) * s) := by
    dsimp only [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ Qc)]
    congr 1
    ring
  constructor
  · push_cast
    calc
      (r : Real) * q0 ≤ (r : Real) * b := by gcongr
      _ ≤ b ^ r := hbpow
      _ = Qc ^ ((r : Real) * s) := htarget
  · rw [Nat.cast_pow]
    calc
      (q0 : Real) ^ r ≤ b ^ r := pow_le_pow_left₀ (by positivity) hq0b r
      _ = Qc ^ ((r : Real) * s) := htarget

private theorem properMultiplyLinear_finsetUnion {N d r : Nat} [NeZero N]
    (gamma s : Real) (hs : 1 ≤ s)
    (Gamma : Fin r → Finset (Point N d × ZMod N))
    (hr : 0 < r) (hGamma : ∀ i, ProperMultiplyLinear gamma s (Gamma i)) :
    ProperMultiplyLinear gamma ((r : Real) * s) (section16FinsetUnion Gamma) := by
  intro theta htheta hthetaOne P hP
  have hsPos : 0 < s := zero_lt_one.trans_le hs
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  let eta : Real := theta / (r : Real)
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hetaOne : eta ≤ 1 := by
    dsimp only [eta]
    apply (div_le_one hrReal).2
    exact hthetaOne.trans (by exact_mod_cast hr)
  have harg : s⁻¹ * eta = ((r : Real) * s)⁻¹ * theta := by
    dsimp only [eta]
    field_simp
  let stageQ := multipleQ (s⁻¹ * eta) gamma d
  let q0 := Nat.floor (stageQ ^ s)
  have hstageQnonneg : 0 ≤ stageQ := by
    dsimp only [stageQ, multipleQ]
    apply inv_nonneg.mpr
    unfold multipleC
    exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩).pow_nonneg _
  have hstageBoundNonneg : 0 ≤ stageQ ^ s :=
    Real.rpow_nonneg hstageQnonneg _
  have hq0Floor : (q0 : Real) ≤ stageQ ^ s := by
    exact Nat.floor_le hstageBoundNonneg
  let D := iterateProperUnionRefinement Gamma P hP gamma eta s heta hetaOne
    hsPos hGamma (fun q hq => Nat.le_floor hq) (q0 := q0) (t := r) le_rfl
  have hDcard : (1 - theta) * (P.carrier.card : Real) ≤ D.H.card := by
    have h := D.H_card
    have hetaCancel : (r : Real) * eta = theta := by
      dsimp only [eta]
      field_simp
    simpa only [hetaCancel] using h
  have hDwidth : ∀ j, (P.width : Real) ^
      ((multipleC (((r : Real) * s)⁻¹ * theta) gamma d) ^
        ((r : Real) * s)) ≤ (D.Q j).width := by
    intro j
    simpa only [harg] using D.width j
  have htargetBoundNonneg : 0 ≤
      (multipleQ (((r : Real) * s)⁻¹ * theta) gamma d) ^
        ((r : Real) * s) := by
    apply Real.rpow_nonneg
    unfold multipleQ
    apply inv_nonneg.mpr
    unfold multipleC
    exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩).pow_nonneg _
  by_cases hthetaStrict : theta < 1
  · by_cases hUnionNe : (section16FinsetUnion Gamma).Nonempty
    · obtain ⟨z, hz⟩ := hUnionNe
      rw [section16FinsetUnion, Finset.mem_biUnion] at hz
      obtain ⟨i, _hi, hzi⟩ := hz
      have hGiNe : (Gamma i).Nonempty := ⟨z, hzi⟩
      have hgammaPos : 0 < |gamma| := abs_pos.mpr
        (gamma_ne_zero_of_nonempty hsPos (hGamma i) hGiNe)
      have hgamma := abs_gamma_le_iteration_of_nonempty hsPos (hGamma i) hGiNe
      have hcounts := final_graph_count_bounds (d := d) hr htheta hthetaStrict hs
        hgammaPos hgamma (by simpa only [stageQ, eta] using hq0Floor)
      let mu : Fin D.M → Fin (r * q0) → Point N d → ZMod N :=
        fun j a =>
          let p := finProdFinEquiv.symm a
          D.mu j p.1 p.2
      refine ⟨D.M, r * q0, D.H, D.Q, mu, D.H_subset, hDcard,
        D.partition, D.proper, hcounts.1, hDwidth, ?_, ?_⟩
      · intro j a
        let p := finProdFinEquiv.symm a
        exact D.multilinear j p.1 p.2
      · intro j x hxQ hxH y hxy
        rw [section16FinsetUnion, Finset.mem_biUnion] at hxy
        obtain ⟨i, _hi, hxy⟩ := hxy
        obtain ⟨a, ha⟩ := D.cover j x hxQ hxH i y hxy
        refine ⟨finProdFinEquiv (i, a), ?_⟩
        change y = D.mu j
          (finProdFinEquiv.symm (finProdFinEquiv (i, a))).1
          (finProdFinEquiv.symm (finProdFinEquiv (i, a))).2 x
        rw [Equiv.symm_apply_apply]
        exact ha
    · refine ⟨D.M, 0, D.H, D.Q, (fun _ i => Fin.elim0 i),
        D.H_subset, hDcard, D.partition, D.proper,
        (by simpa using htargetBoundNonneg), hDwidth, ?_, ?_⟩
      · intro j i
        exact Fin.elim0 i
      · intro j x hxQ hxH y hxy
        exact (hUnionNe ⟨(x, y), hxy⟩).elim
  · refine ⟨D.M, 0, ∅, D.Q, (fun _ i => Fin.elim0 i),
      Finset.empty_subset _, ?_, D.partition, D.proper,
      (by simpa using htargetBoundNonneg), hDwidth, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      have hPnonneg : (0 : Real) ≤ P.carrier.card := by positivity
      nlinarith
    · intro j i
      exact Fin.elim0 i
    · intro j x hxQ hxH
      simp at hxH

/-- The repaired finite-union closure used by the one-dimensional base-case
assembly. -/
theorem properUnionClosure_holds : ProperUnionClosure := by
  intro N d r _ gamma s Gamma hr hs hGamma
  exact properMultiplyLinear_finsetUnion gamma s hs Gamma hr hGamma


end LeanProofs.GowersSzemeredi.BaseCase

import GowersSzemeredi.Sections17_18
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.GroupTheory.CosetCover
import Mathlib.Order.Interval.Set.Infinite

/-!
# Regions of real hyperplane arrangements

This module proves Gowers's Lemma 17.4.  The upper bound is the
Sauer--Shelah bound for the strict sign patterns realized by the arrangement.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

private def regionTrueSet {m : Nat} (p : Fin m -> Bool) : Finset (Fin m) :=
  Finset.univ.filter fun i => p i = true

@[simp] private lemma mem_regionTrueSet {m : Nat} (p : Fin m -> Bool) (i : Fin m) :
    i ∈ regionTrueSet p ↔ p i = true := by
  simp [regionTrueSet]

private lemma regionTrueSet_injective {m : Nat} :
    Function.Injective (regionTrueSet (m := m)) := by
  intro p q hpq
  funext i
  have hi := Finset.ext_iff.mp hpq i
  simp only [mem_regionTrueSet] at hi
  cases hpi : p i <;> cases hqi : q i <;> simp_all

private def regionFamily {k m : Nat} (H : Fin m -> AffineHyperplane k) :
    Finset (Finset (Fin m)) := by
  classical
  exact (Finset.univ.filter fun p => RealizesRegion H p).image regionTrueSet

private lemma hyperplaneRegionCount_eq_card_regionFamily {k m : Nat}
    (H : Fin m -> AffineHyperplane k) :
    hyperplaneRegionCount H = (regionFamily H).card := by
  classical
  unfold hyperplaneRegionCount countWhere regionFamily
  rw [Finset.filter_congr_decidable]
  exact (Finset.card_image_iff.mpr regionTrueSet_injective.injOn).symm

private lemma regionFamily_shattered_card_le {k m : Nat}
    (H : Fin m -> AffineHyperplane k) (s : Finset (Fin m))
    (hs : (regionFamily H).Shatters s) : s.card <= k := by
  classical
  by_contra hsk
  have hdep : ¬ LinearIndependent Real (fun i : s => (H i.1).normal) := fun hli => by
    have := hli.fintype_card_le_finrank
    rw [Module.finrank_fin_fun, Fintype.card_coe] at this
    exact hsk this
  obtain ⟨c0, hc0, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hdep
  -- a dependency `c` of the normals with `∑ c i * offset i ≤ 0` and `c i0 ≠ 0`: `c0` or `-c0`
  suffices key : ∀ c : s -> Real, ∑ i : s, c i • (H i.1).normal = 0 →
      ∑ i : s, c i * (H i.1).offset <= 0 → c i0 ≠ 0 → False by
    rcases le_total (∑ i : s, c0 i * (H i.1).offset) 0 with hoff | hoff
    · exact key c0 hc0 hoff hi0
    · refine key (-c0) ?_ ?_ (neg_ne_zero.mpr hi0)
      · simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hc0, neg_zero]
      · simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_nonpos] using hoff
  intro c hcNormal hcOffset hi0ne
  -- the region realizing the sign pattern `{i ∈ s | 0 < c i}` on `s`
  let t : Finset (Fin m) := (s.attach.filter fun i => 0 < c i).image Subtype.val
  have hts : t ⊆ s := by
    intro i hi
    simp only [t, Finset.mem_image, Finset.mem_filter, Finset.mem_attach] at hi
    obtain ⟨j, ⟨_, _⟩, rfl⟩ := hi
    exact j.2
  obtain ⟨u, hu, hsu⟩ := hs hts
  rw [regionFamily, Finset.mem_image] at hu
  obtain ⟨p, hp, rfl⟩ := hu
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hp).2
  have hmem (i : s) : p i.1 = true ↔ 0 < c i := by
    rw [← mem_regionTrueSet]
    calc
      i.1 ∈ regionTrueSet p ↔ i.1 ∈ s ∩ regionTrueSet p := by simp [i.2]
      _ ↔ i.1 ∈ t := by rw [hsu]
      _ ↔ 0 < c i := by simp [t]
  -- so every term of `∑ c i * (⟨normal i, x⟩ - offset i)` is `≤ 0`, the term at `i0` `< 0`
  have hstrict (i : s) (hci : c i ≠ 0) :
      c i * (realDot (H i.1).normal x - (H i.1).offset) < 0 := by
    cases hpi : p i.1
    · have hc : ¬ 0 < c i := fun h => by simp [(hmem i).mpr h] at hpi
      exact mul_neg_of_neg_of_pos (lt_of_le_of_ne (not_lt.mp hc) hci)
        (sub_pos.mpr ((hx i.1).2.mp hpi))
    · exact mul_neg_of_pos_of_neg ((hmem i).mp hpi) (sub_neg.mpr ((hx i.1).1.mp hpi))
  have hsumNeg : (∑ i : s, c i * (realDot (H i.1).normal x - (H i.1).offset)) < 0 := by
    simpa only [Finset.sum_const_zero] using
      Finset.sum_lt_sum (s := Finset.univ)
        (fun i _ => (eq_or_ne (c i) 0).elim (fun h => by simp [h]) fun h => (hstrict i h).le)
        ⟨i0, Finset.mem_univ _, hstrict i0 hi0ne⟩
  -- but the sum is `-∑ c i * offset i ≥ 0`, as `∑ c i • normal i = 0`
  have hdotZero : ∑ i : s, c i * realDot (H i.1).normal x = 0 := by
    have hcj (j : Fin k) : ∑ i : s, c i * (H i.1).normal j = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
        congrFun hcNormal j
    simp only [realDot, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun j _ => by rw [← Finset.sum_mul, hcj, zero_mul]
  refine not_le_of_gt hsumNeg ?_
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hdotZero, zero_sub]
  exact neg_nonneg.mpr hcOffset

private lemma hyperplaneRegionCount_le {k m : Nat}
    (H : Fin m -> AffineHyperplane k) :
    hyperplaneRegionCount H <=
      ∑ j ∈ Finset.range (k + 1), Nat.choose m j := by
  let A := regionFamily H
  have hvc : A.vcDim <= k := by
    unfold Finset.vcDim
    apply Finset.sup_le
    intro s hs
    exact regionFamily_shattered_card_le H s (Finset.mem_shatterer.mp hs)
  have hIic : Finset.Iic A.vcDim ⊆ Finset.Iic k := by gcongr
  have hIicRange : Finset.Iic k = Finset.range (k + 1) := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  rw [hyperplaneRegionCount_eq_card_regionFamily]
  calc
    A.card <= A.shatterer.card := Finset.card_le_card_shatterer A
    _ <= ∑ j ∈ Finset.Iic A.vcDim, (Fintype.card (Fin m)).choose j :=
      Finset.card_shatterer_le_sum_vcDim
    _ <= ∑ j ∈ Finset.Iic k, (Fintype.card (Fin m)).choose j :=
      Finset.sum_le_sum_of_subset hIic
    _ = ∑ j ∈ Finset.range (k + 1), Nat.choose m j := by
      rw [hIicRange]
      simp only [Fintype.card_fin]

private def dotLinear {k : Nat} (a : Fin k → Real) :
    (Fin k → Real) →ₗ[Real] Real where
  toFun := realDot a
  map_add' := by
    intro x y
    simp only [realDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp only [realDot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc
      (∑ i, a i * (c * x i)) = ∑ i, c * (a i * x i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = c * ∑ i, a i * x i := (Finset.mul_sum _ _ _).symm

private lemma dotLinear_apply {k : Nat} (a x : Fin k → Real) :
    dotLinear a x = realDot a x := rfl

private lemma realDot_add_smul {k : Nat} (a x v : Fin k → Real) (t : Real) :
    realDot a (x + t • v) = realDot a x + t * realDot a v := by
  simp only [realDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma exists_dot_values {k : Nat} {I : Type*} [Fintype I]
    (v : I → Fin k → Real) (hli : LinearIndependent Real v) (b : I → Real) :
    ∃ x : Fin k → Real, ∀ i, realDot (v i) x = b i := by
  let coeff : (I →₀ Real) →ₗ[Real] Real :=
    Finsupp.lsum Real (fun i => b i • LinearMap.id)
  let f0 : Submodule.span Real (Set.range v) →ₗ[Real] Real :=
    coeff.comp hli.repr
  obtain ⟨f, hf⟩ := LinearMap.exists_extend f0
  let x : Fin k → Real := fun j => f (Pi.basisFun Real (Fin k) j)
  refine ⟨x, fun i => ?_⟩
  have hcoord : realDot (v i) x = f (v i) := by
    dsimp only [realDot, x]
    calc
      (∑ j, v i j * f (Pi.basisFun Real (Fin k) j)) =
          ∑ j, f (v i j • Pi.basisFun Real (Fin k) j) := by simp
      _ = f (∑ j, v i j • Pi.basisFun Real (Fin k) j) := by rw [map_sum]
      _ = f (v i) := by
        congr 1
        simpa [Pi.basisFun_repr] using
          (Pi.basisFun Real (Fin k)).sum_repr (v i)
  rw [hcoord]
  have hvi : v i ∈ Submodule.span Real (Set.range v) :=
    Submodule.subset_span (Set.mem_range_self i)
  have hcomp := LinearMap.congr_fun hf ⟨v i, hvi⟩
  rw [LinearMap.comp_apply] at hcomp
  rw [show f (v i) = f0 ⟨v i, hvi⟩ by simpa using hcomp]
  dsimp only [f0, coeff]
  rw [LinearMap.comp_apply, hli.repr_eq_single i ⟨v i, hvi⟩ rfl]
  simp

private lemma exists_avoiding_kernels
    {V : Type*} [AddCommGroup V] [Module Real V]
    {I : Type*} [DecidableEq I] (S : Finset I) (f : I → V →ₗ[Real] Real)
    (hf : ∀ i, i ∈ S → f i ≠ 0) :
    ∃ v : V, ∀ i, i ∈ S → f i v ≠ 0 := by
  let K : Finset (Subspace Real V) := S.image fun i => LinearMap.ker (f i)
  have htop : (⊤ : Subspace Real V) ∉ K := by
    intro hmem
    simp only [K, Finset.mem_image] at hmem
    obtain ⟨i, hiS, hi⟩ := hmem
    have hk : LinearMap.ker (f i) ≠ ⊤ := by
      exact fun hker => hf i hiS (LinearMap.ker_eq_top.mp hker)
    exact hk hi
  have hne := Subspace.biUnion_ne_univ_of_top_notMem htop
  have hex : ∃ v, v ∉ ⋃ p ∈ K, (p : Set V) := by
    by_contra hn
    push Not at hn
    exact hne (Set.eq_univ_of_forall hn)
  obtain ⟨v, hv⟩ := hex
  refine ⟨v, fun i hiS hzero => ?_⟩
  apply hv
  apply Set.mem_iUnion_of_mem (LinearMap.ker (f i))
  apply Set.mem_iUnion_of_mem (show LinearMap.ker (f i) ∈ K by
    exact Finset.mem_image.mpr ⟨i, hiS, rfl⟩)
  exact hzero

private lemma exists_intersectionPoint_avoids {k m : Nat}
    (H : Fin m → AffineHyperplane k) (hgp : HyperplanesInGeneralPosition H)
    (s : Finset (Fin m)) (hsk : s.card ≤ k) :
    ∃ x : Fin k → Real,
      (∀ i, i ∈ s → realDot (H i).normal x = (H i).offset) ∧
      (∀ i, i ∉ s → realDot (H i).normal x ≠ (H i).offset) := by
  obtain ⟨a, ha⟩ := exists_dot_values
    (fun i : s => (H i.1).normal) (hgp.1 s hsk) (fun i => (H i.1).offset)
  by_cases hcard : s.card = k
  · -- `k` hyperplanes meet in one point, which no further hyperplane contains
    refine ⟨a, fun i hi => ha ⟨i, hi⟩, fun i hi hisect => hgp.2 (insert i s)
      (by rw [Finset.card_insert_of_notMem hi, hcard]; omega) ⟨a, fun j hjI => ?_⟩⟩
    rcases Finset.mem_insert.mp hjI with rfl | hj
    · exact hisect
    · exact ha ⟨j, hj⟩
  · -- move `a` inside the intersection `K` of the kernels, off the other hyperplanes
    have hcardlt : s.card < k := lt_of_le_of_ne hsk hcard
    let K : Subspace Real (Fin k → Real) :=
      ⨅ i : s, LinearMap.ker (dotLinear (H i.1).normal)
    let outside : Finset (Fin m) := Finset.univ \ s
    let f : Fin m → K →ₗ[Real] Real := fun i =>
      (dotLinear (H i).normal).domRestrict K
    have hfne : ∀ i, i ∈ outside → f i ≠ 0 := by
      intro i hiout hfzero
      have hinot : i ∉ s := (Finset.mem_sdiff.mp hiout).2
      obtain ⟨d, hd⟩ := exists_dot_values (fun j : (insert i s : Finset (Fin m)) => (H j.1).normal)
        (hgp.1 _ (by rw [Finset.card_insert_of_notMem hinot]; omega))
        (fun j => if j.1 = i then 1 else 0)
      have hdK : d ∈ K := by
        simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, dotLinear_apply]
        intro j
        have hji : j.1 ≠ i := fun h => hinot (h ▸ j.2)
        simpa [hji] using hd ⟨j.1, Finset.mem_insert_of_mem j.2⟩
      have hdone : realDot (H i).normal d = 1 := by
        simpa using hd ⟨i, Finset.mem_insert_self i s⟩
      simpa [f, dotLinear_apply, hdone] using LinearMap.congr_fun hfzero ⟨d, hdK⟩
    obtain ⟨v, hv⟩ := exists_avoiding_kernels outside f hfne
    let forbidden : Finset Real := outside.image fun i =>
      ((H i).offset - realDot (H i).normal a) / realDot (H i).normal v.1
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset forbidden
    let x : Fin k → Real := a + t • v.1
    refine ⟨x, fun i hi => ?_, fun i hi hxi => ?_⟩
    · have hvK := v.2
      simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, dotLinear_apply] at hvK
      rw [show x = a + t • v.1 by rfl, realDot_add_smul, ha ⟨i, hi⟩, hvK ⟨i, hi⟩]
      ring
    · have hiout : i ∈ outside := by simp [outside, hi]
      have hfv : realDot (H i).normal v.1 ≠ 0 := by simpa [f, dotLinear_apply] using hv i hiout
      have hxformula : realDot (H i).normal x =
          realDot (H i).normal a + t * realDot (H i).normal v.1 := realDot_add_smul _ _ _ _
      refine ht (Finset.mem_image.mpr ⟨i, hiout, ?_⟩)
      rw [div_eq_iff hfv]
      linarith

private def StronglyShatters {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (A : Finset (Finset alpha)) (s : Finset alpha) : Prop :=
  ∃ u : Finset alpha, Disjoint u s ∧ ∀ t : Finset alpha, t ⊆ s → u ∪ t ∈ A

private lemma stronglyShatters_regionFamily_of_card_le {k m : Nat}
    (H : Fin m → AffineHyperplane k) (hgp : HyperplanesInGeneralPosition H)
    (s : Finset (Fin m)) (hsk : s.card ≤ k) :
    StronglyShatters (regionFamily H) s := by
  classical
  obtain ⟨x0, hx0S, hx0Outside⟩ := exists_intersectionPoint_avoids H hgp s hsk
  let outside : Finset (Fin m) := Finset.univ \ s
  let u : Finset (Fin m) := outside.filter fun i =>
    realDot (H i).normal x0 < (H i).offset
  have hus : Disjoint u s := Finset.disjoint_left.mpr fun i hiu his =>
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hiu).1).2 his
  refine ⟨u, hus, fun t hts => ?_⟩
  let target : s → Real := fun i => if i.1 ∈ t then -1 else 1
  obtain ⟨w, hw⟩ := exists_dot_values
    (fun i : s => (H i.1).normal) (hgp.1 s hsk) target
  -- `x0 + eps • w` puts the hyperplanes through `x0` on the sides `t` asks for, and leaves the
  -- other hyperplanes' sides as at `x0`
  let gap : Fin m → Real := fun i =>
    realDot (H i).normal x0 - (H i).offset
  let total : Real := ∑ i ∈ outside,
    |realDot (H i).normal w| / |gap i|
  let eps : Real := 1 / (1 + total)
  have hgapne : ∀ i, i ∈ outside → gap i ≠ 0 := fun i hiout =>
    sub_ne_zero.mpr (hx0Outside i (Finset.mem_sdiff.mp hiout).2)
  have htotalNonneg : 0 ≤ total := by positivity
  have hepsPos : 0 < eps := by positivity
  have hepsTotal : eps * total < 1 := by
    rw [show eps = (1 + total)⁻¹ from one_div _, inv_mul_lt_iff₀ (by positivity)]
    linarith
  have hperturb : ∀ i, i ∈ outside →
      |eps * realDot (H i).normal w| < |gap i| := by
    intro i hiout
    have hratioLe : |realDot (H i).normal w| / |gap i| ≤ total :=
      Finset.single_le_sum (s := outside) (f := fun j => |realDot (H j).normal w| / |gap j|)
        (fun j _ => by positivity) hiout
    rw [abs_mul, abs_of_pos hepsPos, ← div_lt_one (abs_pos.mpr (hgapne i hiout)), mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left hratioLe hepsPos.le).trans_lt hepsTotal
  let x : Fin k → Real := x0 + eps • w
  have hside (i : Fin m) :
      if i ∈ u ∪ t then realDot (H i).normal x < (H i).offset
      else (H i).offset < realDot (H i).normal x := by
    have hxFormula : realDot (H i).normal x =
        realDot (H i).normal x0 + eps * realDot (H i).normal w :=
      realDot_add_smul _ _ _ _
    by_cases his : i ∈ s
    · have hiNotU : i ∉ u := fun hiu => Finset.disjoint_left.mp hus hiu his
      simp only [Finset.mem_union, hiNotU, false_or]
      rw [hxFormula, hx0S i his, hw ⟨i, his⟩]
      by_cases hit : i ∈ t <;> simp [target, hit] <;> linarith
    · have hiout : i ∈ outside := by simp [outside, his]
      have hiNotT : i ∉ t := fun hit => his (hts hit)
      have hiu : i ∈ u ↔ gap i < 0 := by simp [u, hiout, gap]
      have herr := abs_lt.mp (hperturb i hiout)
      simp only [Finset.mem_union, hiNotT, or_false, hiu]
      rcases lt_or_gt_of_ne (hgapne i hiout) with hneg | hpos
      · rw [if_pos hneg]
        rw [abs_of_neg hneg] at herr
        dsimp only [gap] at herr
        linarith [herr.2]
      · rw [if_neg (not_lt_of_ge hpos.le)]
        rw [abs_of_pos hpos] at herr
        dsimp only [gap] at herr
        linarith [herr.1]
  let p : Fin m → Bool := fun i => decide (i ∈ u ∪ t)
  have hpReal : RealizesRegion H p := by
    refine ⟨x, fun i => ?_⟩
    have h := hside i
    by_cases hi : i ∈ u ∪ t
    · rw [if_pos hi] at h
      simp only [p, hi, decide_true]; simp [h, not_lt_of_ge h.le]
    · rw [if_neg hi] at h
      simp only [p, hi, decide_false]; simp [h, not_lt_of_ge h.le]
  rw [regionFamily, Finset.mem_image]
  refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpReal⟩, ?_⟩
  ext i
  simp [regionTrueSet, p]

private lemma not_stronglyShatters_iff_compl_shatters
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (A : Finset (Finset alpha)) (s : Finset alpha) :
    ¬ StronglyShatters A s ↔ Aᶜ.Shatters sᶜ := by
  constructor
  · intro hstrong t hts
    rw [StronglyShatters] at hstrong
    push Not at hstrong
    have hnt : ∀ x ∈ s, x ∉ t := fun x hxs hxt => Finset.mem_compl.mp (hts hxt) hxs
    obtain ⟨u, hus', humiss⟩ :=
      hstrong t (Finset.disjoint_left.mpr fun x hxt hxs => hnt x hxs hxt)
    refine ⟨t ∪ u, by simpa only [Finset.mem_compl] using humiss, ?_⟩
    ext x
    simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_union]
    by_cases hxs : x ∈ s
    · simp [hxs, hnt x hxs]
    · have hnu : x ∉ u := fun hxu => hxs (hus' hxu)
      simp [hxs, hnu]
  · rintro hshat ⟨u, hus', hcube⟩
    have hucomp : u ⊆ sᶜ := fun x hxu =>
      Finset.mem_compl.mpr fun hxs => Finset.disjoint_left.mp hus' hxu hxs
    obtain ⟨c, hccompl, hcinter⟩ := hshat hucomp
    have huc : u ∪ s ∩ c = c := by
      ext x
      have hi := Finset.ext_iff.mp hcinter x
      simp only [Finset.mem_inter, Finset.mem_compl] at hi
      by_cases hxs : x ∈ s
      · have hnu : x ∉ u := fun hxu => Finset.disjoint_left.mp hus' hxu hxs
        simp [hxs, hnu]
      · simpa [hxs] using hi.symm
    have hmem := hcube (s ∩ c) Finset.inter_subset_left
    rw [huc] at hmem
    exact Finset.mem_compl.mp hccompl hmem

private def strongShatterer {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (A : Finset (Finset alpha)) : Finset (Finset alpha) := by
  classical
  exact Finset.univ.filter (StronglyShatters A)

private def nonStrongFamily {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (A : Finset (Finset alpha)) : Finset (Finset alpha) := by
  classical
  exact Finset.univ.filter (fun s => ¬ StronglyShatters A s)

private lemma card_nonStrongFamily_eq_card_compl_shatterer
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (A : Finset (Finset alpha)) :
    (nonStrongFamily A).card = Aᶜ.shatterer.card := by
  rw [show nonStrongFamily A = Aᶜ.shatterer.image (fun s => sᶜ) by
    ext s
    simp only [nonStrongFamily, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hs
      refine ⟨sᶜ, ?_, ?_⟩
      · rw [Finset.mem_shatterer]
        rw [← not_stronglyShatters_iff_compl_shatters]
        simpa using hs
      · simp
    · rintro ⟨t, ht, rfl⟩
      rw [not_stronglyShatters_iff_compl_shatters]
      rw [Finset.mem_shatterer] at ht
      simpa using ht]
  rw [Finset.card_image_iff.mpr]
  intro s _ t _ hst
  simpa using congrArg (fun u : Finset alpha => uᶜ) hst

private lemma card_strongShatterer_le
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (A : Finset (Finset alpha)) : (strongShatterer A).card ≤ A.card := by
  have hpartition : (strongShatterer A).card + (nonStrongFamily A).card =
      Fintype.card (Finset alpha) := by
    rw [show nonStrongFamily A = (strongShatterer A)ᶜ by
      ext s
      simp [nonStrongFamily, strongShatterer]]
    exact Finset.card_add_card_compl (strongShatterer A)
  have hcompPartition : A.card + Aᶜ.card = Fintype.card (Finset alpha) :=
    Finset.card_add_card_compl A
  have hPajor : Aᶜ.card ≤ Aᶜ.shatterer.card :=
    Finset.card_le_card_shatterer Aᶜ
  rw [← card_nonStrongFamily_eq_card_compl_shatterer] at hPajor
  omega

private def smallSubsets (m k : Nat) : Finset (Finset (Fin m)) :=
  (Finset.range (k + 1)).biUnion fun j =>
    (Finset.univ : Finset (Fin m)).powersetCard j

private lemma card_smallSubsets (m k : Nat) :
    (smallSubsets m k).card =
      ∑ j ∈ Finset.range (k + 1), Nat.choose m j := by
  unfold smallSubsets
  rw [Finset.card_biUnion
    ((Finset.univ : Finset (Fin m)).pairwise_disjoint_powersetCard.set_pairwise _)]
  apply Finset.sum_congr rfl
  intro j _
  simp

private lemma smallSubsets_subset_strongShatterer {k m : Nat}
    (H : Fin m → AffineHyperplane k) (hgp : HyperplanesInGeneralPosition H) :
    smallSubsets m k ⊆ strongShatterer (regionFamily H) := by
  intro s hs
  rw [smallSubsets, Finset.mem_biUnion] at hs
  obtain ⟨j, hj, hsPower⟩ := hs
  have hscard : s.card ≤ k := by
    have hcard := (Finset.mem_powersetCard.mp hsPower).2
    have hjlt := Finset.mem_range.mp hj
    rw [hcard]
    omega
  simp only [strongShatterer, Finset.mem_filter, Finset.mem_univ, true_and]
  exact stronglyShatters_regionFamily_of_card_le H hgp s hscard

private lemma hyperplaneRegionCount_ge_of_generalPosition {k m : Nat}
    (H : Fin m → AffineHyperplane k) (hgp : HyperplanesInGeneralPosition H) :
    ∑ j ∈ Finset.range (k + 1), Nat.choose m j ≤
      hyperplaneRegionCount H := by
  rw [← card_smallSubsets m k]
  calc
    (smallSubsets m k).card ≤ (strongShatterer (regionFamily H)).card :=
      Finset.card_le_card (smallSubsets_subset_strongShatterer H hgp)
    _ ≤ (regionFamily H).card := card_strongShatterer_le (regionFamily H)
    _ = hyperplaneRegionCount H :=
      (hyperplaneRegionCount_eq_card_regionFamily H).symm

/-- **Gowers, Lemma 17.4.** The number of regions cut out by m
real affine hyperplanes in R^k is at most the binomial sum, and
general-position arrangements attain the bound. -/
theorem lemma_17_4_holds : lemma_17_4 := by
  intro k m H
  refine ⟨hyperplaneRegionCount_le H, fun hgp => ?_⟩
  exact Nat.le_antisymm (hyperplaneRegionCount_le H)
    (hyperplaneRegionCount_ge_of_generalPosition H hgp)

end LeanProofs.GowersSzemeredi

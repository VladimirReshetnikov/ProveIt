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
  have hklt : k < Fintype.card s := by
    simpa only [Fintype.card_coe] using Nat.lt_of_not_ge hsk
  have hdep :
      ¬ LinearIndependent Real (fun i : s => (H i.1).normal) := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Module.finrank_fin_fun] at this
    exact (Nat.not_le_of_lt hklt) this
  obtain ⟨c0, hc0, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let offsetSum : Real := ∑ i : s, c0 i * (H i.1).offset
  let c : s -> Real := if offsetSum <= 0 then c0 else -c0
  have hcNormal : ∑ i : s, c i • (H i.1).normal = 0 := by
    by_cases hoff : offsetSum <= 0
    · simpa [c, hoff] using hc0
    · have hcneg : c = -c0 := by simp [c, hoff]
      rw [hcneg]
      simp_rw [Pi.neg_apply, neg_smul]
      rw [Finset.sum_neg_distrib, hc0, neg_zero]
  have hcOffset : ∑ i : s, c i * (H i.1).offset <= 0 := by
    by_cases hoff : offsetSum <= 0
    · have hcEq : c = c0 := by simp [c, hoff]
      rw [hcEq]
      simpa only [offsetSum] using hoff
    · have hcEq : c = -c0 := by simp [c, hoff]
      rw [hcEq]
      simp_rw [Pi.neg_apply, neg_mul]
      rw [Finset.sum_neg_distrib]
      exact neg_nonpos.mpr (le_of_not_ge hoff)
  have hi0ne : c i0 ≠ 0 := by
    by_cases hoff : offsetSum <= 0
    · simpa [c, hoff] using hi0
    · simpa [c, hoff] using neg_ne_zero.mpr hi0
  let t : Finset (Fin m) := (s.attach.filter fun i => 0 < c i).image Subtype.val
  have hts : t ⊆ s := by
    intro i hi
    simp only [t, Finset.mem_image, Finset.mem_filter, Finset.mem_attach] at hi
    obtain ⟨j, ⟨_, _⟩, rfl⟩ := hi
    exact j.2
  obtain ⟨u, hu, hsu⟩ := hs hts
  rw [regionFamily, Finset.mem_image] at hu
  obtain ⟨p, hp, rfl⟩ := hu
  have hpReal : RealizesRegion H p := (Finset.mem_filter.mp hp).2
  obtain ⟨x, hx⟩ := hpReal
  have hmem (i : s) : i.1 ∈ regionTrueSet p ↔ 0 < c i := by
    have his : i.1 ∈ s := i.2
    calc
      i.1 ∈ regionTrueSet p ↔ i.1 ∈ s ∩ regionTrueSet p := by simp [his]
      _ ↔ i.1 ∈ t := by rw [hsu]
      _ ↔ 0 < c i := by simp [t]
  have hstrict (i : s) (hci : c i ≠ 0) :
      c i * (realDot (H i.1).normal x - (H i.1).offset) < 0 := by
    rcases lt_or_gt_of_ne hci with hcneg | hcpos
    · have hpnot : p i.1 ≠ true := by
        intro htrue
        have himem : i.1 ∈ regionTrueSet p := by simpa using htrue
        exact (not_lt_of_ge hcneg.le) ((hmem i).mp himem)
      have hpfalse : p i.1 = false := Bool.eq_false_of_not_eq_true hpnot
      have hside : (H i.1).offset < realDot (H i.1).normal x :=
        (hx i.1).2.mp hpfalse
      exact mul_neg_of_neg_of_pos hcneg (sub_pos.mpr hside)
    · have himem : i.1 ∈ regionTrueSet p := (hmem i).mpr hcpos
      have hptrue : p i.1 = true := (mem_regionTrueSet p i.1).mp himem
      have hside : realDot (H i.1).normal x < (H i.1).offset :=
        (hx i.1).1.mp hptrue
      exact mul_neg_of_pos_of_neg hcpos (sub_neg.mpr hside)
  have hterm (i : s) :
      c i * (realDot (H i.1).normal x - (H i.1).offset) <= 0 := by
    by_cases hci : c i = 0
    · simp [hci]
    · exact (hstrict i hci).le
  have hsumNeg :
      (∑ i : s, c i *
        (realDot (H i.1).normal x - (H i.1).offset)) < 0 := by
    simpa only [Finset.sum_const_zero] using
      Finset.sum_lt_sum (s := Finset.univ) (fun i _ => hterm i)
        ⟨i0, Finset.mem_univ _, hstrict i0 hi0ne⟩
  have hdotZero : ∑ i : s, c i * realDot (H i.1).normal x = 0 := by
    unfold realDot
    calc
      (∑ i : s, c i * ∑ j, (H i.1).normal j * x j) =
          ∑ j, (∑ i : s, c i * (H i.1).normal j) * x j := by
        simp_rw [Finset.mul_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        have hcj (j : Fin k) : ∑ i : s, c i * (H i.1).normal j = 0 := by
          have := congrFun hcNormal j
          simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            Pi.zero_apply] using this
        apply Finset.sum_eq_zero
        intro j _
        rw [hcj j, zero_mul]
  have hsumNonneg :
      0 <= ∑ i : s, c i *
        (realDot (H i.1).normal x - (H i.1).offset) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hdotZero, zero_sub]
    exact neg_nonneg.mpr hcOffset
  exact (not_le_of_gt hsumNeg) hsumNonneg

private lemma regionFamily_vcDim_le {k m : Nat}
    (H : Fin m -> AffineHyperplane k) : (regionFamily H).vcDim <= k := by
  unfold Finset.vcDim
  apply Finset.sup_le
  intro s hs
  exact regionFamily_shattered_card_le H s (Finset.mem_shatterer.mp hs)

private lemma hyperplaneRegionCount_le {k m : Nat}
    (H : Fin m -> AffineHyperplane k) :
    hyperplaneRegionCount H <=
      ∑ j ∈ Finset.range (k + 1), Nat.choose m j := by
  classical
  let A := regionFamily H
  have hvc : A.vcDim <= k := regionFamily_vcDim_le H
  have hIic : Finset.Iic A.vcDim ⊆ Finset.Iic k := by
    intro j hj
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hj).trans hvc)
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
  simp only [realDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  apply congrArg₂ (.+.) rfl
  apply Finset.sum_congr rfl
  intro i _
  ring

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
  rw [LinearMap.comp_apply]
  rw [hli.repr_eq_single i ⟨v i, hvi⟩ rfl]
  simp

private lemma exists_avoiding_kernels
    {V : Type*} [AddCommGroup V] [Module Real V]
    {I : Type*} [DecidableEq I] (S : Finset I) (f : I → V →ₗ[Real] Real)
    (hf : ∀ i, i ∈ S → f i ≠ 0) :
    ∃ v : V, ∀ i, i ∈ S → f i v ≠ 0 := by
  classical
  let K : Finset (Subspace Real V) := S.image fun i => LinearMap.ker (f i)
  have htop : (⊤ : Subspace Real V) ∉ K := by
    intro hmem
    simp only [K, Finset.mem_image] at hmem
    obtain ⟨i, hiS, hi⟩ := hmem
    have hk : LinearMap.ker (f i) ≠ ⊤ := by
      intro hker
      exact hf i hiS (LinearMap.ker_eq_top.mp hker)
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
  classical
  have hliS := hgp.1 s hsk
  obtain ⟨a, ha⟩ := exists_dot_values
    (fun i : s => (H i.1).normal) hliS (fun i => (H i.1).offset)
  by_cases hcard : s.card = k
  · refine ⟨a, ?_, ?_⟩
    · intro i hi
      exact ha ⟨i, hi⟩
    · intro i hi hisect
      let I : Finset (Fin m) := insert i s
      have hIcard : k < I.card := by
        simp only [I, Finset.card_insert_of_notMem hi, hcard]
        omega
      apply hgp.2 I hIcard
      refine ⟨a, fun j hjI => ?_⟩
      simp only [I, Finset.mem_insert] at hjI
      rcases hjI with rfl | hj
      · exact hisect
      · exact ha ⟨j, hj⟩
  · have hcardlt : s.card < k := lt_of_le_of_ne hsk hcard
    let K : Subspace Real (Fin k → Real) :=
      ⨅ i : s, LinearMap.ker (dotLinear (H i.1).normal)
    let outside : Finset (Fin m) := Finset.univ \ s
    let f : Fin m → K →ₗ[Real] Real := fun i =>
      (dotLinear (H i).normal).domRestrict K
    have hfne : ∀ i, i ∈ outside → f i ≠ 0 := by
      intro i hiout
      have hinot : i ∉ s := (Finset.mem_sdiff.mp hiout).2
      let I : Finset (Fin m) := insert i s
      have hIcard : I.card ≤ k := by
        simp only [I, Finset.card_insert_of_notMem hinot]
        omega
      have hliI := hgp.1 I hIcard
      let b : I → Real := fun j => if j.1 = i then 1 else 0
      obtain ⟨d, hd⟩ := exists_dot_values
        (fun j : I => (H j.1).normal) hliI b
      have hdK : d ∈ K := by
        simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, dotLinear_apply]
        intro j
        have hji : j.1 ≠ i := fun h => hinot (h ▸ j.2)
        have hjI : j.1 ∈ I := by simp [I, j.2]
        simpa [b, hji] using hd ⟨j.1, hjI⟩
      intro hfzero
      have hdi := LinearMap.congr_fun hfzero ⟨d, hdK⟩
      have hiI : i ∈ I := by simp [I]
      have hdone : realDot (H i).normal d = 1 := by
        simpa [b] using hd ⟨i, hiI⟩
      simp [f, dotLinear_apply, hdone] at hdi
    obtain ⟨v, hv⟩ := exists_avoiding_kernels outside f hfne
    let forbidden : Finset Real := outside.image fun i =>
      ((H i).offset - realDot (H i).normal a) / realDot (H i).normal v.1
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset forbidden
    let x : Fin k → Real := a + t • v.1
    refine ⟨x, ?_, ?_⟩
    · intro i hi
      have hvK := v.2
      simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, dotLinear_apply] at hvK
      have hvi : realDot (H i).normal v.1 = 0 := hvK ⟨i, hi⟩
      rw [show x = a + t • v.1 by rfl, realDot_add_smul, ha ⟨i, hi⟩, hvi]
      ring
    · intro i hi hxi
      have hiout : i ∈ outside := by simp [outside, hi]
      have hfv : realDot (H i).normal v.1 ≠ 0 := by
        simpa [f, dotLinear_apply] using hv i hiout
      apply ht
      apply Finset.mem_image.mpr
      refine ⟨i, hiout, ?_⟩
      symm
      apply (eq_div_iff hfv).2
      have hxformula : realDot (H i).normal x =
          realDot (H i).normal a + t * realDot (H i).normal v.1 := by
        exact realDot_add_smul _ _ _ _
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
  have hus : Disjoint u s := by
    rw [Finset.disjoint_left]
    intro i hiu his
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hiu).1).2 his
  refine ⟨u, hus, fun t hts => ?_⟩
  have hliS := hgp.1 s hsk
  let target : s → Real := fun i => if i.1 ∈ t then -1 else 1
  obtain ⟨w, hw⟩ := exists_dot_values
    (fun i : s => (H i.1).normal) hliS target
  let gap : Fin m → Real := fun i =>
    realDot (H i).normal x0 - (H i).offset
  let total : Real := ∑ i ∈ outside,
    |realDot (H i).normal w| / |gap i|
  let eps : Real := 1 / (1 + total)
  have hgapne : ∀ i, i ∈ outside → gap i ≠ 0 := by
    intro i hiout
    have hi : i ∉ s := (Finset.mem_sdiff.mp hiout).2
    dsimp only [gap]
    exact sub_ne_zero.mpr (hx0Outside i hi)
  have htotalNonneg : 0 ≤ total := by
    dsimp only [total]
    positivity
  have hepsPos : 0 < eps := by
    dsimp only [eps]
    positivity
  have hepsDen : eps * (1 + total) = 1 := by
    dsimp only [eps]
    field_simp
  have hepsTotal : eps * total < 1 := by
    nlinarith
  have hperturb : ∀ i, i ∈ outside →
      |eps * realDot (H i).normal w| < |gap i| := by
    intro i hiout
    have hgapPos : 0 < |gap i| := abs_pos.mpr (hgapne i hiout)
    have hratioNonneg :
        0 ≤ |realDot (H i).normal w| / |gap i| := by positivity
    have hratioLe : |realDot (H i).normal w| / |gap i| ≤ total := by
      dsimp only [total]
      exact Finset.single_le_sum
        (s := outside) (f := fun j =>
          |realDot (H j).normal w| / |gap j|)
        (fun j hj => by positivity) hiout
    have hfrac : eps *
        (|realDot (H i).normal w| / |gap i|) < 1 :=
      (mul_le_mul_of_nonneg_left hratioLe hepsPos.le).trans_lt hepsTotal
    have hprod : eps * |realDot (H i).normal w| < |gap i| := by
      apply (div_lt_one hgapPos).mp
      calc
        eps * |realDot (H i).normal w| / |gap i| =
            eps * (|realDot (H i).normal w| / |gap i|) := by ring
        _ < 1 := hfrac
    simpa [abs_mul, abs_of_pos hepsPos] using hprod
  let x : Fin k → Real := x0 + eps • w
  have hxFormula (i : Fin m) :
      realDot (H i).normal x - (H i).offset =
        gap i + eps * realDot (H i).normal w := by
    rw [show x = x0 + eps • w by rfl, realDot_add_smul]
    dsimp only [gap]
    ring
  have hxLeft (i : Fin m) :
      realDot (H i).normal x < (H i).offset ↔ i ∈ u ∪ t := by
    by_cases his : i ∈ s
    · have hiTarget := hw ⟨i, his⟩
      have hside : i ∈ t ↔
          realDot (H i).normal x < (H i).offset := by
        by_cases hit : i ∈ t
        · have htarget : target ⟨i, his⟩ = -1 := by simp [target, hit]
          rw [show realDot (H i).normal x =
            realDot (H i).normal x0 + eps * realDot (H i).normal w by
              exact realDot_add_smul _ _ _ _]
          rw [hx0S i his, hiTarget, htarget]
          simp [hit, hepsPos]
        · have htarget : target ⟨i, his⟩ = 1 := by simp [target, hit]
          constructor
          · exact fun h => (hit h).elim
          · intro hleft
            rw [show realDot (H i).normal x =
              realDot (H i).normal x0 + eps * realDot (H i).normal w by
                exact realDot_add_smul _ _ _ _] at hleft
            rw [hx0S i his, hiTarget, htarget] at hleft
            linarith
      have hiNotU : i ∉ u := by
        intro hiu
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hiu).1).2 his
      simp only [Finset.mem_union, hiNotU, false_or]
      exact hside.symm
    · have hiout : i ∈ outside := by simp [outside, his]
      have hgapNe := hgapne i hiout
      have hpert := abs_lt.mp (hperturb i hiout)
      have hiNotT : i ∉ t := fun hit => his (hts hit)
      simp only [Finset.mem_union, hiNotT, or_false]
      rw [Finset.mem_filter]
      simp only [hiout, true_and]
      constructor
      · intro hnew
        by_contra hleft
        have hgapPos : 0 < gap i := by
          have hx0ne := hx0Outside i his
          dsimp only [gap]
          have : (H i).offset < realDot (H i).normal x0 :=
            lt_of_le_of_ne (le_of_not_gt hleft) hx0ne.symm
          linarith
        have herr : -gap i < eps * realDot (H i).normal w := by
          simpa [abs_of_pos hgapPos] using hpert.1
        have hformula := hxFormula i
        linarith
      · intro hleft
        have hgapNeg : gap i < 0 := by
          dsimp only [gap]
          linarith
        have herr : eps * realDot (H i).normal w < -gap i := by
          simpa [abs_of_neg hgapNeg] using hpert.2
        have hformula := hxFormula i
        linarith
  have hxNe (i : Fin m) :
      realDot (H i).normal x ≠ (H i).offset := by
    by_cases his : i ∈ s
    · have hiTarget := hw ⟨i, his⟩
      by_cases hit : i ∈ t
      · exact ne_of_lt ((hxLeft i).mpr (Finset.mem_union_right u hit))
      · have htarget : target ⟨i, his⟩ = 1 := by simp [target, hit]
        intro heq
        have hformula := realDot_add_smul (H i).normal x0 w eps
        rw [hx0S i his, hiTarget, htarget] at hformula
        linarith
    · have hiout : i ∈ outside := by simp [outside, his]
      by_cases hiu : i ∈ u
      · exact ne_of_lt ((hxLeft i).mpr (Finset.mem_union_left t hiu))
      · have hnotleft : ¬ realDot (H i).normal x0 < (H i).offset := by
          intro hleft
          apply hiu
          exact Finset.mem_filter.mpr ⟨hiout, hleft⟩
        have hgapPos : 0 < gap i := by
          have hx0ne := hx0Outside i his
          dsimp only [gap]
          have : (H i).offset < realDot (H i).normal x0 :=
            lt_of_le_of_ne (le_of_not_gt hnotleft) hx0ne.symm
          linarith
        have herr : -gap i < eps * realDot (H i).normal w := by
          simpa [abs_of_pos hgapPos] using
            (abs_lt.mp (hperturb i hiout)).1
        intro heq
        have hformula := hxFormula i
        rw [heq] at hformula
        linarith
  let p : Fin m → Bool := fun i => decide (i ∈ u ∪ t)
  have hpReal : RealizesRegion H p := by
    refine ⟨x, fun i => ?_⟩
    by_cases hmem : i ∈ u ∪ t
    · have hleft := (hxLeft i).mpr hmem
      have hnright : ¬ (H i).offset < realDot (H i).normal x :=
        not_lt_of_ge hleft.le
      rcases Finset.mem_union.mp hmem with hiu | hit
      · simp [p, hiu, hleft, hnright]
      · simp [p, hit, hleft, hnright]
    · have hnleft : ¬ realDot (H i).normal x < (H i).offset := by
        intro hleft
        exact hmem ((hxLeft i).mp hleft)
      have hright : (H i).offset < realDot (H i).normal x :=
        lt_of_le_of_ne (le_of_not_gt hnleft) (hxNe i).symm
      have hnu : i ∉ u := fun hiu => hmem (Finset.mem_union_left _ hiu)
      have hnt : i ∉ t := fun hit => hmem (Finset.mem_union_right _ hit)
      simp [p, hnu, hnt, hnleft, hright]
  rw [regionFamily, Finset.mem_image]
  refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpReal⟩, ?_⟩
  ext i
  simp [regionTrueSet, p]

private lemma not_stronglyShatters_iff_compl_shatters
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (A : Finset (Finset alpha)) (s : Finset alpha) :
    ¬ StronglyShatters A s ↔ Aᶜ.Shatters sᶜ := by
  classical
  constructor
  · intro hstrong t hts
    rw [StronglyShatters] at hstrong
    push Not at hstrong
    have hdisj : Disjoint t s := by
      rw [Finset.disjoint_left]
      intro x hxt hxs
      have hxcomp := hts hxt
      have hxnot : x ∉ s := by simpa only [Finset.mem_compl] using hxcomp
      exact hxnot hxs
    obtain ⟨u, hus', humiss⟩ := hstrong t hdisj
    refine ⟨t ∪ u, ?_, ?_⟩
    · simpa only [Finset.mem_compl] using humiss
    · ext x
      have hts' := @hts x
      have hus'' := @hus' x
      simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_union]
      by_cases hxs : x ∈ s
      · have hnt : x ∉ t := by
          intro hxt
          have hxcomp := hts' hxt
          have hxnot : x ∉ s := by simpa only [Finset.mem_compl] using hxcomp
          exact hxnot hxs
        simp [hxs, hnt]
      · have hnu : x ∉ u := fun hxu => hxs (hus'' hxu)
        simp [hxs, hnu]
  · intro hshat hstrong
    obtain ⟨u, hus', hcube⟩ := hstrong
    have hucomp : u ⊆ sᶜ := by
      intro x hxu
      simp only [Finset.mem_compl]
      exact fun hxs => Finset.disjoint_left.mp hus' hxu hxs
    obtain ⟨c, hccompl, hcinter⟩ := hshat hucomp
    let t := s ∩ c
    have hts : t ⊆ s := Finset.inter_subset_left
    have huc : u ∪ t = c := by
      ext x
      have hi := Finset.ext_iff.mp hcinter x
      simp only [Finset.mem_inter, Finset.mem_compl] at hi
      by_cases hxs : x ∈ s
      · have hnu : x ∉ u := fun hxu => Finset.disjoint_left.mp hus' hxu hxs
        simp [t, hxs, hnu]
      · simpa [t, hxs] using hi.symm
    have hmem := hcube t hts
    rw [huc] at hmem
    have hnot : c ∉ A := by simpa using hccompl
    exact hnot hmem

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
  classical
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
  classical
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
  classical
  unfold smallSubsets
  rw [Finset.card_biUnion
    ((Finset.univ : Finset (Fin m)).pairwise_disjoint_powersetCard.set_pairwise _)]
  apply Finset.sum_congr rfl
  intro j _
  simp

private lemma smallSubsets_subset_strongShatterer {k m : Nat}
    (H : Fin m → AffineHyperplane k) (hgp : HyperplanesInGeneralPosition H) :
    smallSubsets m k ⊆ strongShatterer (regionFamily H) := by
  classical
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

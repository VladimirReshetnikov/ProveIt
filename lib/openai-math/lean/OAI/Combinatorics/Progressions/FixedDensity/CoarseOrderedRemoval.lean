-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Algebra.Order.Chebyshev
import OAI.Combinatorics.Progressions.FixedDensity.BundleCountingRecurrence
import OAI.Combinatorics.Progressions.FixedDensity.CoarseAtomBridge
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable local instance orderedEnergyFaceLinearOrder
    (k r : ℕ) : LinearOrder (OrderedFace k r) :=
  (Fintype.equivFin (OrderedFace k r)).linearOrder

namespace FaceRegularityState

theorem energy_sub_eq_mean_sq_of_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (T S : FaceRegularityState Ω)
    (hTS : T.partition ≤ S.partition)
    (f : Ω → ℝ) :
    T.energy f - S.energy f =
      mean (fun x =>
        (T.structured f x - S.structured f x) ^ 2) := by
  simpa [energy, structured] using
    partitionEnergy_sub_eq_mean_sq
      T.partition S.partition hTS f

theorem energy_mono_of_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (T S : FaceRegularityState Ω)
    (hTS : T.partition ≤ S.partition)
    (f : Ω → ℝ) :
    S.energy f ≤ T.energy f := by
  simpa [energy] using
    partitionEnergy_mono
      T.partition S.partition hTS f

end FaceRegularityState

def OrderedRefines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (T S : OrderedRegularitySystem G k r) : Prop :=
  ∀ e, (T e).partition ≤ (S e).partition

theorem OrderedRefines.refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (S : OrderedRegularitySystem G k r) :
    OrderedRefines S S :=
  fun _ => le_rfl

theorem OrderedRefines.trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {U T S : OrderedRegularitySystem G k r}
    (hUT : OrderedRefines U T)
    (hTS : OrderedRefines T S) :
    OrderedRefines U S :=
  fun e => (hUT e).trans (hTS e)

noncomputable def orderedTotalEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r) : ℝ :=
  ∑ e : OrderedFace k r,
    (S e).energy (H.edgeWeight e)

theorem orderedTotalEnergy_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r) :
    0 ≤ orderedTotalEnergy H S := by
  unfold orderedTotalEnergy
  apply Finset.sum_nonneg
  intro e _he
  exact partitionEnergy_nonneg
    (S e).partition (H.edgeWeight e)

theorem orderedTotalEnergy_le_card
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {H : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    (S : OrderedRegularitySystem G k r) :
    orderedTotalEnergy H S ≤
      Fintype.card (OrderedFace k r) := by
  unfold orderedTotalEnergy
  calc
    (∑ e : OrderedFace k r,
        (S e).energy (H.edgeWeight e)) ≤
        ∑ _e : OrderedFace k r, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _he
      exact partitionEnergy_le_one
        (S e).partition
        (fun y => (hH e y).1)
        (fun y => (hH e y).2)
    _ = Fintype.card (OrderedFace k r) := by
      simp

theorem orderedTotalEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    {T S : OrderedRegularitySystem G k r}
    (hTS : OrderedRefines T S) :
    orderedTotalEnergy H S ≤ orderedTotalEnergy H T := by
  unfold orderedTotalEnergy
  apply Finset.sum_le_sum
  intro e _he
  exact (T e).energy_mono_of_le
    (S e) (hTS e) (H.edgeWeight e)

theorem orderedTotalEnergy_sub_eq_sum_mean_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    {T S : OrderedRegularitySystem G k r}
    (hTS : OrderedRefines T S) :
    orderedTotalEnergy H T - orderedTotalEnergy H S =
      ∑ e : OrderedFace k r,
        mean (fun y =>
          ((T e).structured (H.edgeWeight e) y -
            (S e).structured (H.edgeWeight e) y) ^ 2) := by
  unfold orderedTotalEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  exact
    (T e).energy_sub_eq_mean_sq_of_le
      (S e) (hTS e) (H.edgeWeight e)

theorem orderedTotalEnergy_sub_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    {T S : OrderedRegularitySystem G k r}
    (hTS : OrderedRefines T S) :
    0 ≤ orderedTotalEnergy H T -
      orderedTotalEnergy H S :=
  sub_nonneg.mpr (orderedTotalEnergy_mono H hTS)

theorem mean_comp_orderedFaceTuple
    {G : Type*} [Fintype G] [Nonempty G]
    {k r : ℕ}
    (e : OrderedFace k r)
    (f : (Fin r → G) → ℝ) :
    mean (fun x : Fin k → G =>
      f (orderedFaceTuple e x)) = mean f := by
  rw [mean_splitOrderedFace e]
  unfold mean₂
  simp

theorem mixedOrderedPatternTerm_sq_le_edgeDiff_sq
    {G : Type*}
    {k r : ℕ}
    {H K : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    (hK : K.EdgeWeightsInUnitInterval)
    (e : OrderedFace k r) (x : Fin k → G) :
    mixedOrderedPatternTerm H K e x ^ 2 ≤
      (H.edgeWeight e (orderedFaceTuple e x) -
        K.edgeWeight e (orderedFaceTuple e x)) ^ 2 := by
  let A : ℝ :=
    ∏ f ∈ (Finset.univ : Finset (OrderedFace k r))
        with f < e,
      H.edgeWeight f (orderedFaceTuple f x)
  let B : ℝ :=
    ∏ f ∈ (Finset.univ : Finset (OrderedFace k r))
        with e < f,
      K.edgeWeight f (orderedFaceTuple f x)
  have hA0 : 0 ≤ A := by
    unfold A
    apply Finset.prod_nonneg
    intro f hf
    exact (hH f (orderedFaceTuple f x)).1
  have hA1 : A ≤ 1 := by
    unfold A
    apply Finset.prod_le_one₀
    · intro f hf
      exact (hH f (orderedFaceTuple f x)).1
    · intro f hf
      exact (hH f (orderedFaceTuple f x)).2
  have hB0 : 0 ≤ B := by
    unfold B
    apply Finset.prod_nonneg
    intro f hf
    exact (hK f (orderedFaceTuple f x)).1
  have hB1 : B ≤ 1 := by
    unfold B
    apply Finset.prod_le_one₀
    · intro f hf
      exact (hK f (orderedFaceTuple f x)).1
    · intro f hf
      exact (hK f (orderedFaceTuple f x)).2
  have hAB0 : 0 ≤ A * B :=
    mul_nonneg hA0 hB0
  have hAB1 : A * B ≤ 1 := by
    calc
      A * B ≤ 1 * B :=
        mul_le_mul_of_nonneg_right hA1 hB0
      _ ≤ 1 * 1 :=
        mul_le_mul_of_nonneg_left hB1 zero_le_one
      _ = 1 := one_mul 1
  have hABsq : (A * B) ^ 2 ≤ 1 := by
    simpa using
      (sq_le_sq₀ hAB0 zero_le_one).2 hAB1
  unfold mixedOrderedPatternTerm
  change
    ((H.edgeWeight e (orderedFaceTuple e x) -
        K.edgeWeight e (orderedFaceTuple e x)) *
      A * B) ^ 2 ≤
      (H.edgeWeight e (orderedFaceTuple e x) -
        K.edgeWeight e (orderedFaceTuple e x)) ^ 2
  calc
    ((H.edgeWeight e (orderedFaceTuple e x) -
          K.edgeWeight e (orderedFaceTuple e x)) *
        A * B) ^ 2 =
        (H.edgeWeight e (orderedFaceTuple e x) -
          K.edgeWeight e (orderedFaceTuple e x)) ^ 2 *
            (A * B) ^ 2 := by ring
    _ ≤
        (H.edgeWeight e (orderedFaceTuple e x) -
          K.edgeWeight e (orderedFaceTuple e x)) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hABsq (sq_nonneg _)
    _ = _ := mul_one _

theorem mixedOrderedPatternCorrelation_sq_le_mean_edgeDiff_sq
    {G : Type*} [Fintype G] [Nonempty G]
    {k r : ℕ}
    {H K : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    (hK : K.EdgeWeightsInUnitInterval)
    (e : OrderedFace k r) :
    |mixedOrderedPatternCorrelation H K e| ^ 2 ≤
      mean (fun y =>
        (H.edgeWeight e y - K.edgeWeight e y) ^ 2) := by
  calc
    |mixedOrderedPatternCorrelation H K e| ^ 2 =
        mixedOrderedPatternCorrelation H K e ^ 2 := by
      rw [sq_abs]
    _ ≤
        mean (fun x =>
          mixedOrderedPatternTerm H K e x ^ 2) := by
      exact mean_square_le_mean_square _
    _ ≤
        mean (fun x =>
          (H.edgeWeight e (orderedFaceTuple e x) -
            K.edgeWeight e (orderedFaceTuple e x)) ^ 2) := by
      exact mean_mono fun x =>
        mixedOrderedPatternTerm_sq_le_edgeDiff_sq
          hH hK e x
    _ =
        mean (fun y =>
          (H.edgeWeight e y - K.edgeWeight e y) ^ 2) :=
      mean_comp_orderedFaceTuple
        (G := G) (k := k) (r := r) e
        (fun y =>
          (H.edgeWeight e y - K.edgeWeight e y) ^ 2)

theorem regularizedOrderedPattern_count_sub_sq_le_totalEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {H : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    {fine coarse : OrderedRegularitySystem G k r}
    (hrefines : OrderedRefines fine coarse) :
    |(regularizedOrderedPattern H fine).patternCount -
        (regularizedOrderedPattern H coarse).patternCount| ^ 2 ≤
      (Fintype.card (OrderedFace k r) : ℝ) *
        (orderedTotalEnergy H fine -
          orderedTotalEnergy H coarse) := by
  let F := regularizedOrderedPattern H fine
  let C := regularizedOrderedPattern H coarse
  have hF : F.EdgeWeightsInUnitInterval :=
    regularizedOrderedPattern_unitInterval hH fine
  have hC : C.EdgeWeightsInUnitInterval :=
    regularizedOrderedPattern_unitInterval hH coarse
  have habs :
      |F.patternCount - C.patternCount| ≤
        ∑ e : OrderedFace k r,
          |mixedOrderedPatternCorrelation F C e| :=
    abs_patternCount_sub_le_sum_mixedOrderedPatternCorrelation F C
  have hsum0 :
      0 ≤ ∑ e : OrderedFace k r,
        |mixedOrderedPatternCorrelation F C e| :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  have hsquare :
      |F.patternCount - C.patternCount| ^ 2 ≤
        (∑ e : OrderedFace k r,
          |mixedOrderedPatternCorrelation F C e|) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hsum0).2 habs
  calc
    |F.patternCount - C.patternCount| ^ 2 ≤
        (∑ e : OrderedFace k r,
          |mixedOrderedPatternCorrelation F C e|) ^ 2 :=
      hsquare
    _ ≤
        (Fintype.card (OrderedFace k r) : ℝ) *
          ∑ e : OrderedFace k r,
            |mixedOrderedPatternCorrelation F C e| ^ 2 := by
      simpa using
        sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ :
            Finset (OrderedFace k r)))
          (f := fun e =>
            |mixedOrderedPatternCorrelation F C e|)
    _ ≤
        (Fintype.card (OrderedFace k r) : ℝ) *
          ∑ e : OrderedFace k r,
            mean (fun y =>
              ((fine e).structured (H.edgeWeight e) y -
                (coarse e).structured
                  (H.edgeWeight e) y) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro e _he
        exact
          mixedOrderedPatternCorrelation_sq_le_mean_edgeDiff_sq
            hF hC e
      · positivity
    _ =
        (Fintype.card (OrderedFace k r) : ℝ) *
          (orderedTotalEnergy H fine -
            orderedTotalEnergy H coarse) := by
      rw [orderedTotalEnergy_sub_eq_sum_mean_sq H hrefines]

theorem regularizedOrderedPattern_count_abs_sub_lt_of_energyGap
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {H : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    {fine coarse : OrderedRegularitySystem G k r}
    (hrefines : OrderedRefines fine coarse)
    {γ : ℝ} (hγ : 0 < γ)
    (hgap :
      (Fintype.card (OrderedFace k r) : ℝ) *
          (orderedTotalEnergy H fine -
            orderedTotalEnergy H coarse) <
        γ ^ 2) :
    |(regularizedOrderedPattern H fine).patternCount -
        (regularizedOrderedPattern H coarse).patternCount| <
      γ := by
  have hsquare :
      |(regularizedOrderedPattern H fine).patternCount -
          (regularizedOrderedPattern H coarse).patternCount| ^ 2 <
        γ ^ 2 :=
    (regularizedOrderedPattern_count_sub_sq_le_totalEnergyGap
      hH hrefines).trans_lt hgap
  exact
    (sq_lt_sq₀ (abs_nonneg _) hγ.le).mp hsquare

theorem exists_adjacent_sub_le_div
    (E : ℕ → ℝ) {m : ℕ} (hm : 0 < m)
    {B : ℝ}
    (hE0 : 0 ≤ E 0)
    (hEm : E m ≤ B) :
    ∃ i : ℕ, i < m ∧
      E (i + 1) - E i ≤ B / m := by
  have htel :
      ∑ i ∈ Finset.range m,
          (E (i + 1) - E i) =
        E m - E 0 := by
    exact Finset.sum_range_sub E m
  have hsum :
      ∑ i ∈ Finset.range m,
          (E (i + 1) - E i) ≤
        ∑ _i ∈ Finset.range m, B / (m : ℝ) := by
    rw [htel]
    calc
      E m - E 0 ≤ B := by linarith
      _ = ∑ _i ∈ Finset.range m,
          B / (m : ℝ) := by
        simp only [Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        field_simp
  obtain ⟨i, hi, hsmall⟩ :=
    Finset.exists_le_of_sum_le
      ⟨0, Finset.mem_range.mpr hm⟩ hsum
  exact ⟨i, Finset.mem_range.mp hi, hsmall⟩

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem finsetIndicator_biUnion_le_sum
    {ι Ω : Type*} [DecidableEq Ω]
    (s : Finset ι) (F : ι → Finset Ω) (x : Ω) :
    finsetIndicator (s.biUnion F) x ≤
      ∑ i ∈ s, finsetIndicator (F i) x := by
  by_cases hx : x ∈ s.biUnion F
  · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    rw [finsetIndicator_of_mem hx]
    calc
      1 = finsetIndicator (F i) x :=
        (finsetIndicator_of_mem hxi).symm
      _ ≤ ∑ j ∈ s, finsetIndicator (F j) x := by
        apply Finset.single_le_sum
          (s := s)
          (f := fun j => finsetIndicator (F j) x)
        · intro j hj
          by_cases hxj : x ∈ F j <;> simp [hxj]
        · exact hi
  · rw [finsetIndicator_of_not_mem hx]
    exact Finset.sum_nonneg fun i _ => by
      by_cases hxi : x ∈ F i <;> simp [hxi]

theorem mean_finsetIndicator_biUnion_le_sum
    {ι Ω : Type*} [DecidableEq Ω]
    [Fintype Ω]
    (s : Finset ι) (F : ι → Finset Ω) :
    mean (finsetIndicator (s.biUnion F)) ≤
      ∑ i ∈ s, mean (finsetIndicator (F i)) := by
  calc
    mean (finsetIndicator (s.biUnion F)) ≤
        mean (fun x => ∑ i ∈ s,
          finsetIndicator (F i) x) :=
      mean_mono (finsetIndicator_biUnion_le_sum s F)
    _ = ∑ i ∈ s, mean (finsetIndicator (F i)) :=
      mean_finset_sum s (fun i => finsetIndicator (F i))

noncomputable def ownAtomBadBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (α β : ℝ) : Finset Ω := by
  classical
  exact
    (Finset.univ : Finset upper.parts).biUnion fun a =>
      a.1 ∩ atomBadBaseSupport fine coarse upper a α β

@[simp]
theorem mem_ownAtomBadBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (α β : ℝ) (x : Ω) :
    x ∈ ownAtomBadBaseSupport fine coarse upper α β ↔
      x ∈ atomBadBaseSupport fine coarse upper
        (partitionAtomAt upper x) α β := by
  classical
  constructor
  · intro hx
    rw [ownAtomBadBaseSupport] at hx
    obtain ⟨a, _ha, hxpart⟩ :=
      Finset.mem_biUnion.mp hx
    have hxa : x ∈ a.1 :=
      (Finset.mem_inter.mp hxpart).1
    have hbad :
        x ∈ atomBadBaseSupport
          fine coarse upper a α β :=
      (Finset.mem_inter.mp hxpart).2
    have hcanonical :
        partitionAtomAt upper x = a :=
      (partitionAtomAt_eq_iff_mem upper x a).2 hxa
    simpa [hcanonical] using hbad
  · intro hbad
    rw [ownAtomBadBaseSupport]
    apply Finset.mem_biUnion.mpr
    refine
      ⟨partitionAtomAt upper x, Finset.mem_univ _, ?_⟩
    apply Finset.mem_inter.mpr
    exact
      ⟨upper.mem_part (Finset.mem_univ x), hbad⟩

theorem mean_indicator_atom_inter_badBaseSupport_le_local
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (a.1 ∩ atomBadBaseSupport
          fine coarse upper a α β)) ≤
      α + mean
        (atomBoundaryDefectSq fine coarse upper a) / β := by
  calc
    mean (finsetIndicator
        (a.1 ∩ atomBadBaseSupport
          fine coarse upper a α β)) ≤
        mean (finsetIndicator
          (a.1 ∩ smallAverageBaseSupport coarse
            (partitionAtomIndicator upper a) α)) +
        mean (finsetIndicator
          (largeDefectBaseSupport
            fine coarse upper a β)) := by
      exact
        mean_indicator_inter_union_le_add
          a.1
          (smallAverageBaseSupport coarse
            (partitionAtomIndicator upper a) α)
          (largeDefectBaseSupport fine coarse upper a β)
    _ ≤
        α + mean
          (atomBoundaryDefectSq fine coarse upper a) / β :=
      add_le_add
        (mean_indicator_inter_smallAverageBaseSupport_le
          coarse a.1 hα)
        (mean_indicator_largeAverageBaseSupport_le
          coarse
          (atomBoundaryDefectSq fine coarse upper a)
          (atomBoundaryDefectSq_nonneg
            fine coarse upper a) hβ)

theorem mean_indicator_ownAtomBadBaseSupport_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {fine coarse : FacePartition Ω}
    (hfc : fine ≤ coarse)
    (upper : FacePartition Ω)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (ownAtomBadBaseSupport fine coarse upper α β)) ≤
      (FacePartition.complexity upper : ℝ) * α +
        (partitionAtomEnergy fine upper -
          partitionAtomEnergy coarse upper) / β := by
  calc
    mean (finsetIndicator
        (ownAtomBadBaseSupport fine coarse upper α β)) ≤
        ∑ a : upper.parts,
          mean (finsetIndicator
            (a.1 ∩ atomBadBaseSupport
              fine coarse upper a α β)) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ : Finset upper.parts)
          (fun a =>
            a.1 ∩ atomBadBaseSupport
              fine coarse upper a α β)
    _ ≤
        ∑ a : upper.parts,
          (α +
            mean (atomBoundaryDefectSq
              fine coarse upper a) / β) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact
        mean_indicator_atom_inter_badBaseSupport_le_local
          fine coarse upper a hα hβ
    _ =
        (FacePartition.complexity upper : ℝ) * α +
          (partitionAtomEnergy fine upper -
            partitionAtomEnergy coarse upper) / β := by
      rw [partitionAtomEnergy_sub_eq_sum_mean_sq hfc upper]
      unfold atomBoundaryDefectSq atomBoundaryDefect
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Finset.sum_div]
      rw [Fintype.card_coe]
      rfl

noncomputable def orderedOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (α β : ℝ) :
    Finset (Fin (j + 1) → G) :=
  ownAtomBadBaseSupport
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper α β

@[simp]
theorem mem_orderedOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (α β : ℝ) (x : Fin (j + 1) → G) :
    x ∈ orderedOwnAtomBadBaseSupport
        fine coarse e upper α β ↔
      x ∈ orderedAtomBadBaseSupport
        fine coarse e upper
          (partitionAtomAt upper x) α β := by
  exact
    mem_ownAtomBadBaseSupport
      (orderedBoundaryPartition fine e)
      (orderedBoundaryPartition coarse e)
      upper α β x

theorem mean_indicator_orderedOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (orderedOwnAtomBadBaseSupport
          fine coarse e upper α β)) ≤
      (FacePartition.complexity upper : ℝ) * α +
        (orderedAtomEnergy fine e upper -
          orderedAtomEnergy coarse e upper) / β := by
  exact
    mean_indicator_ownAtomBadBaseSupport_le
      (orderedBoundaryPartition_mono hfc e)
      upper hα hβ

abbrev OrderedPositiveSubface (r : ℕ) :=
  (j : Fin r) ×' OrderedFace r (j.1 + 1)

theorem exists_orderedFace_factor_through
    {k s r : ℕ} (hsr : s ≤ r) (hrk : r ≤ k)
    (f : OrderedFace k s) :
    ∃ e : OrderedFace k r, ∃ d : OrderedFace r s,
      d.trans e = f := by
  classical
  let sf : Finset (Fin k) :=
    Finset.univ.map f.toEmbedding
  have hsf_card : sf.card = s := by
    rw [show sf.card =
        (Finset.univ : Finset (Fin s)).card by
      exact Finset.card_map f.toEmbedding]
    simp
  have hsf_univ : sf ⊆ Finset.univ :=
    Finset.subset_univ sf
  obtain ⟨t, hsf_t, _ht_univ, ht⟩ :=
    Finset.exists_subsuperset_card_eq
      hsf_univ
      (by simpa [hsf_card] using hsr)
      (by simpa using hrk)
  let e : OrderedFace k r :=
    t.orderEmbOfFin ht
  have hf_mem (i : Fin s) : f i ∈ t := by
    apply hsf_t
    exact Finset.mem_map.mpr
      ⟨i, Finset.mem_univ i, rfl⟩
  let ft : Fin s ↪o t :=
    OrderEmbedding.ofStrictMono
      (fun i => ⟨f i, hf_mem i⟩)
      (fun _ _ hij => f.strictMono hij)
  let d : OrderedFace r s :=
    ft.trans (t.orderIsoOfFin ht).symm.toOrderEmbedding
  refine ⟨e, d, ?_⟩
  apply RelEmbedding.ext
  intro i
  change
    t.orderEmbOfFin ht
        ((t.orderIsoOfFin ht).symm
          ⟨f i, hf_mem i⟩) =
      f i
  rw [← Finset.coe_orderIsoOfFin_apply]
  simp

noncomputable def orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G)) :
    Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter fun y =>
    orderedFaceTuple d y ∈ S

@[simp]
theorem mem_orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G))
    (y : Fin r → G) :
    y ∈ orderedFacePullbackFinset d S ↔
      orderedFaceTuple d y ∈ S := by
  simp [orderedFacePullbackFinset]

theorem mean_indicator_orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G)) :
    mean (finsetIndicator
        (orderedFacePullbackFinset d S)) =
      mean (finsetIndicator S) := by
  rw [show
      finsetIndicator (orderedFacePullbackFinset d S) =
        fun y => finsetIndicator S
          (orderedFaceTuple d y) by
    funext y
    by_cases hy : orderedFaceTuple d y ∈ S
    · rw [finsetIndicator_of_mem hy,
        finsetIndicator_of_mem]
      exact
        (mem_orderedFacePullbackFinset d S y).2 hy
    · rw [finsetIndicator_of_not_mem hy,
        finsetIndicator_of_not_mem]
      exact fun h =>
        hy ((mem_orderedFacePullbackFinset d S y).1 h)]
  exact mean_comp_orderedFaceTuple d
    (finsetIndicator S)

noncomputable def orderedTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ) :
    Finset (Fin r → G) := by
  classical
  exact
    (Finset.univ :
      Finset (OrderedPositiveSubface r)).biUnion fun q =>
      orderedFacePullbackFinset q.2
        (orderedOwnAtomBadBaseSupport
          (fine.layer q.1.1
            (Nat.le_of_lt q.1.2))
          (coarse.layer q.1.1
            (Nat.le_of_lt q.1.2))
          (q.2.trans e)
          (fine.partition q.1.succ
            (q.2.trans e))
          (α (q.1.1 + 1))
          (β (q.1.1 + 1)))

theorem mean_indicator_orderedTopBadBaseDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    (hfc : fine.Refines coarse)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1)) :
    mean (finsetIndicator
        (orderedTopBadBaseDeletion fine coarse e α β)) ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (fine.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          (orderedAtomEnergy
              (fine.layer q.1.1
                (Nat.le_of_lt q.1.2))
              (q.2.trans e)
              (fine.partition q.1.succ
                (q.2.trans e)) -
            orderedAtomEnergy
              (coarse.layer q.1.1
                (Nat.le_of_lt q.1.2))
              (q.2.trans e)
              (fine.partition q.1.succ
                (q.2.trans e))) /
            β (q.1.1 + 1)) := by
  calc
    mean (finsetIndicator
        (orderedTopBadBaseDeletion fine coarse e α β)) ≤
        ∑ q : OrderedPositiveSubface r,
          mean (finsetIndicator
            (orderedFacePullbackFinset q.2
              (orderedOwnAtomBadBaseSupport
                (fine.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (coarse.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (q.2.trans e)
                (fine.partition q.1.succ
                  (q.2.trans e))
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ :
            Finset (OrderedPositiveSubface r))
          (fun q =>
            orderedFacePullbackFinset q.2
              (orderedOwnAtomBadBaseSupport
                (fine.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (coarse.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (q.2.trans e)
                (fine.partition q.1.succ
                  (q.2.trans e))
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))
    _ ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (fine.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            (orderedAtomEnergy
                (fine.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (q.2.trans e)
                (fine.partition q.1.succ
                  (q.2.trans e)) -
              orderedAtomEnergy
                (coarse.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (q.2.trans e)
                (fine.partition q.1.succ
                  (q.2.trans e))) /
              β (q.1.1 + 1)) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [mean_indicator_orderedFacePullbackFinset]
      have hlayer :
          OrderedFacePartitionRefines
            (fine.layer q.1.1
              (Nat.le_of_lt q.1.2))
            (coarse.layer q.1.1
              (Nat.le_of_lt q.1.2)) := by
        intro g
        exact hfc
          ⟨q.1.1,
            Nat.lt_succ_iff.mpr
              (Nat.le_of_lt q.1.2)⟩ g
      exact
        mean_indicator_orderedOwnAtomBadBaseSupport_le
          hlayer
          (q.2.trans e)
          (fine.partition q.1.succ
            (q.2.trans e))
          (hα q.1.1) (hβ q.1.1)

noncomputable def orderedBadBaseDeletionFamily
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r)
    (α β : ℕ → ℝ) :
    OrderedPattern.DeletionFamily (G := G) k r :=
  fun e => orderedTopBadBaseDeletion fine coarse e α β

theorem faceDeletionDensity_orderedBadBaseDeletionFamily_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    (hfc : fine.Refines coarse)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1))
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          fine coarse α β) e ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (fine.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          (orderedAtomEnergy
              (fine.layer q.1.1
                (Nat.le_of_lt q.1.2))
              (q.2.trans e)
              (fine.partition q.1.succ
                (q.2.trans e)) -
            orderedAtomEnergy
              (coarse.layer q.1.1
                (Nat.le_of_lt q.1.2))
              (q.2.trans e)
              (fine.partition q.1.succ
                (q.2.trans e))) /
            β (q.1.1 + 1)) := by
  rw [show
      OrderedPattern.faceDeletionDensity
          (orderedBadBaseDeletionFamily
            fine coarse α β) e =
        mean (finsetIndicator
          (orderedTopBadBaseDeletion
            fine coarse e α β)) by
    unfold OrderedPattern.faceDeletionDensity
      orderedBadBaseDeletionFamily
    rw [mean_finsetIndicator]]
  exact
    mean_indicator_orderedTopBadBaseDeletion_le
      hfc e α β hα hβ

theorem faceDeletionDensity_orderedBadBaseDeletionFamily_constant_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r M : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (hcomplex :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (P.fine.partition j e) ≤ M)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          P.fine P.coarse (fun _ => α) (fun _ => β)) e ≤
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
        ((M : ℝ) * α + P.totalAtomEnergyGap / β) := by
  calc
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          P.fine P.coarse (fun _ => α) (fun _ => β)) e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.fine.partition q.1.succ
                (q.2.trans e)) : ℝ) * α +
            (orderedAtomEnergy
                (P.fine.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (q.2.trans e)
                (P.fine.partition q.1.succ
                  (q.2.trans e)) -
              orderedAtomEnergy
                (P.coarse.layer q.1.1
                  (Nat.le_of_lt q.1.2))
                (q.2.trans e)
                (P.fine.partition q.1.succ
                  (q.2.trans e))) / β) := by
      exact
        faceDeletionDensity_orderedBadBaseDeletionFamily_le
          P.refines (fun _ => α) (fun _ => β)
          (fun _ => hα) (fun _ => hβ) e
    _ ≤
        ∑ _q : OrderedPositiveSubface r,
          ((M : ℝ) * α +
            P.totalAtomEnergyGap / β) := by
      apply Finset.sum_le_sum
      intro q _hq
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ hα
        exact_mod_cast
          hcomplex q.1.succ (q.2.trans e)
      · apply div_le_div_of_nonneg_right _ hβ.le
        have hfineLayer :
            P.fine.layer q.1.1
                (Nat.le_of_lt q.1.2) =
              P.fine.partition q.1.castSucc := by
          rfl
        have hcoarseLayer :
            P.coarse.layer q.1.1
                (Nat.le_of_lt q.1.2) =
              P.coarse.partition q.1.castSucc := by
          rfl
        rw [hfineLayer, hcoarseLayer]
        change
          P.faceAtomEnergyGap q.1 (q.2.trans e) ≤
            P.totalAtomEnergyGap
        exact
          P.faceAtomEnergyGap_le_total
            q.1 (q.2.trans e)
    _ =
        (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          ((M : ℝ) * α +
            P.totalAtomEnergyGap / β) := by
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]

theorem faceDeletionDensity_orderedBadBaseDeletionFamily_constant_le_of_bound
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r M : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (hcomplex :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (P.fine.partition j e) ≤ M)
    {α β ε : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (hparameters :
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          ((M : ℝ) * α + P.totalAtomEnergyGap / β) ≤
        ε)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          P.fine P.coarse (fun _ => α) (fun _ => β)) e ≤
      ε :=
  (faceDeletionDensity_orderedBadBaseDeletionFamily_constant_le
    P hcomplex hα hβ e).trans hparameters

theorem ClosedOrderedAtomConfiguration.isGood_of_avoids_topBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (hrk : r ≤ k)
    (fine coarse : OrderedPartitionComplex G k r)
    (x : Fin k → G) (α β : ℕ → ℝ)
    (havoid :
      ∀ e : OrderedFace k r,
        orderedFaceTuple e x ∉
          orderedTopBadBaseDeletion
            fine coarse e α β) :
    (ClosedOrderedAtomConfiguration.ofTuple fine x).IsGood
      fine coarse α β := by
  apply
    (ClosedOrderedAtomConfiguration.ofTuple fine x).isGood_of_avoids_badBases
      fine coarse α β
  intro j hj f hbad
  obtain ⟨e, d, hde⟩ :=
    exists_orderedFace_factor_through
      (Nat.succ_le_iff.mpr hj) hrk f
  apply havoid e
  rw [orderedTopBadBaseDeletion]
  apply Finset.mem_biUnion.mpr
  refine
    ⟨⟨⟨j, hj⟩, d⟩, Finset.mem_univ _, ?_⟩
  rw [mem_orderedFacePullbackFinset]
  have htuple :
      orderedFaceTuple d (orderedFaceTuple e x) =
        orderedFaceTuple f x := by
    rw [show
        orderedFaceTuple d (orderedFaceTuple e x) =
          orderedFaceTuple (d.trans e) x by rfl,
      hde]
  rw [htuple, hde]
  exact
    (mem_orderedOwnAtomBadBaseSupport
      (fine.layer j (Nat.le_of_lt hj))
      (coarse.layer j (Nat.le_of_lt hj))
      f
      (fine.partition
        ⟨j + 1, Nat.succ_lt_succ hj⟩ f)
      (α (j + 1)) (β (j + 1))
      (orderedFaceTuple f x)).2 hbad

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedCoarseFineComplex

noncomputable def orderedCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r)
    (e : OrderedFace k (j.1 + 1))
    (α β : ℝ) :
    Finset (Fin (j.1 + 1) → G) :=
  orderedOwnAtomBadBaseSupport
    (P.fine.partition j.castSucc)
    (P.coarse.partition j.castSucc)
    e
    (P.coarse.partition j.succ e)
    α β

@[simp]
theorem mem_orderedCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r)
    (e : OrderedFace k (j.1 + 1))
    (α β : ℝ) (x : Fin (j.1 + 1) → G) :
    x ∈ P.orderedCoarseOwnAtomBadBaseSupport j e α β ↔
      x ∈ orderedAtomBadBaseSupport
        (P.fine.partition j.castSucc)
        (P.coarse.partition j.castSucc)
        e
        (P.coarse.partition j.succ e)
        (partitionAtomAt
          (P.coarse.partition j.succ e) x)
        α β := by
  exact
    mem_orderedOwnAtomBadBaseSupport
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.castSucc)
      e (P.coarse.partition j.succ e) α β x

theorem mean_indicator_orderedCoarseOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r)
    (e : OrderedFace k (j.1 + 1))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (P.orderedCoarseOwnAtomBadBaseSupport
          j e α β)) ≤
      (FacePartition.complexity
          (P.coarse.partition j.succ e) : ℝ) * α +
        P.coarseUpperFaceAtomEnergyGap j e / β := by
  unfold orderedCoarseOwnAtomBadBaseSupport
    coarseUpperFaceAtomEnergyGap
  apply
    mean_indicator_orderedOwnAtomBadBaseSupport_le
      (fun f => P.refines j.castSucc f)
      e (P.coarse.partition j.succ e) hα hβ

end OrderedCoarseFineComplex

namespace ClosedOrderedAtomConfiguration

def IsMixedGoodAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (j : ℕ) (hj : j < r)
    (e : OrderedFace k (j + 1))
    (α β : ℝ) : Prop :=
  OrderedAtomIsGoodAtBoundary
    (P.fine.partition
      (⟨j, hj⟩ : Fin r).castSucc)
    (P.coarse.partition
      (⟨j, hj⟩ : Fin r).castSucc)
    e
    (P.coarse.partition
      (⟨j, hj⟩ : Fin r).succ e)
    (A.atom (⟨j, hj⟩ : Fin r).succ e)
    (orderedFaceTuple e A.witness)
    α β

def IsMixedGood
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ (j : ℕ) (hj : j < r) (e : OrderedFace k (j + 1)),
    A.IsMixedGoodAt P j hj e
      (α (j + 1)) (β (j + 1))

theorem isMixedGoodAt_of_not_mem_coarseBadBase
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (j : ℕ) (hj : j < r)
    (e : OrderedFace k (j + 1))
    (α β : ℝ)
    (havoid :
      orderedFaceTuple e A.witness ∉
        P.orderedCoarseOwnAtomBadBaseSupport
          ⟨j, hj⟩ e α β) :
    A.IsMixedGoodAt P j hj e α β := by
  apply
    orderedAtomIsGoodAtBoundary_of_not_mem_badBase
      (P.fine.partition
        (⟨j, hj⟩ : Fin r).castSucc)
      (P.coarse.partition
        (⟨j, hj⟩ : Fin r).castSucc)
      e
      (P.coarse.partition
        (⟨j, hj⟩ : Fin r).succ e)
      (A.atom (⟨j, hj⟩ : Fin r).succ e)
      (orderedFaceTuple e A.witness)
      α β
  intro hbad
  apply havoid
  unfold
    OrderedCoarseFineComplex.orderedCoarseOwnAtomBadBaseSupport
    orderedOwnAtomBadBaseSupport
    ownAtomBadBaseSupport
  apply Finset.mem_biUnion.mpr
  refine
    ⟨A.atom (⟨j, hj⟩ : Fin r).succ e,
      Finset.mem_univ _, ?_⟩
  exact Finset.mem_inter.mpr
    ⟨A.mem_atom (⟨j, hj⟩ : Fin r).succ e, hbad⟩

theorem isMixedGood_of_avoids_coarseBadBases
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (havoid :
      ∀ (j : ℕ) (hj : j < r)
        (e : OrderedFace k (j + 1)),
        orderedFaceTuple e A.witness ∉
          P.orderedCoarseOwnAtomBadBaseSupport
            ⟨j, hj⟩ e
            (α (j + 1)) (β (j + 1))) :
    A.IsMixedGood P α β := by
  intro j hj e
  exact
    A.isMixedGoodAt_of_not_mem_coarseBadBase
      P j hj e (α (j + 1)) (β (j + 1))
      (havoid j hj e)

end ClosedOrderedAtomConfiguration

namespace OrderedCoarseFineComplex

noncomputable def orderedCoarseTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ) :
    Finset (Fin r → G) := by
  classical
  exact
    (Finset.univ :
      Finset (OrderedPositiveSubface r)).biUnion fun q =>
      orderedFacePullbackFinset q.2
        (P.orderedCoarseOwnAtomBadBaseSupport
          q.1 (q.2.trans e)
          (α (q.1.1 + 1))
          (β (q.1.1 + 1)))

noncomputable def orderedCoarseBadBaseDeletionFamily
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ) :
    OrderedPattern.DeletionFamily (G := G) k r :=
  fun e => P.orderedCoarseTopBadBaseDeletion e α β

theorem mean_indicator_orderedCoarseTopBadBaseDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1)) :
    mean (finsetIndicator
        (P.orderedCoarseTopBadBaseDeletion e α β)) ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          P.coarseUpperFaceAtomEnergyGap
              q.1 (q.2.trans e) /
            β (q.1.1 + 1)) := by
  calc
    mean (finsetIndicator
        (P.orderedCoarseTopBadBaseDeletion e α β)) ≤
        ∑ q : OrderedPositiveSubface r,
          mean (finsetIndicator
            (orderedFacePullbackFinset q.2
              (P.orderedCoarseOwnAtomBadBaseSupport
                q.1 (q.2.trans e)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ :
            Finset (OrderedPositiveSubface r))
          (fun q =>
            orderedFacePullbackFinset q.2
              (P.orderedCoarseOwnAtomBadBaseSupport
                q.1 (q.2.trans e)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))
    _ ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap
                q.1 (q.2.trans e) /
              β (q.1.1 + 1)) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [mean_indicator_orderedFacePullbackFinset]
      exact
        mean_indicator_orderedCoarseOwnAtomBadBaseSupport_le
          P q.1 (q.2.trans e)
          (hα q.1.1) (hβ q.1.1)

theorem faceDeletionDensity_orderedCoarseBadBaseDeletionFamily_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1))
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.orderedCoarseBadBaseDeletionFamily α β) e ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          P.coarseUpperFaceAtomEnergyGap
              q.1 (q.2.trans e) /
            β (q.1.1 + 1)) := by
  rw [show
      OrderedPattern.faceDeletionDensity
          (P.orderedCoarseBadBaseDeletionFamily α β) e =
        mean (finsetIndicator
          (P.orderedCoarseTopBadBaseDeletion e α β)) by
    unfold OrderedPattern.faceDeletionDensity
      orderedCoarseBadBaseDeletionFamily
    rw [mean_finsetIndicator]]
  exact
    mean_indicator_orderedCoarseTopBadBaseDeletion_le
      P e α β hα hβ

theorem faceDeletionDensity_orderedCoarseBadBaseDeletionFamily_le_fineGap
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1))
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.orderedCoarseBadBaseDeletionFamily α β) e ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          ((FacePartition.complexity
              (P.fine.partition q.1.succ
                (q.2.trans e)) : ℝ) *
            P.faceAtomEnergyGap
              q.1 (q.2.trans e)) /
            β (q.1.1 + 1)) := by
  calc
    OrderedPattern.faceDeletionDensity
        (P.orderedCoarseBadBaseDeletionFamily α β) e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap
                q.1 (q.2.trans e) /
              β (q.1.1 + 1)) :=
      faceDeletionDensity_orderedCoarseBadBaseDeletionFamily_le
        P α β hα hβ e
    _ ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            ((FacePartition.complexity
                (P.fine.partition q.1.succ
                  (q.2.trans e)) : ℝ) *
              P.faceAtomEnergyGap
                q.1 (q.2.trans e)) /
              β (q.1.1 + 1)) := by
      apply Finset.sum_le_sum
      intro q _hq
      exact add_le_add
        (le_refl _)
        (div_le_div_of_nonneg_right
          (P.coarseUpperFaceAtomEnergyGap_le
            q.1 (q.2.trans e))
          (hβ q.1.1).le)

theorem faceDeletionDensity_orderedCoarseBadBaseDeletionFamily_constant_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r coarseBound fineBound : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (hcoarse :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (P.coarse.partition j e) ≤ coarseBound)
    (hfine :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (P.fine.partition j e) ≤ fineBound)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.orderedCoarseBadBaseDeletionFamily
          (fun _ => α) (fun _ => β)) e ≤
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
        ((coarseBound : ℝ) * α +
          (fineBound : ℝ) * P.totalAtomEnergyGap / β) := by
  calc
    OrderedPattern.faceDeletionDensity
        (P.orderedCoarseBadBaseDeletionFamily
          (fun _ => α) (fun _ => β)) e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) * α +
            ((FacePartition.complexity
                (P.fine.partition q.1.succ
                  (q.2.trans e)) : ℝ) *
              P.faceAtomEnergyGap
                q.1 (q.2.trans e)) / β) := by
      exact
        faceDeletionDensity_orderedCoarseBadBaseDeletionFamily_le_fineGap
          P (fun _ => α) (fun _ => β)
          (fun _ => hα) (fun _ => hβ) e
    _ ≤
        ∑ _q : OrderedPositiveSubface r,
          ((coarseBound : ℝ) * α +
            (fineBound : ℝ) * P.totalAtomEnergyGap / β) := by
      apply Finset.sum_le_sum
      intro q _hq
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr
            (hcoarse q.1.succ (q.2.trans e)))
          hα
      · apply div_le_div_of_nonneg_right _ hβ.le
        calc
          (FacePartition.complexity
                (P.fine.partition q.1.succ
                  (q.2.trans e)) : ℝ) *
              P.faceAtomEnergyGap
                q.1 (q.2.trans e) ≤
              (fineBound : ℝ) *
                P.faceAtomEnergyGap
                  q.1 (q.2.trans e) :=
            mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr
                (hfine q.1.succ (q.2.trans e)))
              (P.faceAtomEnergyGap_nonneg
                q.1 (q.2.trans e))
          _ ≤
              (fineBound : ℝ) *
                P.totalAtomEnergyGap :=
            mul_le_mul_of_nonneg_left
              (P.faceAtomEnergyGap_le_total
                q.1 (q.2.trans e))
              (Nat.cast_nonneg fineBound)
    _ =
        (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          ((coarseBound : ℝ) * α +
            (fineBound : ℝ) * P.totalAtomEnergyGap / β) := by
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]

end OrderedCoarseFineComplex

namespace ClosedOrderedAtomConfiguration

theorem isMixedGood_of_avoids_coarseTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (hrk : r ≤ k)
    (P : OrderedCoarseFineComplex G k r)
    (x : Fin k → G) (α β : ℕ → ℝ)
    (havoid :
      ∀ e : OrderedFace k r,
        orderedFaceTuple e x ∉
          P.orderedCoarseTopBadBaseDeletion e α β) :
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).IsMixedGood P α β := by
  apply
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).isMixedGood_of_avoids_coarseBadBases
      P α β
  intro j hj f hbad
  obtain ⟨e, d, hde⟩ :=
    exists_orderedFace_factor_through
      (Nat.succ_le_iff.mpr hj) hrk f
  apply havoid e
  rw [
    OrderedCoarseFineComplex.orderedCoarseTopBadBaseDeletion]
  apply Finset.mem_biUnion.mpr
  refine
    ⟨⟨⟨j, hj⟩, d⟩, Finset.mem_univ _, ?_⟩
  rw [mem_orderedFacePullbackFinset]
  have htuple :
      orderedFaceTuple d (orderedFaceTuple e x) =
        orderedFaceTuple f x := by
    rw [show
        orderedFaceTuple d (orderedFaceTuple e x) =
          orderedFaceTuple (d.trans e) x by rfl,
      hde]
  rw [htuple, hde]
  exact hbad

end ClosedOrderedAtomConfiguration

end Erdos3.FixedDensity

end

end OAI

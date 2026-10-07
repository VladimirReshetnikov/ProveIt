import OAI.Combinatorics.Progressions.FixedDensity.OrderedAtomEnergy

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def partitionAtomAt
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) :
    P.parts :=
  ⟨P.part x, P.part_mem.2 (Finset.mem_univ x)⟩

@[simp]
theorem partitionAtomAt_val
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) :
    (partitionAtomAt P x).1 = P.part x :=
  rfl

@[simp]
theorem partitionAtomAt_eq_iff_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x : Ω) (a : P.parts) :
    partitionAtomAt P x = a ↔ x ∈ a.1 := by
  constructor
  · intro h
    rw [← h]
    exact P.mem_part (Finset.mem_univ x)
  · intro hx
    apply Subtype.ext
    exact P.part_eq_of_mem a.2 hx

theorem partitionAtomAt_eq_iff_mem_part
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x y : Ω) :
    partitionAtomAt P y = partitionAtomAt P x ↔
      y ∈ P.part x := by
  rw [partitionAtomAt_eq_iff_mem]
  rfl

theorem partitionAtomIndicator_measurable
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (a : P.parts) :
    IsPartitionMeasurable P (partitionAtomIndicator P a) := by
  intro x y hy
  have hxy :
      partitionAtomAt P y = partitionAtomAt P x :=
    (partitionAtomAt_eq_iff_mem_part P x y).2 hy
  by_cases hx : x ∈ a.1
  · have hax : partitionAtomAt P x = a :=
      (partitionAtomAt_eq_iff_mem P x a).2 hx
    have hay : partitionAtomAt P y = a := hxy.trans hax
    have hy' : y ∈ a.1 :=
      (partitionAtomAt_eq_iff_mem P y a).1 hay
    simp [partitionAtomIndicator_of_mem P a hx,
      partitionAtomIndicator_of_mem P a hy']
  · have hy' : y ∉ a.1 := by
      intro hya
      have hay : partitionAtomAt P y = a :=
        (partitionAtomAt_eq_iff_mem P y a).2 hya
      have hax : partitionAtomAt P x = a :=
        hxy.symm.trans hay
      exact hx ((partitionAtomAt_eq_iff_mem P x a).1 hax)
    simp [partitionAtomIndicator_of_not_mem P a hx,
      partitionAtomIndicator_of_not_mem P a hy']

def partitionAtomUnion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) :
    Finset Ω :=
  s.biUnion fun a => a.1

@[simp]
theorem mem_partitionAtomUnion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) (x : Ω) :
    x ∈ partitionAtomUnion P s ↔
      ∃ a ∈ s, x ∈ a.1 := by
  simp [partitionAtomUnion]

theorem mem_partitionAtomUnion_iff_atomAt_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) (x : Ω) :
    x ∈ partitionAtomUnion P s ↔
      partitionAtomAt P x ∈ s := by
  constructor
  · intro hx
    obtain ⟨a, ha, hxa⟩ :=
      (mem_partitionAtomUnion P s x).1 hx
    have hcanonical :
        partitionAtomAt P x = a :=
      (partitionAtomAt_eq_iff_mem P x a).2 hxa
    simpa [hcanonical] using ha
  · intro hx
    exact
      (mem_partitionAtomUnion P s x).2
        ⟨partitionAtomAt P x, hx,
          P.mem_part (Finset.mem_univ x)⟩

theorem selectedPartitionAtoms_pairwiseDisjoint
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) :
    (↑s : Set P.parts).PairwiseDisjoint
      (fun a => a.1) := by
  intro a _ha b _hb hab
  exact
    P.disjoint a.2 b.2
      (fun hv => hab (Subtype.ext hv))

theorem card_partitionAtomUnion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) :
    (partitionAtomUnion P s).card =
      ∑ a ∈ s, a.1.card := by
  exact Finset.card_biUnion
    (selectedPartitionAtoms_pairwiseDisjoint P s)

theorem finsetIndicator_partitionAtomUnion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) (x : Ω) :
    finsetIndicator (partitionAtomUnion P s) x =
      ∑ a ∈ s, partitionAtomIndicator P a x := by
  classical
  by_cases hx : x ∈ partitionAtomUnion P s
  · obtain ⟨a, ha, hxa⟩ :=
      (mem_partitionAtomUnion P s x).1 hx
    rw [finsetIndicator_of_mem hx,
      Finset.sum_eq_single a]
    · exact (partitionAtomIndicator_of_mem P a hxa).symm
    · intro b hb hba
      apply partitionAtomIndicator_of_not_mem
      intro hxb
      have hab : b = a := by
        apply Subtype.ext
        exact P.eq_of_mem_parts b.2 a.2 hxb hxa
      exact hba hab
    · intro hnot
      exact (hnot ha).elim
  · rw [finsetIndicator_of_not_mem hx]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    apply partitionAtomIndicator_of_not_mem
    intro hxa
    exact hx
      ((mem_partitionAtomUnion P s x).2 ⟨a, ha, hxa⟩)

theorem mean_finsetIndicator_partitionAtomUnion
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) :
    mean (finsetIndicator (partitionAtomUnion P s)) =
      ∑ a ∈ s, mean (partitionAtomIndicator P a) := by
  rw [show
      finsetIndicator (partitionAtomUnion P s) =
        fun x => ∑ a ∈ s, partitionAtomIndicator P a x by
    funext x
    exact finsetIndicator_partitionAtomUnion P s x]
  unfold mean
  exact
    Finset.expect_sum_comm
      (Finset.univ : Finset Ω) s
      (fun x a => partitionAtomIndicator P a x)

theorem partitionAtomUnion_indicator_measurable
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) :
    IsPartitionMeasurable P
      (finsetIndicator (partitionAtomUnion P s)) := by
  intro x y hy
  have hxy :
      partitionAtomAt P y = partitionAtomAt P x :=
    (partitionAtomAt_eq_iff_mem_part P x y).2 hy
  have hmem :
      y ∈ partitionAtomUnion P s ↔
        x ∈ partitionAtomUnion P s := by
    rw [mem_partitionAtomUnion_iff_atomAt_mem,
      mem_partitionAtomUnion_iff_atomAt_mem, hxy]
  by_cases hx : x ∈ partitionAtomUnion P s
  · have hy' : y ∈ partitionAtomUnion P s := hmem.mpr hx
    simp [finsetIndicator_of_mem hx,
      finsetIndicator_of_mem hy']
  · have hy' : y ∉ partitionAtomUnion P s :=
      fun h => hx (hmem.mp h)
    simp [finsetIndicator_of_not_mem hx,
      finsetIndicator_of_not_mem hy']

theorem mean_mul_partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (a : P.parts) :
    mean (fun x => f x * partitionAtomIndicator P a x) =
      conditionalMean P f (P.representative a) *
        mean (partitionAtomIndicator P a) := by
  rw [FaceRegularityState.mean_mul_eq_mean_conditionalMean_mul
    P f (partitionAtomIndicator P a)
    (partitionAtomIndicator_measurable P a)]
  rw [← mean_smul]
  apply congrArg mean
  funext x
  by_cases hx : x ∈ a.1
  · rw [partitionAtomIndicator_of_mem P a hx,
      mul_one, mul_one]
    have hrep :
        P.representative a ∈ P.part x := by
      rw [P.part_eq_of_mem a.2 hx]
      exact P.representative_mem a
    exact
      (conditionalMean_eq_of_mem_part P f hrep).symm
  · rw [partitionAtomIndicator_of_not_mem P a hx,
      mul_zero, mul_zero]

theorem mean_mul_partitionAtomIndicator_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (a : P.parts)
    {β : ℝ}
    (hβ : conditionalMean P f (P.representative a) ≤ β) :
    mean (fun x => f x * partitionAtomIndicator P a x) ≤
      β * mean (partitionAtomIndicator P a) := by
  rw [mean_mul_partitionAtomIndicator P f a]
  apply mul_le_mul_of_nonneg_right hβ
  exact mean_nonneg fun x =>
    partitionAtomIndicator_nonneg P a x

noncomputable def smallAverageBaseAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ) :
    Finset P.parts := by
  classical
  exact (Finset.univ : Finset P.parts).filter fun b =>
    conditionalMean P f (P.representative b) < α

noncomputable def smallAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ) :
    Finset Ω :=
  partitionAtomUnion P (smallAverageBaseAtoms P f α)

@[simp]
theorem mem_smallAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ)
    (x : Ω) :
    x ∈ smallAverageBaseSupport P f α ↔
      conditionalMean P f x < α := by
  rw [smallAverageBaseSupport,
    mem_partitionAtomUnion_iff_atomAt_mem]
  simp only [smallAverageBaseAtoms, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hrep :
      P.representative (partitionAtomAt P x) ∈
        P.part x := by
    exact P.representative_mem (partitionAtomAt P x)
  have heq :=
    conditionalMean_eq_of_mem_part P f hrep
  rw [heq]

theorem mean_indicator_inter_smallAverageBaseSupport_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P : FacePartition Ω) (A : Finset Ω)
    {α : ℝ} (hα : 0 ≤ α) :
    mean (finsetIndicator
      (A ∩ smallAverageBaseSupport P (finsetIndicator A) α)) ≤
      α := by
  rw [show
      finsetIndicator
          (A ∩ smallAverageBaseSupport P (finsetIndicator A) α) =
        fun x =>
          finsetIndicator A x *
            finsetIndicator
              (smallAverageBaseSupport
                P (finsetIndicator A) α) x by
    funext x
    by_cases hxA : x ∈ A <;>
      by_cases hxB :
        x ∈ smallAverageBaseSupport P (finsetIndicator A) α <;>
      simp [hxA, hxB]]
  rw [FaceRegularityState.mean_mul_eq_mean_conditionalMean_mul
    P (finsetIndicator A)
      (finsetIndicator
        (smallAverageBaseSupport P (finsetIndicator A) α))
      (partitionAtomUnion_indicator_measurable P
        (smallAverageBaseAtoms P (finsetIndicator A) α))]
  calc
    mean (fun x =>
        conditionalMean P (finsetIndicator A) x *
          finsetIndicator
            (smallAverageBaseSupport P
              (finsetIndicator A) α) x) ≤
        mean (fun _x : Ω => α) := by
      apply mean_mono
      intro x
      by_cases hx :
          x ∈ smallAverageBaseSupport P (finsetIndicator A) α
      · rw [finsetIndicator_of_mem hx, mul_one]
        exact
          (mem_smallAverageBaseSupport
            P (finsetIndicator A) α x).1 hx |>.le
      · rw [finsetIndicator_of_not_mem hx, mul_zero]
        exact hα
    _ = α := mean_const α

noncomputable def largeAverageBaseAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ) :
    Finset P.parts := by
  classical
  exact (Finset.univ : Finset P.parts).filter fun b =>
    β < conditionalMean P f (P.representative b)

noncomputable def largeAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ) :
    Finset Ω :=
  partitionAtomUnion P (largeAverageBaseAtoms P f β)

@[simp]
theorem mem_largeAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ)
    (x : Ω) :
    x ∈ largeAverageBaseSupport P f β ↔
      β < conditionalMean P f x := by
  rw [largeAverageBaseSupport,
    mem_partitionAtomUnion_iff_atomAt_mem]
  simp only [largeAverageBaseAtoms, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hrep :
      P.representative (partitionAtomAt P x) ∈
        P.part x := by
    exact P.representative_mem (partitionAtomAt P x)
  have heq :=
    conditionalMean_eq_of_mem_part P f hrep
  rw [heq]

theorem mul_mean_indicator_largeAverageBaseSupport_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    {β : ℝ} (_hβ : 0 ≤ β) :
    β * mean (finsetIndicator
        (largeAverageBaseSupport P f β)) ≤
      mean f := by
  rw [← mean_smul]
  calc
    mean (fun x =>
        β * finsetIndicator
          (largeAverageBaseSupport P f β) x) ≤
        mean (conditionalMean P f) := by
      apply mean_mono
      intro x
      by_cases hx : x ∈ largeAverageBaseSupport P f β
      · rw [finsetIndicator_of_mem hx, mul_one]
        exact
          (mem_largeAverageBaseSupport P f β x).1 hx |>.le
      · rw [finsetIndicator_of_not_mem hx, mul_zero]
        exact conditionalMean_nonneg P hf x
    _ = mean f := mean_conditionalMean P f

theorem mean_indicator_largeAverageBaseSupport_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    {β : ℝ} (hβ : 0 < β) :
    mean (finsetIndicator
        (largeAverageBaseSupport P f β)) ≤
      mean f / β := by
  apply (le_div_iff₀ hβ).2
  simpa [mul_comm] using
    mul_mean_indicator_largeAverageBaseSupport_le
      P f hf hβ.le

noncomputable def atomBoundaryDefect
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (x : Ω) : ℝ :=
  conditionalMean fine (partitionAtomIndicator upper a) x -
    conditionalMean coarse (partitionAtomIndicator upper a) x

noncomputable def atomBoundaryDefectSq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (x : Ω) : ℝ :=
  atomBoundaryDefect fine coarse upper a x ^ 2

theorem atomBoundaryDefectSq_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (x : Ω) :
    0 ≤ atomBoundaryDefectSq fine coarse upper a x :=
  sq_nonneg _

noncomputable def largeDefectBaseAtoms
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (β : ℝ) :
    Finset coarse.parts :=
  largeAverageBaseAtoms coarse
    (atomBoundaryDefectSq fine coarse upper a) β

noncomputable def largeDefectBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (β : ℝ) :
    Finset Ω :=
  partitionAtomUnion coarse
    (largeDefectBaseAtoms fine coarse upper a β)

@[simp]
theorem mem_largeDefectBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (β : ℝ) (x : Ω) :
    x ∈ largeDefectBaseSupport fine coarse upper a β ↔
      β <
        conditionalMean coarse
          (atomBoundaryDefectSq fine coarse upper a) x := by
  exact
    mem_largeAverageBaseSupport coarse
      (atomBoundaryDefectSq fine coarse upper a) β x

theorem mean_atomBoundaryDefectSq_le_atomEnergy_sub
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fine coarse : FacePartition Ω}
    (hfc : fine ≤ coarse)
    (upper : FacePartition Ω) (a : upper.parts) :
    mean (atomBoundaryDefectSq fine coarse upper a) ≤
      partitionAtomEnergy fine upper -
        partitionAtomEnergy coarse upper := by
  rw [partitionAtomEnergy_sub_eq_sum_mean_sq hfc upper]
  exact
    Finset.single_le_sum
      (s := (Finset.univ : Finset upper.parts))
      (f := fun b =>
        mean (fun x =>
          (conditionalMean fine
                (partitionAtomIndicator upper b) x -
            conditionalMean coarse
                (partitionAtomIndicator upper b) x) ^ 2))
      (fun b _ => mean_nonneg fun x => sq_nonneg _)
      (Finset.mem_univ a)

theorem mul_mean_indicator_largeDefectBaseSupport_le_atomEnergy_sub
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fine coarse : FacePartition Ω}
    (hfc : fine ≤ coarse)
    (upper : FacePartition Ω) (a : upper.parts)
    {β : ℝ} (hβ : 0 ≤ β) :
    β * mean (finsetIndicator
        (largeDefectBaseSupport fine coarse upper a β)) ≤
      partitionAtomEnergy fine upper -
        partitionAtomEnergy coarse upper := by
  exact
    (mul_mean_indicator_largeAverageBaseSupport_le
      coarse (atomBoundaryDefectSq fine coarse upper a)
      (atomBoundaryDefectSq_nonneg fine coarse upper a)
      hβ).trans
      (mean_atomBoundaryDefectSq_le_atomEnergy_sub
        hfc upper a)

theorem mean_indicator_largeDefectBaseSupport_le_atomEnergy_sub_div
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {fine coarse : FacePartition Ω}
    (hfc : fine ≤ coarse)
    (upper : FacePartition Ω) (a : upper.parts)
    {β : ℝ} (hβ : 0 < β) :
    mean (finsetIndicator
        (largeDefectBaseSupport fine coarse upper a β)) ≤
      (partitionAtomEnergy fine upper -
        partitionAtomEnergy coarse upper) / β := by
  apply (le_div_iff₀ hβ).2
  simpa [mul_comm] using
    mul_mean_indicator_largeDefectBaseSupport_le_atomEnergy_sub
      hfc upper a hβ.le

noncomputable def atomBadBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (α β : ℝ) :
    Finset Ω :=
  smallAverageBaseSupport coarse
      (partitionAtomIndicator upper a) α ∪
    largeDefectBaseSupport fine coarse upper a β

theorem mean_indicator_inter_union_le_add
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A B C : Finset Ω) :
    mean (finsetIndicator (A ∩ (B ∪ C))) ≤
      mean (finsetIndicator (A ∩ B)) +
        mean (finsetIndicator C) := by
  rw [← mean_add]
  apply mean_mono
  intro x
  by_cases hx : x ∈ A ∩ (B ∪ C)
  · rw [finsetIndicator_of_mem hx]
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).2 with hxB | hxC
    · have hxAB : x ∈ A ∩ B :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hxB⟩
      rw [finsetIndicator_of_mem hxAB]
      exact le_add_of_nonneg_right
        (by
          by_cases hxc : x ∈ C <;> simp [hxc])
    · rw [finsetIndicator_of_mem hxC]
      exact le_add_of_nonneg_left
        (by
          by_cases hxab : x ∈ A ∩ B <;> simp [hxab])
  · rw [finsetIndicator_of_not_mem hx]
    exact add_nonneg
      (by
        by_cases hxab : x ∈ A ∩ B <;> simp [hxab])
      (by
        by_cases hxc : x ∈ C <;> simp [hxc])

theorem mean_indicator_atom_inter_badBaseSupport_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {fine coarse : FacePartition Ω}
    (hfc : fine ≤ coarse)
    (upper : FacePartition Ω) (a : upper.parts)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (a.1 ∩ atomBadBaseSupport fine coarse upper a α β)) ≤
      α +
        (partitionAtomEnergy fine upper -
          partitionAtomEnergy coarse upper) / β := by
  calc
    mean (finsetIndicator
        (a.1 ∩ atomBadBaseSupport fine coarse upper a α β)) ≤
        mean (finsetIndicator
          (a.1 ∩ smallAverageBaseSupport coarse
            (partitionAtomIndicator upper a) α)) +
        mean (finsetIndicator
          (largeDefectBaseSupport fine coarse upper a β)) := by
      exact
        mean_indicator_inter_union_le_add
          a.1
          (smallAverageBaseSupport coarse
            (partitionAtomIndicator upper a) α)
          (largeDefectBaseSupport fine coarse upper a β)
    _ ≤
        α +
          (partitionAtomEnergy fine upper -
            partitionAtomEnergy coarse upper) / β :=
      add_le_add
        (mean_indicator_inter_smallAverageBaseSupport_le
          coarse a.1 hα)
        (mean_indicator_largeDefectBaseSupport_le_atomEnergy_sub_div
          hfc upper a hβ)

def orderedFaceAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k j) (x : Fin j → G) :
    (P e).parts :=
  partitionAtomAt (P e) x

@[simp]
theorem orderedFaceAtomAt_val
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k j) (x : Fin j → G) :
    (orderedFaceAtomAt P e x).1 = (P e).part x :=
  rfl

theorem orderedBoundaryAtomAt_eq_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x y : Fin (j + 1) → G) :
    orderedBoundaryAtomAt P e y =
        orderedBoundaryAtomAt P e x ↔
      ∀ i : Fin (j + 1),
        orderedFaceAtomAt P (eraseBoundaryFace e i)
            (eraseBoundaryCoordinate i y) =
          orderedFaceAtomAt P (eraseBoundaryFace e i)
            (eraseBoundaryCoordinate i x) := by
  rw [Subtype.ext_iff,
    orderedBoundaryAtomAt_val,
    orderedBoundaryAtomAt_val]
  constructor
  · intro h i
    apply Subtype.ext
    rw [orderedFaceAtomAt_val, orderedFaceAtomAt_val]
    have hmem :
        y ∈ (orderedBoundaryPartition P e).part x := by
      rw [← h]
      exact
        (orderedBoundaryPartition P e).mem_part
          (Finset.mem_univ y)
    exact
      (mem_orderedBoundaryPartition_part_iff_part_eq
        P e x y).1 hmem i
  · intro h
    apply
      (orderedBoundaryPartition P e).part_eq_of_mem
        ((orderedBoundaryPartition P e).part_mem.2
          (Finset.mem_univ x))
    apply
      (mem_orderedBoundaryPartition_part_iff_part_eq
        P e x y).2
    intro i
    exact congrArg Subtype.val (h i)

noncomputable def orderedAtomBoundaryDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (x : Fin (j + 1) → G) : ℝ :=
  atomBoundaryDefect
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper a x

noncomputable def orderedBoundaryAtomMass
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : (orderedBoundaryPartition coarse e).parts) : ℝ :=
  mean
    (partitionAtomIndicator
      (orderedBoundaryPartition coarse e) b)

noncomputable def orderedLocalizedAtomDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts)
    (b : (orderedBoundaryPartition coarse e).parts) : ℝ :=
  mean fun x =>
    orderedAtomBoundaryDefect fine coarse e upper a x ^ 2 *
      partitionAtomIndicator
        (orderedBoundaryPartition coarse e) b x

theorem orderedLocalizedAtomDefectSq_eq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts)
    (b : (orderedBoundaryPartition coarse e).parts) :
    orderedLocalizedAtomDefectSq fine coarse e upper a b =
      conditionalMean (orderedBoundaryPartition coarse e)
          (fun x =>
            orderedAtomBoundaryDefect
              fine coarse e upper a x ^ 2)
          ((orderedBoundaryPartition coarse e).representative b) *
        orderedBoundaryAtomMass coarse e b := by
  exact
    mean_mul_partitionAtomIndicator
      (orderedBoundaryPartition coarse e)
      (fun x =>
        orderedAtomBoundaryDefect fine coarse e upper a x ^ 2)
      b

theorem orderedLocalizedAtomDefectSq_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts)
    (b : (orderedBoundaryPartition coarse e).parts)
    {β : ℝ}
    (hβ :
      conditionalMean (orderedBoundaryPartition coarse e)
          (fun x =>
            orderedAtomBoundaryDefect
              fine coarse e upper a x ^ 2)
          ((orderedBoundaryPartition coarse e).representative b) ≤
        β) :
    orderedLocalizedAtomDefectSq fine coarse e upper a b ≤
      β * orderedBoundaryAtomMass coarse e b := by
  exact
    mean_mul_partitionAtomIndicator_le
      (orderedBoundaryPartition coarse e)
      (fun x =>
        orderedAtomBoundaryDefect fine coarse e upper a x ^ 2)
      b hβ

noncomputable def orderedLargeDefectBaseAtoms
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (β : ℝ) :
    Finset (orderedBoundaryPartition coarse e).parts :=
  largeDefectBaseAtoms
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper a β

noncomputable def orderedLargeDefectBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (β : ℝ) :
    Finset (Fin (j + 1) → G) :=
  largeDefectBaseSupport
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper a β

noncomputable def orderedAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (α β : ℝ) :
    Finset (Fin (j + 1) → G) :=
  atomBadBaseSupport
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    upper a α β

theorem mul_mean_indicator_orderedLargeDefectBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts)
    {β : ℝ} (hβ : 0 ≤ β) :
    β * mean (finsetIndicator
        (orderedLargeDefectBaseSupport
          fine coarse e upper a β)) ≤
      orderedAtomEnergy fine e upper -
        orderedAtomEnergy coarse e upper := by
  exact
    mul_mean_indicator_largeDefectBaseSupport_le_atomEnergy_sub
      (orderedBoundaryPartition_mono hfc e)
      upper a hβ

theorem mean_indicator_orderedAtom_inter_badBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (a.1 ∩ orderedAtomBadBaseSupport
          fine coarse e upper a α β)) ≤
      α +
        (orderedAtomEnergy fine e upper -
          orderedAtomEnergy coarse e upper) / β := by
  exact
    mean_indicator_atom_inter_badBaseSupport_le
      (orderedBoundaryPartition_mono hfc e)
      upper a hα hβ

def OrderedAtomIsGoodAtBoundary
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (x : Fin (j + 1) → G)
    (α β : ℝ) : Prop :=
  α ≤
      orderedBoundaryStructured coarse e
        (partitionAtomIndicator upper a) x ∧
    conditionalMean (orderedBoundaryPartition coarse e)
        (fun y => orderedAtomBoundaryDefect
          fine coarse e upper a y ^ 2) x ≤
      β

theorem orderedAtomIsGoodAtBoundary_of_not_mem_badBase
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (x : Fin (j + 1) → G)
    (α β : ℝ)
    (hx : x ∉ orderedAtomBadBaseSupport
      fine coarse e upper a α β) :
    OrderedAtomIsGoodAtBoundary
      fine coarse e upper a x α β := by
  have hlow :
      x ∉ smallAverageBaseSupport
        (orderedBoundaryPartition coarse e)
        (partitionAtomIndicator upper a) α := by
    intro h
    exact hx (Finset.mem_union_left _ h)
  have hdefect :
      x ∉ orderedLargeDefectBaseSupport
        fine coarse e upper a β := by
    intro h
    exact hx (Finset.mem_union_right _ h)
  constructor
  · exact not_lt.mp
      (fun h =>
        hlow
          ((mem_smallAverageBaseSupport
            (orderedBoundaryPartition coarse e)
            (partitionAtomIndicator upper a) α x).2 h))
  · exact not_lt.mp
      (fun h =>
        hdefect
          ((mem_largeDefectBaseSupport
            (orderedBoundaryPartition fine e)
            (orderedBoundaryPartition coarse e)
            upper a β x).2 h))

theorem OrderedAtomIsGoodAtBoundary.localized_defect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G))
    (a : upper.parts) (x : Fin (j + 1) → G)
    (α β : ℝ)
    (hgood :
      OrderedAtomIsGoodAtBoundary
        fine coarse e upper a x α β) :
    orderedLocalizedAtomDefectSq
        fine coarse e upper a
        (orderedBoundaryAtomAt coarse e x) ≤
      β *
        orderedBoundaryAtomMass coarse e
          (orderedBoundaryAtomAt coarse e x) := by
  apply orderedLocalizedAtomDefectSq_le
  have hrep :
      (orderedBoundaryPartition coarse e).representative
          (orderedBoundaryAtomAt coarse e x) ∈
        (orderedBoundaryPartition coarse e).part x := by
    exact
      (orderedBoundaryPartition coarse e).representative_mem
        (orderedBoundaryAtomAt coarse e x)
  have heq :=
    conditionalMean_eq_of_mem_part
      (orderedBoundaryPartition coarse e)
      (fun y =>
        orderedAtomBoundaryDefect
          fine coarse e upper a y ^ 2)
      hrep
  rw [heq]
  exact hgood.2

structure ClosedOrderedAtomConfiguration
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) (C : OrderedPartitionComplex G k r) where
  witness : Fin k → G
  atom :
    (j : Fin (r + 1)) →
      (e : OrderedFace k j.1) →
        (C.partition j e).parts
  mem_atom :
    ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
      orderedFaceTuple e witness ∈ (atom j e).1

namespace ClosedOrderedAtomConfiguration

def ofTuple
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (C : OrderedPartitionComplex G k r)
    (x : Fin k → G) :
    ClosedOrderedAtomConfiguration G k r C where
  witness := x
  atom j e :=
    partitionAtomAt (C.partition j e)
      (orderedFaceTuple e x)
  mem_atom j e :=
    (C.partition j e).mem_part
      (Finset.mem_univ (orderedFaceTuple e x))

theorem atom_eq_partitionAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (j : Fin (r + 1)) (e : OrderedFace k j.1) :
    A.atom j e =
      partitionAtomAt (C.partition j e)
        (orderedFaceTuple e A.witness) := by
  apply Subtype.ext
  exact
    ((C.partition j e).part_eq_of_mem
      (A.atom j e).2 (A.mem_atom j e)).symm

def IsGoodAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r fine)
    (j : ℕ) (hj : j < r)
    (e : OrderedFace k (j + 1))
    (α β : ℝ) : Prop :=
  OrderedAtomIsGoodAtBoundary
    (fine.layer j (Nat.le_of_lt hj))
    (coarse.layer j (Nat.le_of_lt hj))
    e
    (fine.partition
      ⟨j + 1, Nat.succ_lt_succ hj⟩ e)
    (A.atom ⟨j + 1, Nat.succ_lt_succ hj⟩ e)
    (orderedFaceTuple e A.witness)
    α β

def IsGood
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r fine)
    (α β : ℕ → ℝ) : Prop :=
  ∀ (j : ℕ) (hj : j < r) (e : OrderedFace k (j + 1)),
    A.IsGoodAt fine coarse j hj e (α (j + 1)) (β (j + 1))

theorem isGoodAt_of_not_mem_badBase
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r fine)
    (j : ℕ) (hj : j < r)
    (e : OrderedFace k (j + 1))
    (α β : ℝ)
    (havoid :
      orderedFaceTuple e A.witness ∉
        orderedAtomBadBaseSupport
          (fine.layer j (Nat.le_of_lt hj))
          (coarse.layer j (Nat.le_of_lt hj))
          e
          (fine.partition
            ⟨j + 1, Nat.succ_lt_succ hj⟩ e)
          (A.atom ⟨j + 1, Nat.succ_lt_succ hj⟩ e)
          α β) :
    A.IsGoodAt fine coarse j hj e α β :=
  orderedAtomIsGoodAtBoundary_of_not_mem_badBase
    (fine.layer j (Nat.le_of_lt hj))
    (coarse.layer j (Nat.le_of_lt hj))
    e
    (fine.partition
      ⟨j + 1, Nat.succ_lt_succ hj⟩ e)
    (A.atom ⟨j + 1, Nat.succ_lt_succ hj⟩ e)
    (orderedFaceTuple e A.witness)
    α β havoid

theorem isGood_of_avoids_badBases
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r fine)
    (α β : ℕ → ℝ)
    (havoid :
      ∀ (j : ℕ) (hj : j < r)
        (e : OrderedFace k (j + 1)),
        orderedFaceTuple e A.witness ∉
          orderedAtomBadBaseSupport
            (fine.layer j (Nat.le_of_lt hj))
            (coarse.layer j (Nat.le_of_lt hj))
            e
            (fine.partition
              ⟨j + 1, Nat.succ_lt_succ hj⟩ e)
            (A.atom ⟨j + 1, Nat.succ_lt_succ hj⟩ e)
            (α (j + 1)) (β (j + 1))) :
    A.IsGood fine coarse α β := by
  intro j hj e
  exact
    A.isGoodAt_of_not_mem_badBase
      fine coarse j hj e
      (α (j + 1)) (β (j + 1))
      (havoid j hj e)

end ClosedOrderedAtomConfiguration

end Erdos3.FixedDensity

end

end OAI

-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.FixedDensity.OrderedAtomEnergy
import OAI.Compat.Core

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev BoundaryBooleanCutAssignment
    (G : Type*) (j : ℕ) :=
  (i : Fin (j + 1)) → (Fin j → G) → Bool

noncomputable def boundaryBooleanComponentCut
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) :
    BooleanCutTest (Fin j → G) := by
  classical
  exact Finset.univ.filter fun z => b i z = true

@[simp]
theorem mem_boundaryBooleanComponentCut
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) (z : Fin j → G) :
    z ∈ boundaryBooleanComponentCut b i ↔
      b i z = true := by
  simp [boundaryBooleanComponentCut]

noncomputable def boundaryBooleanCutSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    BooleanCutTest (Fin (j + 1) → G) := by
  classical
  exact Finset.univ.filter fun x =>
    ∀ i, b i (eraseBoundaryCoordinate i x) = true

@[simp]
theorem mem_boundaryBooleanCutSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (x : Fin (j + 1) → G) :
    x ∈ boundaryBooleanCutSupport b ↔
      ∀ i, b i (eraseBoundaryCoordinate i x) = true := by
  simp [boundaryBooleanCutSupport]

noncomputable def orderedBoundaryComponentCuts
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (g : OrderedFace k j) :
    Finset (BooleanCutTest (Fin j → G)) := by
  classical
  exact
    ((Finset.univ : Finset (Fin (j + 1))).filter
      (fun i => eraseBoundaryFace e i = g)).image
      (fun i => boundaryBooleanComponentCut b i)

theorem boundaryBooleanComponentCut_mem_orderedBoundaryComponentCuts
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) :
    boundaryBooleanComponentCut b i ∈
      orderedBoundaryComponentCuts e b
        (eraseBoundaryFace e i) := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨i, ?_, rfl⟩
  simp

noncomputable def refineOrderedFacePartitionsByBoundaryCut
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
    OrderedFacePartitionSystem G k j :=
  fun g =>
    FacePartition.join (P g)
      (FacePartition.generatedBy
        (orderedBoundaryComponentCuts e b g))

theorem refineOrderedFacePartitionsByBoundaryCut_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
    OrderedFacePartitionRefines
      (refineOrderedFacePartitionsByBoundaryCut P e b) P := by
  intro g
  exact FacePartition.join_le_left _ _

theorem refineOrderedFacePartitionsByBoundaryCut_le_component
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) :
    refineOrderedFacePartitionsByBoundaryCut P e b
          (eraseBoundaryFace e i) ≤
      FacePartition.generatedBy
        ({boundaryBooleanComponentCut b i} :
          Finset (Finset (Fin j → G))) := by
  apply le_trans (FacePartition.join_le_right _ _)
  apply FacePartition.generatedBy_antitone
  intro A hA
  have hAeq : A = boundaryBooleanComponentCut b i := by
    simpa using hA
  subst A
  exact
    boundaryBooleanComponentCut_mem_orderedBoundaryComponentCuts
      e b i

theorem boundaryComponentBit_eq_of_mem_refined_part
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1))
    (x y : Fin j → G)
    (hy :
      y ∈
        (refineOrderedFacePartitionsByBoundaryCut P e b
          (eraseBoundaryFace e i)).part x) :
    b i x = b i y := by
  have hpart :
      y ∈
        (FacePartition.generatedBy
          ({boundaryBooleanComponentCut b i} :
            Finset (Finset (Fin j → G)))).part x :=
    FacePartition.part_subset_of_le
      (refineOrderedFacePartitionsByBoundaryCut_le_component
        P e b i) x hy
  have hsignature :=
    (FacePartition.mem_part_generatedBy_iff
      ({boundaryBooleanComponentCut b i} :
        Finset (Finset (Fin j → G))) x y).1 hpart
      (boundaryBooleanComponentCut b i) (by simp)
  cases hbx : b i x <;> cases hby : b i y <;>
    simp [mem_boundaryBooleanComponentCut, hbx, hby] at hsignature ⊢

theorem orderedBoundaryPartition_refined_le_generatedSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
    orderedBoundaryPartition
        (refineOrderedFacePartitionsByBoundaryCut P e b) e ≤
      FacePartition.generatedBy
        ({boundaryBooleanCutSupport b} :
          Finset (Finset (Fin (j + 1) → G))) := by
  rw [FacePartition.le_iff_part_subset]
  intro x y hy
  rw [FacePartition.mem_part_generatedBy_iff]
  intro A hA
  have hAeq : A = boundaryBooleanCutSupport b := by
    simpa using hA
  subst A
  rw [mem_boundaryBooleanCutSupport,
    mem_boundaryBooleanCutSupport]
  have hboundary :=
    (mem_orderedBoundaryPartition_part_iff
      (refineOrderedFacePartitionsByBoundaryCut P e b)
      e x y).1 hy
  constructor
  · intro hx i
    have hbit :=
      boundaryComponentBit_eq_of_mem_refined_part
        P e b i
        (eraseBoundaryCoordinate i x)
        (eraseBoundaryCoordinate i y)
        (hboundary i)
    exact hbit ▸ hx i
  · intro hy' i
    have hbit :=
      boundaryComponentBit_eq_of_mem_refined_part
        P e b i
        (eraseBoundaryCoordinate i x)
        (eraseBoundaryCoordinate i y)
        (hboundary i)
    exact hbit.symm ▸ hy' i

theorem orderedBoundaryPartition_refined_le_refineBy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j) :
      orderedBoundaryPartition
        (refineOrderedFacePartitionsByBoundaryCut P e b) e ≤
      ((⟨orderedBoundaryPartition P e⟩ :
          FaceRegularityState (Fin (j + 1) → G)).refineBy
        (boundaryBooleanCutSupport b)).partition := by
  apply FacePartition.le_join_iff.mpr
  constructor
  · exact orderedBoundaryPartition_mono
      (refineOrderedFacePartitionsByBoundaryCut_refines P e b) e
  · exact orderedBoundaryPartition_refined_le_generatedSupport
      P e b

noncomputable def orderedLayerAtomEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1)) : ℝ :=
  ∑ e : OrderedFace k (j + 1),
    orderedAtomEnergy lower e (upper e)

theorem orderedLayerAtomEnergy_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1)) :
    0 ≤ orderedLayerAtomEnergy lower upper := by
  unfold orderedLayerAtomEnergy
  exact Finset.sum_nonneg fun e _ =>
    orderedAtomEnergy_nonneg lower e (upper e)

theorem orderedLayerAtomEnergy_le_card
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1)) :
    orderedLayerAtomEnergy lower upper ≤
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) := by
  unfold orderedLayerAtomEnergy
  calc
    (∑ e : OrderedFace k (j + 1),
        orderedAtomEnergy lower e (upper e)) ≤
        ∑ _e : OrderedFace k (j + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      exact orderedAtomEnergy_le_one lower e (upper e)
    _ = (Fintype.card (OrderedFace k (j + 1)) : ℝ) := by
      simp

theorem orderedLayerAtomEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (upper : OrderedFacePartitionSystem G k (j + 1)) :
    orderedLayerAtomEnergy coarse upper ≤
      orderedLayerAtomEnergy fine upper := by
  unfold orderedLayerAtomEnergy
  apply Finset.sum_le_sum
  intro e _
  exact orderedAtomEnergy_mono hfc e (upper e)

theorem orderedLayerAtomEnergy_increment_of_boundaryCut
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (e : OrderedFace k (j + 1))
    (a : (upper e).parts)
    (b : BoundaryBooleanCutAssignment G j)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorrelation :
      ε ≤
        |FaceRegularityState.booleanCutCorrelation
          (⟨orderedBoundaryPartition lower e⟩ :
            FaceRegularityState (Fin (j + 1) → G))
            (partitionAtomIndicator (upper e) a)
            (boundaryBooleanCutSupport b)|) :
    orderedLayerAtomEnergy lower upper + ε ^ 2 ≤
      orderedLayerAtomEnergy
        (refineOrderedFacePartitionsByBoundaryCut lower e b)
        upper := by
  classical
  let fine :=
    refineOrderedFacePartitionsByBoundaryCut lower e b
  let S : FaceRegularityState (Fin (j + 1) → G) :=
    ⟨orderedBoundaryPartition lower e⟩
  have hincrement :
      S.energy (partitionAtomIndicator (upper e) a) + ε ^ 2 ≤
        (S.refineBy (boundaryBooleanCutSupport b)).energy
          (partitionAtomIndicator (upper e) a) :=
    S.energy_increment_of_booleanCut
      (partitionAtomIndicator (upper e) a)
      (boundaryBooleanCutSupport b) hε hcorrelation
  have hrefined :
      orderedBoundaryPartition fine e ≤
        (S.refineBy (boundaryBooleanCutSupport b)).partition := by
    exact orderedBoundaryPartition_refined_le_refineBy
      lower e b
  have hatom :
      orderedAtomEnergy lower e (upper e) + ε ^ 2 ≤
        orderedAtomEnergy fine e (upper e) := by
    unfold orderedAtomEnergy partitionAtomEnergy
    let U : Finset (upper e).parts := Finset.univ
    have haU : a ∈ U := by simp [U]
    have hother :
        ∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) c) ≤
          ∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) c) := by
      apply Finset.sum_le_sum
      intro c _
      exact partitionEnergy_mono
        (orderedBoundaryPartition fine e)
        (orderedBoundaryPartition lower e)
        (orderedBoundaryPartition_mono
          (refineOrderedFacePartitionsByBoundaryCut_refines
            lower e b) e)
        (partitionAtomIndicator (upper e) c)
    have hchosen :
        partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) a) +
            ε ^ 2 ≤
          partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) a) := by
      exact le_trans hincrement
        (partitionEnergy_mono
          (orderedBoundaryPartition fine e)
          (S.refineBy (boundaryBooleanCutSupport b)).partition
          hrefined
          (partitionAtomIndicator (upper e) a))
    change
      (∑ c ∈ U,
          partitionEnergy
            (orderedBoundaryPartition lower e)
            (partitionAtomIndicator (upper e) c)) +
          ε ^ 2 ≤
        ∑ c ∈ U,
          partitionEnergy
            (orderedBoundaryPartition fine e)
            (partitionAtomIndicator (upper e) c)
    calc
      (∑ c ∈ U,
          partitionEnergy
            (orderedBoundaryPartition lower e)
            (partitionAtomIndicator (upper e) c)) +
            ε ^ 2 =
          (∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) c)) +
            (partitionEnergy
              (orderedBoundaryPartition lower e)
              (partitionAtomIndicator (upper e) a) +
              ε ^ 2) := by
        rw [← Finset.sum_erase_add U _ haU]
        ring
      _ ≤
          (∑ c ∈ U.erase a,
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) c)) +
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) a) :=
        add_le_add hother hchosen
      _ =
          ∑ c ∈ U,
            partitionEnergy
              (orderedBoundaryPartition fine e)
              (partitionAtomIndicator (upper e) c) :=
        Finset.sum_erase_add U _ haU
  unfold orderedLayerAtomEnergy
  let E : Finset (OrderedFace k (j + 1)) := Finset.univ
  have heE : e ∈ E := by simp [E]
  have hotherFaces :
      ∑ d ∈ E.erase e,
          orderedAtomEnergy lower d (upper d) ≤
        ∑ d ∈ E.erase e,
          orderedAtomEnergy fine d (upper d) := by
    apply Finset.sum_le_sum
    intro d _
    exact orderedAtomEnergy_mono
      (refineOrderedFacePartitionsByBoundaryCut_refines
        lower e b)
      d (upper d)
  change
    (∑ d ∈ E, orderedAtomEnergy lower d (upper d)) +
        ε ^ 2 ≤
      ∑ d ∈ E, orderedAtomEnergy fine d (upper d)
  calc
    (∑ d ∈ E, orderedAtomEnergy lower d (upper d)) +
          ε ^ 2 =
        (∑ d ∈ E.erase e,
          orderedAtomEnergy lower d (upper d)) +
        (orderedAtomEnergy lower e (upper e) + ε ^ 2) := by
      rw [← Finset.sum_erase_add E _ heE]
      ring
    _ ≤
        (∑ d ∈ E.erase e,
          orderedAtomEnergy fine d (upper d)) +
        orderedAtomEnergy fine e (upper e) :=
      add_le_add hotherFaces hatom
    _ =
        ∑ d ∈ E, orderedAtomEnergy fine d (upper d) :=
      Finset.sum_erase_add E _ heE

def IsPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) : Prop :=
  ∀ (e : OrderedFace k (j + 1))
      (a : (upper e).parts)
      (b : BoundaryBooleanCutAssignment G j),
    |FaceRegularityState.booleanCutCorrelation
        (⟨orderedBoundaryPartition lower e⟩ :
          FaceRegularityState (Fin (j + 1) → G))
        (partitionAtomIndicator (upper e) a)
        (boundaryBooleanCutSupport b)| ≤ ε

theorem exists_boundaryCut_of_not_preliminaryRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ}
    (h : ¬IsPreliminaryOrderedRegular lower upper ε) :
    ∃ (e : OrderedFace k (j + 1))
        (a : (upper e).parts)
        (b : BoundaryBooleanCutAssignment G j),
      ε <
        |FaceRegularityState.booleanCutCorrelation
          (⟨orderedBoundaryPartition lower e⟩ :
            FaceRegularityState (Fin (j + 1) → G))
          (partitionAtomIndicator (upper e) a)
          (boundaryBooleanCutSupport b)| := by
  unfold IsPreliminaryOrderedRegular at h
  obtain ⟨e, he⟩ := not_forall.mp h
  obtain ⟨a, ha⟩ := not_forall.mp he
  obtain ⟨b, hb⟩ := not_forall.mp ha
  exact ⟨e, a, b, lt_of_not_ge hb⟩

structure PreliminaryIrregularWitness
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) where
  face : OrderedFace k (j + 1)
  atom : (upper face).parts
  cut : BoundaryBooleanCutAssignment G j
  correlation :
    ε <
      |FaceRegularityState.booleanCutCorrelation
        (⟨orderedBoundaryPartition lower face⟩ :
          FaceRegularityState (Fin (j + 1) → G))
        (partitionAtomIndicator (upper face) atom)
        (boundaryBooleanCutSupport cut)|

noncomputable def chosenPreliminaryIrregularWitness
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ)
    (h : ¬IsPreliminaryOrderedRegular lower upper ε) :
    PreliminaryIrregularWitness lower upper ε := by
  classical
  let hex :=
    exists_boundaryCut_of_not_preliminaryRegular
      lower upper h
  let e := Classical.choose hex
  let he := Classical.choose_spec hex
  let a := Classical.choose he
  let ha := Classical.choose_spec he
  let b := Classical.choose ha
  have hcorr := Classical.choose_spec ha
  exact ⟨e, a, b, hcorr⟩

noncomputable def preliminaryOrderedRegularityStep
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    OrderedFacePartitionSystem G k j := by
  classical
  exact
    if h : IsPreliminaryOrderedRegular lower upper ε then
      lower
    else
      let W :=
        chosenPreliminaryIrregularWitness lower upper ε h
      refineOrderedFacePartitionsByBoundaryCut
        lower W.face W.cut

theorem preliminaryOrderedRegularityStep_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    OrderedFacePartitionRefines
      (preliminaryOrderedRegularityStep lower upper ε)
      lower := by
  classical
  by_cases h :
      IsPreliminaryOrderedRegular lower upper ε
  · simpa [preliminaryOrderedRegularityStep, h] using
      OrderedFacePartitionRefines.refl lower
  · simp only [preliminaryOrderedRegularityStep, dite_eq_right h]
    let W :=
      chosenPreliminaryIrregularWitness lower upper ε h
    exact refineOrderedFacePartitionsByBoundaryCut_refines
      lower W.face W.cut

theorem preliminaryOrderedRegularityStep_energy_increment
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : ¬IsPreliminaryOrderedRegular lower upper ε) :
    orderedLayerAtomEnergy lower upper + ε ^ 2 ≤
      orderedLayerAtomEnergy
        (preliminaryOrderedRegularityStep lower upper ε)
        upper := by
  classical
  simp only [preliminaryOrderedRegularityStep, dite_eq_right h]
  let W :=
    chosenPreliminaryIrregularWitness lower upper ε h
  exact orderedLayerAtomEnergy_increment_of_boundaryCut
    lower upper W.face W.atom W.cut hε
    (le_of_lt W.correlation)

noncomputable def preliminaryOrderedRegularityRun
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    ℕ → OrderedFacePartitionSystem G k j
  | 0 => lower
  | n + 1 =>
      preliminaryOrderedRegularityStep
        (preliminaryOrderedRegularityRun lower upper ε n)
        upper ε

@[simp]
theorem preliminaryOrderedRegularityRun_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) :
    preliminaryOrderedRegularityRun lower upper ε 0 =
      lower :=
  rfl

@[simp]
theorem preliminaryOrderedRegularityRun_succ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (n : ℕ) :
    preliminaryOrderedRegularityRun lower upper ε (n + 1) =
      preliminaryOrderedRegularityStep
        (preliminaryOrderedRegularityRun lower upper ε n)
        upper ε :=
  rfl

theorem preliminaryOrderedRegularityRun_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (n : ℕ) :
    OrderedFacePartitionRefines
      (preliminaryOrderedRegularityRun lower upper ε n)
      lower := by
  induction n with
  | zero =>
      exact OrderedFacePartitionRefines.refl lower
  | succ n ih =>
      exact OrderedFacePartitionRefines.trans
        (preliminaryOrderedRegularityStep_refines
          (preliminaryOrderedRegularityRun lower upper ε n)
          upper ε)
        ih

theorem exists_preliminaryOrderedRegularityRun_index_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ, n < m ∧
      IsPreliminaryOrderedRegular
        (preliminaryOrderedRegularityRun
          lower upper ε n)
        upper ε := by
  by_contra hregular
  have hnotregular :
      ∀ n, n < m →
        ¬IsPreliminaryOrderedRegular
          (preliminaryOrderedRegularityRun
            lower upper ε n)
          upper ε := by
    intro n hn hreg
    exact hregular ⟨n, hn, hreg⟩
  have hgain :
      ∀ n, n < m →
        orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε n)
            upper +
            ε ^ 2 ≤
          orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε (n + 1))
            upper := by
    intro n hn
    rw [preliminaryOrderedRegularityRun_succ]
    exact preliminaryOrderedRegularityStep_energy_increment
      (preliminaryOrderedRegularityRun
        lower upper ε n)
      upper hε (hnotregular n hn)
  have growth :
      ∀ n : ℕ,
        (∀ i, i < n →
          orderedLayerAtomEnergy
              (preliminaryOrderedRegularityRun
                lower upper ε i)
              upper +
              ε ^ 2 ≤
            orderedLayerAtomEnergy
              (preliminaryOrderedRegularityRun
                lower upper ε (i + 1))
              upper) →
        orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε 0)
            upper +
            (n : ℝ) * ε ^ 2 ≤
          orderedLayerAtomEnergy
            (preliminaryOrderedRegularityRun
              lower upper ε n)
            upper := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have hprevious :=
          ih (fun i hi =>
            hn i (Nat.lt_trans hi (Nat.lt_succ_self n)))
        have hstep := hn n (Nat.lt_succ_self n)
        calc
          orderedLayerAtomEnergy
                (preliminaryOrderedRegularityRun
                  lower upper ε 0)
                upper +
                (↑(Nat.succ n) : ℝ) * ε ^ 2 =
              (orderedLayerAtomEnergy
                  (preliminaryOrderedRegularityRun
                    lower upper ε 0)
                  upper +
                (n : ℝ) * ε ^ 2) +
                ε ^ 2 := by
            push_cast
            ring
          _ ≤
              orderedLayerAtomEnergy
                  (preliminaryOrderedRegularityRun
                    lower upper ε n)
                  upper +
                ε ^ 2 := by
            linarith
          _ ≤
              orderedLayerAtomEnergy
                (preliminaryOrderedRegularityRun
                  lower upper ε (n + 1))
                upper :=
            hstep
  have hgrowth := growth m hgain
  have hnonneg :
      0 ≤
        orderedLayerAtomEnergy
          (preliminaryOrderedRegularityRun
            lower upper ε 0)
          upper :=
    orderedLayerAtomEnergy_nonneg _ _
  have hupper :
      orderedLayerAtomEnergy
          (preliminaryOrderedRegularityRun
            lower upper ε m)
          upper ≤
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) :=
    orderedLayerAtomEnergy_le_card _ _
  linarith

theorem exists_preliminaryOrderedRegular_refinement_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ,
      ∃ fine : OrderedFacePartitionSystem G k j,
        n < m ∧
        OrderedFacePartitionRefines fine lower ∧
        IsPreliminaryOrderedRegular fine upper ε := by
  obtain ⟨n, hn, hregular⟩ :=
    exists_preliminaryOrderedRegularityRun_index_before
      lower upper hε hlong
  exact
    ⟨n,
      preliminaryOrderedRegularityRun lower upper ε n,
      hn,
      preliminaryOrderedRegularityRun_refines
        lower upper ε n,
      hregular⟩

theorem card_orderedBoundaryComponentCuts_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (g : OrderedFace k j) :
    (orderedBoundaryComponentCuts e b g).card ≤
      j + 1 := by
  classical
  let I : Finset (Fin (j + 1)) :=
    (Finset.univ : Finset (Fin (j + 1))).filter
      (fun i => eraseBoundaryFace e i = g)
  calc
    (orderedBoundaryComponentCuts e b g).card ≤
        I.card := by
      exact Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin (j + 1))).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = j + 1 := by simp

theorem complexity_refineOrderedFacePartitionsByBoundaryCut_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : BoundaryBooleanCutAssignment G j)
    (g : OrderedFace k j) :
    FacePartition.complexity
        (refineOrderedFacePartitionsByBoundaryCut P e b g) ≤
      2 ^ (j + 1) *
        FacePartition.complexity (P g) := by
  have hgenerated :
      FacePartition.complexity
          (FacePartition.generatedBy
            (orderedBoundaryComponentCuts e b g)) ≤
        2 ^ (j + 1) := by
    exact le_trans
      (FacePartition.complexity_generatedBy_le
        (orderedBoundaryComponentCuts e b g))
      (Nat.pow_le_pow_right (by decide)
        (card_orderedBoundaryComponentCuts_le e b g))
  calc
    FacePartition.complexity
        (refineOrderedFacePartitionsByBoundaryCut P e b g) ≤
        FacePartition.complexity (P g) *
          FacePartition.complexity
            (FacePartition.generatedBy
              (orderedBoundaryComponentCuts e b g)) :=
      FacePartition.complexity_join_le _ _
    _ ≤
        FacePartition.complexity (P g) *
          2 ^ (j + 1) :=
      Nat.mul_le_mul_left _ hgenerated
    _ =
        2 ^ (j + 1) *
          FacePartition.complexity (P g) :=
      Nat.mul_comm _ _

theorem complexity_preliminaryOrderedRegularityStep_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (g : OrderedFace k j) :
    FacePartition.complexity
        (preliminaryOrderedRegularityStep
          lower upper ε g) ≤
      2 ^ (j + 1) *
        FacePartition.complexity (lower g) := by
  classical
  by_cases h :
      IsPreliminaryOrderedRegular lower upper ε
  · simp only [preliminaryOrderedRegularityStep, dite_eq_left h]
    exact Nat.le_mul_of_pos_left _
      (by positivity : 0 < 2 ^ (j + 1))
  · simp only [preliminaryOrderedRegularityStep, dite_eq_right h]
    let W :=
      chosenPreliminaryIrregularWitness lower upper ε h
    exact
      complexity_refineOrderedFacePartitionsByBoundaryCut_le
        lower W.face W.cut g

theorem complexity_preliminaryOrderedRegularityRun_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (n : ℕ) (g : OrderedFace k j) :
    FacePartition.complexity
        (preliminaryOrderedRegularityRun
          lower upper ε n g) ≤
      (2 ^ (j + 1)) ^ n *
        FacePartition.complexity (lower g) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        FacePartition.complexity
            (preliminaryOrderedRegularityRun
              lower upper ε (n + 1) g) ≤
            2 ^ (j + 1) *
              FacePartition.complexity
                (preliminaryOrderedRegularityRun
                  lower upper ε n g) := by
          rw [preliminaryOrderedRegularityRun_succ]
          exact complexity_preliminaryOrderedRegularityStep_le
            (preliminaryOrderedRegularityRun
              lower upper ε n)
            upper ε g
        _ ≤
            2 ^ (j + 1) *
              ((2 ^ (j + 1)) ^ n *
                FacePartition.complexity (lower g)) :=
          Nat.mul_le_mul_left _ ih
        _ =
            (2 ^ (j + 1)) ^ (n + 1) *
              FacePartition.complexity (lower g) := by
          rw [pow_succ]
          ring

theorem exists_preliminaryOrderedRegular_refinement_with_complexity_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ,
      ∃ fine : OrderedFacePartitionSystem G k j,
        n < m ∧
        OrderedFacePartitionRefines fine lower ∧
        IsPreliminaryOrderedRegular fine upper ε ∧
        ∀ g,
          FacePartition.complexity (fine g) ≤
            (2 ^ (j + 1)) ^ n *
              FacePartition.complexity (lower g) := by
  obtain ⟨n, hn, hregular⟩ :=
    exists_preliminaryOrderedRegularityRun_index_before
      lower upper hε hlong
  exact
    ⟨n,
      preliminaryOrderedRegularityRun lower upper ε n,
      hn,
      preliminaryOrderedRegularityRun_refines
        lower upper ε n,
      hregular,
      complexity_preliminaryOrderedRegularityRun_le
        lower upper ε n⟩

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def boundaryBooleanAssignmentOfBoolean
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    BoundaryBooleanCutAssignment G j :=
  fun i z => b ⟨i, z⟩

def booleanAssignmentOfBoundary
    {G : Type*} {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    BooleanCutAssignment G (j + 1) :=
  fun q => b q.1 q.2

@[simp]
theorem booleanAssignmentOfBoundary_ofBoolean
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    booleanAssignmentOfBoundary
        (boundaryBooleanAssignmentOfBoolean b) = b := by
  funext q
  cases q
  rfl

@[simp]
theorem boundaryBooleanAssignmentOfBoolean_ofBoundary
    {G : Type*} {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    boundaryBooleanAssignmentOfBoolean
        (booleanAssignmentOfBoundary b) = b := by
  funext i z
  rfl

def booleanBoundaryAssignmentEquiv
    (G : Type*) (j : ℕ) :
    BooleanCutAssignment G (j + 1) ≃
      BoundaryBooleanCutAssignment G j where
  toFun := boundaryBooleanAssignmentOfBoolean
  invFun := booleanAssignmentOfBoundary
  left_inv := booleanAssignmentOfBoundary_ofBoolean
  right_inv := boundaryBooleanAssignmentOfBoolean_ofBoundary

@[simp]
theorem booleanAssignmentOfBoundary_equiv_apply
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    booleanAssignmentOfBoundary
        ((booleanBoundaryAssignmentEquiv G j) b) = b :=
  booleanAssignmentOfBoundary_ofBoolean b

def boundaryBernoulliWeight
    {G : Type*} [Fintype G] {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (b : BoundaryBooleanCutAssignment G j) : ℝ :=
  bernoulliAssignmentWeight
    (cutTestCoordinateValue u)
    (booleanAssignmentOfBoundary b)

theorem sum_boundaryBernoulliWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (u : CutTestFamily G (j + 1)) :
    ∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b = 1 := by
  classical
  calc
    (∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b) =
        ∑ b : BooleanCutAssignment G (j + 1),
          bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b := by
      symm
      exact
        Fintype.sum_equiv
          (booleanBoundaryAssignmentEquiv G j)
          (fun b : BooleanCutAssignment G (j + 1) =>
            bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b)
          (fun b : BoundaryBooleanCutAssignment G j =>
            boundaryBernoulliWeight u b)
          (fun b => by simp [boundaryBernoulliWeight])
    _ = 1 :=
      sum_bernoulliAssignmentWeight
        (cutTestCoordinateValue u)

theorem boundaryBernoulliWeight_nonneg
    {G : Type*} [Fintype G]
    {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (hu : IsBoundedCutTest u)
    (b : BoundaryBooleanCutAssignment G j) :
    0 ≤ boundaryBernoulliWeight u b := by
  exact
    bernoulliAssignmentWeight_nonneg
      (p := cutTestCoordinateValue u)
      (fun q => hu.nonneg q.1 q.2)
      (fun q => hu.le_one q.1 q.2)
      (booleanAssignmentOfBoundary b)

theorem boundaryBooleanComponentCut_eval
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (i : Fin (j + 1)) (z : Fin j → G) :
    (boundaryBooleanComponentCut b i).eval z =
      booleanValue (booleanAssignmentOfBoundary b) ⟨i, z⟩ := by
  classical
  by_cases h : b i z = true
  · have hz : z ∈ boundaryBooleanComponentCut b i := by
      rw [mem_boundaryBooleanComponentCut]
      exact h
    rw [BooleanCutTest.eval_of_mem _ hz]
    simp [booleanValue, booleanAssignmentOfBoundary, h]
  · have hz : z ∉ boundaryBooleanComponentCut b i := by
      rw [mem_boundaryBooleanComponentCut]
      exact h
    rw [BooleanCutTest.eval_of_not_mem _ hz]
    simp [booleanValue, booleanAssignmentOfBoundary, h]

theorem eraseBoundaryCoordinate_eq_eraseCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    eraseBoundaryCoordinate i x = eraseCoordinate i x :=
  rfl

theorem boundaryBooleanCutSupport_eq_booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    boundaryBooleanCutSupport b =
      booleanFaceCutSupport (booleanAssignmentOfBoundary b) := by
  classical
  ext x
  rw [mem_boundaryBooleanCutSupport,
    mem_booleanFaceCutSupport]
  simp only [booleanAssignmentOfBoundary,
    eraseBoundaryCoordinate_eq_eraseCoordinate]

theorem boundaryBooleanCutSupport_eval
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j)
    (x : Fin (j + 1) → G) :
    (boundaryBooleanCutSupport b).eval x =
      cutTestProduct
        (cutTestFamilyOfBooleanAssignment
          (booleanAssignmentOfBoundary b)) x := by
  rw [boundaryBooleanCutSupport_eq_booleanFaceCutSupport,
    booleanFaceCutSupport_eval]

theorem boundaryFactor_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (i : Fin (j + 1)) (z : Fin j → G) :
    u i z =
      ∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b *
          (boundaryBooleanComponentCut b i).eval z := by
  classical
  have hmoment :
      (∑ b : BooleanCutAssignment G (j + 1),
          bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            booleanValue b ⟨i, z⟩) =
        u i z := by
    simpa [cutTestCoordinateValue] using
      (sum_bernoulliAssignmentWeight_mul_selected
        (cutTestCoordinateValue u)
        ({⟨i, z⟩} :
          Finset (CutTestCoordinate G (j + 1))))
  rw [← hmoment]
  exact
    Fintype.sum_equiv
      (booleanBoundaryAssignmentEquiv G j)
      (fun b : BooleanCutAssignment G (j + 1) =>
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          booleanValue b ⟨i, z⟩)
      (fun b : BoundaryBooleanCutAssignment G j =>
        boundaryBernoulliWeight u b *
          (boundaryBooleanComponentCut b i).eval z)
      (fun b => by
        simp [boundaryBernoulliWeight,
          boundaryBooleanComponentCut_eval])

theorem boundaryCutProduct_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (x : Fin (j + 1) → G) :
    cutTestProduct u x =
      ∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b *
          (boundaryBooleanCutSupport b).eval x := by
  classical
  rw [cutTestProduct_eq_sum_boolean]
  exact
    Fintype.sum_equiv
      (booleanBoundaryAssignmentEquiv G j)
      (fun b : BooleanCutAssignment G (j + 1) =>
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutTestProduct
            (cutTestFamilyOfBooleanAssignment b) x)
      (fun b : BoundaryBooleanCutAssignment G j =>
        boundaryBernoulliWeight u b *
          (boundaryBooleanCutSupport b).eval x)
      (fun b => by
        simp [boundaryBernoulliWeight,
          boundaryBooleanCutSupport_eval])

namespace FaceRegularityState

theorem faceCutCorrelation_eq_sum_boundaryBoolean
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (S : FaceRegularityState (Fin (j + 1) → G))
    (f : (Fin (j + 1) → G) → ℝ)
    (u : CutTestFamily G (j + 1)) :
    S.faceCutCorrelation f u =
      ∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b) := by
  classical
  rw [S.faceCutCorrelation_eq_sum_boolean]
  exact
    Fintype.sum_equiv
      (booleanBoundaryAssignmentEquiv G j)
      (fun b : BooleanCutAssignment G (j + 1) =>
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          S.faceCutCorrelation f
            (cutTestFamilyOfBooleanAssignment b))
      (fun b : BoundaryBooleanCutAssignment G j =>
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b))
      (fun b => by
        rw [S.faceCutCorrelation_boolean]
        simp [boundaryBernoulliWeight,
          boundaryBooleanCutSupport_eq_booleanFaceCutSupport])

theorem abs_faceCutCorrelation_le_of_boundaryBoolean
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (S : FaceRegularityState (Fin (j + 1) → G))
    (f : (Fin (j + 1) → G) → ℝ)
    {ε : ℝ}
    (u : CutTestFamily G (j + 1))
    (hu : IsBoundedCutTest u)
    (hboolean :
      ∀ b : BoundaryBooleanCutAssignment G j,
        |S.booleanCutCorrelation f
          (boundaryBooleanCutSupport b)| ≤ ε) :
    |S.faceCutCorrelation f u| ≤ ε := by
  rw [S.faceCutCorrelation_eq_sum_boundaryBoolean]
  calc
    |∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b)| ≤
        ∑ b : BoundaryBooleanCutAssignment G j,
          |boundaryBernoulliWeight u b *
            S.booleanCutCorrelation f
              (boundaryBooleanCutSupport b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ b : BoundaryBooleanCutAssignment G j,
          boundaryBernoulliWeight u b * ε := by
      apply Finset.sum_le_sum
      intro b _
      have hw : 0 ≤ boundaryBernoulliWeight u b :=
        boundaryBernoulliWeight_nonneg u hu b
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hboolean b) hw
    _ = ε := by
      rw [← Finset.sum_mul,
        sum_boundaryBernoulliWeight, one_mul]

end FaceRegularityState

def IsPreliminaryOrderedBoundedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) : Prop :=
  ∀ (e : OrderedFace k (j + 1))
      (a : (upper e).parts),
    (⟨orderedBoundaryPartition lower e⟩ :
      FaceRegularityState (Fin (j + 1) → G)).IsFaceCutRegular
        (partitionAtomIndicator (upper e) a) ε

theorem IsPreliminaryOrderedRegular.toBounded
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {lower : OrderedFacePartitionSystem G k j}
    {upper : OrderedFacePartitionSystem G k (j + 1)}
    {ε : ℝ}
    (hregular :
      IsPreliminaryOrderedRegular lower upper ε) :
    IsPreliminaryOrderedBoundedRegular
      lower upper ε := by
  intro e a u hu
  exact
    FaceRegularityState.abs_faceCutCorrelation_le_of_boundaryBoolean
      (⟨orderedBoundaryPartition lower e⟩ :
        FaceRegularityState (Fin (j + 1) → G))
      (partitionAtomIndicator (upper e) a)
      u hu (fun b => hregular e a b)

end Erdos3.FixedDensity

end

end OAI

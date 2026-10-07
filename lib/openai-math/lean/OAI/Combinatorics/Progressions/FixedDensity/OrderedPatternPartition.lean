import OAI.Combinatorics.Progressions.FixedDensity.BoundaryBernoulli
import OAI.Combinatorics.Progressions.FixedDensity.OrderedGoodAtoms

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedPartitionComplex

def topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) :
    OrderedFacePartitionSystem G k r :=
  C.partition (Fin.last r)

def dropTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1)) :
    OrderedPartitionComplex G k r where
  partition j := C.partition j.castSucc

def appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    OrderedPartitionComplex G k (r + 1) where
  partition j :=
    Fin.lastCases top (fun i => C.partition i) j

def withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    OrderedPartitionComplex G k r where
  partition j :=
    Fin.lastCases top (fun i => C.partition i.castSucc) j

@[simp]
theorem topLayer_appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).topLayer = top := by
  simp [topLayer, appendTop]

@[simp]
theorem dropTop_appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).dropTop = C := by
  cases C with
  | mk partition =>
      simp [dropTop, appendTop]

@[simp]
theorem topLayer_withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    (withTopLayer C top).topLayer = top := by
  simp [topLayer, withTopLayer]

@[simp]
theorem withTopLayer_partition_castSucc
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1))
    (top : OrderedFacePartitionSystem G k (r + 1))
    (j : Fin (r + 1)) :
    (withTopLayer C top).partition j.castSucc =
      C.partition j.castSucc := by
  simp [withTopLayer]

@[simp]
theorem appendTop_partition_castSucc
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1))
    (j : Fin (r + 1)) :
    (appendTop C top).partition j.castSucc =
      C.partition j := by
  simp [appendTop]

@[simp]
theorem appendTop_partition_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).partition (Fin.last (r + 1)) =
      top := by
  simp [appendTop]

@[simp]
theorem withTopLayer_partition_castSucc_general
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r)
    (i : Fin r) :
    (withTopLayer C top).partition i.castSucc =
      C.partition i.castSucc := by
  simp [withTopLayer]

@[simp]
theorem appendTop_dropTop_topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1)) :
    appendTop C.dropTop C.topLayer = C := by
  cases C with
  | mk partition =>
      simp only [dropTop, topLayer, appendTop]
      congr 1
      funext j e
      cases j using Fin.lastCases <;>
        simp only [Fin.lastCases_last,
          Fin.lastCases_castSucc]

theorem dropTop_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k (r + 1)}
    (hfc : fine.Refines coarse) :
    fine.dropTop.Refines coarse.dropTop := by
  intro j e
  exact hfc j.castSucc e

theorem appendTop_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    {fineTop coarseTop :
      OrderedFacePartitionSystem G k (r + 1)}
    (hfc : fine.Refines coarse)
    (htop : OrderedFacePartitionRefines fineTop coarseTop) :
    (appendTop fine fineTop).Refines
      (appendTop coarse coarseTop) := by
  intro j e
  cases j using Fin.lastCases with
  | last =>
      simp only [appendTop, Fin.lastCases_last]
      change OrderedFace k (r + 1) at e
      change fineTop e ≤ coarseTop e
      exact htop e
  | cast i =>
      simp only [appendTop, Fin.lastCases_castSucc]
      change OrderedFace k i.1 at e
      change fine.partition i e ≤ coarse.partition i e
      exact hfc i e

theorem withTopLayer_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r)
    (htop : OrderedFacePartitionRefines top C.topLayer) :
    (withTopLayer C top).Refines C := by
  intro j e
  cases j using Fin.lastCases with
  | last =>
      simp only [withTopLayer, Fin.lastCases_last]
      change OrderedFace k r at e
      change top e ≤ C.partition (Fin.last r) e
      exact htop e
  | cast i =>
      simp only [withTopLayer, Fin.lastCases_castSucc]
      exact le_rfl

end OrderedPartitionComplex

structure OrderedCoarseFineComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse

namespace OrderedCoarseFineComplex

theorem boundaryRefines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r j : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (hj : j < r)
    (e : OrderedFace k (j + 1)) :
    P.fine.boundary hj e ≤ P.coarse.boundary hj e :=
  OrderedPartitionComplex.boundary_mono P.refines hj e

noncomputable def faceAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) : ℝ :=
  orderedAtomEnergy
      (P.fine.partition j.castSucc) e
      (P.fine.partition j.succ e) -
    orderedAtomEnergy
      (P.coarse.partition j.castSucc) e
      (P.fine.partition j.succ e)

theorem faceAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    0 ≤ P.faceAtomEnergyGap j e := by
  apply sub_nonneg.mpr
  exact orderedAtomEnergy_mono
    (fun f => P.refines j.castSucc f)
    e (P.fine.partition j.succ e)

noncomputable def layerAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) : ℝ :=
  orderedLayerAtomEnergy
      (P.fine.partition j.castSucc)
      (P.fine.partition j.succ) -
    orderedLayerAtomEnergy
      (P.coarse.partition j.castSucc)
      (P.fine.partition j.succ)

theorem layerAtomEnergyGap_eq_sum_face
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) :
    P.layerAtomEnergyGap j =
      ∑ e : OrderedFace k (j.1 + 1),
        P.faceAtomEnergyGap j e := by
  unfold layerAtomEnergyGap faceAtomEnergyGap
    orderedLayerAtomEnergy
  rw [Finset.sum_sub_distrib]
  rfl

theorem layerAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) :
    0 ≤ P.layerAtomEnergyGap j := by
  apply sub_nonneg.mpr
  exact orderedLayerAtomEnergy_mono
    (fun e => P.refines j.castSucc e)
    (P.fine.partition j.succ)

theorem layerAtomEnergyGap_le_card
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) :
    P.layerAtomEnergyGap j ≤
      (Fintype.card (OrderedFace k (j.1 + 1)) : ℝ) := by
  have hfine :=
    orderedLayerAtomEnergy_le_card
      (P.fine.partition j.castSucc)
      (P.fine.partition j.succ)
  have hcoarse :=
    orderedLayerAtomEnergy_nonneg
      (P.coarse.partition j.castSucc)
      (P.fine.partition j.succ)
  have hfine' :
      orderedLayerAtomEnergy
          (P.fine.partition j.castSucc)
          (P.fine.partition j.succ) ≤
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) := by
    convert hfine using 1
    rfl
  unfold layerAtomEnergyGap
  linarith

noncomputable def totalAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) : ℝ :=
  ∑ j : Fin r, P.layerAtomEnergyGap j

theorem totalAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) :
    0 ≤ P.totalAtomEnergyGap := by
  exact Finset.sum_nonneg fun j _ =>
    P.layerAtomEnergyGap_nonneg j

theorem faceAtomEnergyGap_le_layer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    P.faceAtomEnergyGap j e ≤
      P.layerAtomEnergyGap j := by
  rw [P.layerAtomEnergyGap_eq_sum_face j]
  exact Finset.single_le_sum
    (fun f _ => P.faceAtomEnergyGap_nonneg j f)
    (Finset.mem_univ e)

theorem layerAtomEnergyGap_le_total
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) :
    P.layerAtomEnergyGap j ≤
      P.totalAtomEnergyGap := by
  unfold totalAtomEnergyGap
  exact Finset.single_le_sum
    (fun i _ => P.layerAtomEnergyGap_nonneg i)
    (Finset.mem_univ j)

theorem faceAtomEnergyGap_le_total
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    P.faceAtomEnergyGap j e ≤
      P.totalAtomEnergyGap :=
  (P.faceAtomEnergyGap_le_layer j e).trans
    (P.layerAtomEnergyGap_le_total j)

theorem totalAtomEnergyGap_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) :
    P.totalAtomEnergyGap ≤
      ∑ j : Fin r,
        (Fintype.card (OrderedFace k (j.1 + 1)) : ℝ) := by
  exact Finset.sum_le_sum fun j _ =>
    P.layerAtomEnergyGap_le_card j

end OrderedCoarseFineComplex

abbrev OrderedRegularityTolerance (r : ℕ) := Fin r → ℝ

abbrev OrderedRegularityBudget (r : ℕ) := Fin r → ℕ

abbrev OrderedRegularityStepSchedule (r : ℕ) := Fin r → ℕ

def IsFullyPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r) : Prop :=
  ∀ j : Fin r,
    IsPreliminaryOrderedRegular
      (C.partition j.castSucc)
      (C.partition j.succ)
      (ε j)

def IsOrderedRegularityBudget
    (k r : ℕ)
    (ε : OrderedRegularityTolerance r)
    (m : OrderedRegularityBudget r) : Prop :=
  ∀ j : Fin r,
    (Fintype.card (OrderedFace k (j.1 + 1)) : ℝ) <
      (m j : ℝ) * (ε j) ^ 2

def HasOrderedRegularityComplexityBound
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r)
    (steps : OrderedRegularityStepSchedule r) : Prop :=
  ∀ (j : Fin r) (e : OrderedFace k j.1),
    FacePartition.complexity
        (fine.partition j.castSucc e) ≤
      (2 ^ (j.1 + 1)) ^ (steps j) *
        FacePartition.complexity
          (coarse.partition j.castSucc e)

structure FullOrderedRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (coarse : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r)
    (m : OrderedRegularityBudget r) where
  steps : OrderedRegularityStepSchedule r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  topLayer_eq :
    fine.topLayer = coarse.topLayer
  steps_lt : ∀ j, steps j < m j
  regular :
    IsFullyPreliminaryOrderedRegular fine ε
  complexity :
    HasOrderedRegularityComplexityBound
      fine coarse steps

theorem exists_fullOrderedRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r)
    (m : OrderedRegularityBudget r)
    (hε : ∀ j, 0 ≤ ε j)
    (hbudget : IsOrderedRegularityBudget k r ε m) :
    Nonempty (FullOrderedRegularityCertificate C ε m) := by
  induction r with
  | zero =>
      let steps : OrderedRegularityStepSchedule 0 :=
        fun j => Fin.elim0 j
      refine ⟨{
        steps := steps
        fine := C
        refines := OrderedPartitionComplex.Refines.refl C
        topLayer_eq := rfl
        steps_lt := ?_
        regular := ?_
        complexity := ?_ }⟩
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
  | succ r ih =>
      let lowerComplex : OrderedPartitionComplex G k r :=
        C.dropTop
      let upper : OrderedFacePartitionSystem G k (r + 1) :=
        C.topLayer
      have hεtop : 0 ≤ ε (Fin.last r) :=
        hε (Fin.last r)
      have hbudgetTop :
          (Fintype.card (OrderedFace k (r + 1)) : ℝ) <
            (m (Fin.last r) : ℝ) *
              (ε (Fin.last r)) ^ 2 := by
        have hb := hbudget (Fin.last r)
        change
          (Fintype.card (OrderedFace k (r + 1)) : ℝ) <
            (m (Fin.last r) : ℝ) *
              (ε (Fin.last r)) ^ 2 at hb
        exact hb
      obtain ⟨n, lower, hn, hlowerRefines,
          hlowerRegular, hlowerComplexity⟩ :=
        exists_preliminaryOrderedRegular_refinement_with_complexity_before
          lowerComplex.topLayer upper hεtop hbudgetTop
      let prepared : OrderedPartitionComplex G k r :=
        lowerComplex.withTopLayer lower
      have hpreparedRefines :
          prepared.Refines lowerComplex := by
        exact OrderedPartitionComplex.withTopLayer_refines
          lowerComplex lower hlowerRefines
      let εlower : OrderedRegularityTolerance r :=
        fun j => ε j.castSucc
      let mlower : OrderedRegularityBudget r :=
        fun j => m j.castSucc
      have hεlower : ∀ j, 0 ≤ εlower j := by
        intro j
        exact hε j.castSucc
      have hbudgetLower :
          IsOrderedRegularityBudget k r εlower mlower := by
        intro j
        exact hbudget j.castSucc
      obtain ⟨lowerCertificate⟩ :=
        ih prepared εlower mlower hεlower hbudgetLower
      let fine : OrderedPartitionComplex G k (r + 1) :=
        lowerCertificate.fine.appendTop upper
      let steps : OrderedRegularityStepSchedule (r + 1) :=
        fun j =>
          Fin.lastCases n lowerCertificate.steps j
      have hlowerCertificateTop :
          lowerCertificate.fine.topLayer = lower := by
        calc
          lowerCertificate.fine.topLayer =
              prepared.topLayer :=
            lowerCertificate.topLayer_eq
          _ = lower :=
            OrderedPartitionComplex.topLayer_withTopLayer
              lowerComplex lower
      refine ⟨{
        steps := steps
        fine := fine
        refines := ?_
        topLayer_eq := ?_
        steps_lt := ?_
        regular := ?_
        complexity := ?_ }⟩
      · have hprefixFinal :
            lowerCertificate.fine.Refines lowerComplex :=
          OrderedPartitionComplex.Refines.trans
            lowerCertificate.refines hpreparedRefines
        have happended :
            fine.Refines
              (lowerComplex.appendTop upper) := by
          exact OrderedPartitionComplex.appendTop_refines
            hprefixFinal
            (OrderedFacePartitionRefines.refl upper)
        simpa [fine, lowerComplex, upper] using happended
      · simp [fine, upper]
      · intro j
        cases j using Fin.lastCases with
        | last =>
            simpa [steps] using hn
        | cast i =>
            simpa [steps] using
              lowerCertificate.steps_lt i
      · intro j
        cases j using Fin.lastCases with
        | last =>
            have htop :
                IsPreliminaryOrderedRegular
                  lowerCertificate.fine.topLayer
                  upper (ε (Fin.last r)) := by
              rw [hlowerCertificateTop]
              exact hlowerRegular
            simp only [fine,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              Fin.succ_last]
            change
              @IsPreliminaryOrderedRegular
                G _ _ k r
                (lowerCertificate.fine.partition
                  (Fin.last r))
                upper (ε (Fin.last r))
            exact htop
        | cast i =>
            have hi := lowerCertificate.regular i
            simp only [fine, εlower,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              Fin.succ_castSucc]
            change
              @IsPreliminaryOrderedRegular
                G _ _ k i.1
                (lowerCertificate.fine.partition i.castSucc)
                (lowerCertificate.fine.partition i.succ)
                (ε i.castSucc)
            exact hi
      · intro j
        cases j using Fin.lastCases with
        | last =>
            intro e
            have htop :
                FacePartition.complexity
                    (lowerCertificate.fine.topLayer e) ≤
                  (2 ^ (r + 1)) ^ n *
                    FacePartition.complexity
                      (lowerComplex.topLayer e) := by
              rw [hlowerCertificateTop]
              exact hlowerComplexity e
            simp only [fine, steps,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              Fin.lastCases_last]
            change OrderedFace k r at e
            change
              FacePartition.complexity
                  (lowerCertificate.fine.partition
                    (Fin.last r) e) ≤
                (2 ^ (r + 1)) ^ n *
                  FacePartition.complexity
                    (C.partition
                      (Fin.last r).castSucc e)
            exact htop
        | cast i =>
            intro e
            change OrderedFace k i.1 at e
            have hi := lowerCertificate.complexity i e
            simp only [prepared, lowerComplex,
              OrderedPartitionComplex.withTopLayer,
              OrderedPartitionComplex.dropTop,
              Fin.lastCases_castSucc] at hi
            simp only [fine, steps, εlower, mlower,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              Fin.lastCases_castSucc]
            change
              FacePartition.complexity
                  (lowerCertificate.fine.partition
                    i.castSucc e) ≤
                (2 ^ (i.1 + 1)) ^
                    lowerCertificate.steps i *
                  FacePartition.complexity
                    (C.partition
                      i.castSucc.castSucc e)
            exact hi

theorem exists_fullyPreliminaryOrderedRegular_refinement
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r)
    (m : OrderedRegularityBudget r)
    (hε : ∀ j, 0 ≤ ε j)
    (hbudget : IsOrderedRegularityBudget k r ε m) :
    ∃ (steps : OrderedRegularityStepSchedule r)
        (fine : OrderedPartitionComplex G k r),
      fine.Refines C ∧
      fine.topLayer = C.topLayer ∧
      (∀ j, steps j < m j) ∧
      IsFullyPreliminaryOrderedRegular fine ε ∧
      HasOrderedRegularityComplexityBound
        fine C steps := by
  obtain ⟨certificate⟩ :=
    exists_fullOrderedRegularityCertificate
      C ε m hε hbudget
  exact ⟨certificate.steps, certificate.fine,
    certificate.refines, certificate.topLayer_eq,
    certificate.steps_lt, certificate.regular,
    certificate.complexity⟩

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

noncomputable def OrderedPattern.edgeFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    (e : OrderedFace k r) : Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter (H.edge e)

@[simp]
theorem OrderedPattern.mem_edgeFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    (e : OrderedFace k r) (y : Fin r → G) :
    y ∈ H.edgeFinset e ↔ H.edge e y := by
  simp [OrderedPattern.edgeFinset]

noncomputable def orderedPatternTopPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    OrderedFacePartitionSystem G k r := by
  classical
  exact fun e =>
    FacePartition.generatedBy ({H.edgeFinset e} :
      Finset (Finset (Fin r → G)))

theorem complexity_orderedPatternTopPartition_le_two
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    (e : OrderedFace k r) :
    FacePartition.complexity
        (orderedPatternTopPartition H e) ≤ 2 := by
  simpa [orderedPatternTopPartition] using
    FacePartition.complexity_generatedBy_le
      ({H.edgeFinset e} :
        Finset (Finset (Fin r → G)))

theorem mem_of_mem_part_of_le_generatedBy_singleton
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P : FacePartition Ω} {S : Finset Ω}
    (hP : P ≤ FacePartition.generatedBy
      ({S} : Finset (Finset Ω)))
    {x y : Ω} (hx : x ∈ S) (hy : y ∈ P.part x) :
    y ∈ S := by
  have hyGenerated :
      y ∈
        (FacePartition.generatedBy
          ({S} : Finset (Finset Ω))).part x :=
    FacePartition.part_subset_of_le hP x hy
  have hsignature :=
    (FacePartition.mem_part_generatedBy_iff
      ({S} : Finset (Finset Ω)) x y).1 hyGenerated
  exact (hsignature S (by simp)).1 hx

theorem orderedPattern_edge_of_mem_refinedTopAtom
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {P : OrderedFacePartitionSystem G k r}
    (hP : OrderedFacePartitionRefines P
      (orderedPatternTopPartition H))
    (e : OrderedFace k r) {x y : Fin r → G}
    (hx : H.edge e x) (hy : y ∈ (P e).part x) :
    H.edge e y := by
  rw [← H.mem_edgeFinset e y]
  exact
    mem_of_mem_part_of_le_generatedBy_singleton
      (hP e)
      ((H.mem_edgeFinset e x).2 hx) hy

def indiscreteOrderedPartitionComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) : OrderedPartitionComplex G k r where
  partition _ _ := FacePartition.indiscrete

noncomputable def orderedPatternInitialComplex
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    OrderedPartitionComplex G k r :=
  (indiscreteOrderedPartitionComplex G k r).withTopLayer
    (orderedPatternTopPartition H)

@[simp]
theorem orderedPatternInitialComplex_topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    (orderedPatternInitialComplex H).topLayer =
      orderedPatternTopPartition H := by
  exact OrderedPartitionComplex.topLayer_withTopLayer _ _

theorem orderedPatternTopPartition_refines_of_complex_refines_initial
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {C : OrderedPartitionComplex G k r}
    (hC : C.Refines (orderedPatternInitialComplex H)) :
    OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H) := by
  intro e
  change
    C.partition (Fin.last r) e ≤
      orderedPatternTopPartition H e
  rw [← orderedPatternInitialComplex_topLayer H]
  exact hC (Fin.last r) e

theorem ClosedOrderedAtomConfiguration.edge_of_mem_topAtom
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {C : OrderedPartitionComplex G k r}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k r C)
    (hA : H.IsOccurrence A.witness)
    (e : OrderedFace k r) (y : Fin r → G)
    (hy : y ∈ (A.atom (Fin.last r) e).1) :
    H.edge e y := by
  apply
    orderedPattern_edge_of_mem_refinedTopAtom
      H hC e (hA e)
  have hw :
      orderedFaceTuple e A.witness ∈
        (A.atom (Fin.last r) e).1 :=
    A.mem_atom (Fin.last r) e
  have hpart :
      (C.topLayer e).part
          (orderedFaceTuple e A.witness) =
        (A.atom (Fin.last r) e).1 := by
    exact
      (C.topLayer e).part_eq_of_mem
        (A.atom (Fin.last r) e).2 hw
  rwa [hpart]

theorem ClosedOrderedAtomConfiguration.isOccurrence_of_mem_topAtoms
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {C : OrderedPartitionComplex G k r}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k r C)
    (hA : H.IsOccurrence A.witness)
    (x : Fin k → G)
    (hx :
      ∀ e : OrderedFace k r,
        orderedFaceTuple e x ∈
          (A.atom (Fin.last r) e).1) :
    H.IsOccurrence x := by
  intro e
  exact A.edge_of_mem_topAtom H hC hA e
    (orderedFaceTuple e x) (hx e)

end Erdos3.FixedDensity

end

end OAI

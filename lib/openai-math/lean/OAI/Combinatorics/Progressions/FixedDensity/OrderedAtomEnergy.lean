-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.FixedDensity.OrderedBoundaryPartition
import OAI.Compat.Core

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω ι : Type*}
  [Fintype Ω] [DecidableEq Ω]

namespace FaceRegularityState

noncomputable def familyEnergy [Fintype ι]
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ) : ℝ :=
  ∑ i, S.energy (f i)

def IsFamilyRegularAgainst
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) : Prop :=
  ∀ i, S.IsRegularAgainst (f i) cuts ε

theorem familyEnergy_nonneg [Fintype ι]
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ) :
    0 ≤ S.familyEnergy f := by
  unfold familyEnergy
  exact Finset.sum_nonneg fun i _ =>
    partitionEnergy_nonneg S.partition (f i)

theorem familyEnergy_le_card [Fintype ι] [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (hf0 : ∀ i x, 0 ≤ f i x)
    (hf1 : ∀ i x, f i x ≤ 1) :
    S.familyEnergy f ≤ (Fintype.card ι : ℝ) := by
  unfold familyEnergy
  calc
    (∑ i, S.energy (f i)) ≤ ∑ _i : ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact partitionEnergy_le_one S.partition
        (hf0 i) (hf1 i)
    _ = (Fintype.card ι : ℝ) := by simp

theorem familyEnergy_mono [Fintype ι]
    (S T : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (hTS : T.partition ≤ S.partition) :
    S.familyEnergy f ≤ T.familyEnergy f := by
  unfold familyEnergy
  apply Finset.sum_le_sum
  intro i _
  exact partitionEnergy_mono T.partition S.partition
    hTS (f i)

theorem familyEnergy_refineBy_increment [Fintype ι]
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (i : ι) (A : BooleanCutTest Ω) {ε : ℝ}
    (hgain :
      S.energy (f i) + ε ^ 2 ≤
        (S.refineBy A).energy (f i)) :
    S.familyEnergy f + ε ^ 2 ≤
      (S.refineBy A).familyEnergy f := by
  classical
  let U : Finset ι := Finset.univ
  have hiU : i ∈ U := by simp [U]
  have hother :
      ∑ j ∈ U.erase i, S.energy (f j) ≤
        ∑ j ∈ U.erase i, (S.refineBy A).energy (f j) := by
    apply Finset.sum_le_sum
    intro j _
    exact partitionEnergy_mono
      (S.refineBy A).partition S.partition
      (S.refineBy_le A) (f j)
  unfold familyEnergy
  change
    (∑ j ∈ U, S.energy (f j)) + ε ^ 2 ≤
      ∑ j ∈ U, (S.refineBy A).energy (f j)
  calc
    (∑ j ∈ U, S.energy (f j)) + ε ^ 2 =
        (∑ j ∈ U.erase i, S.energy (f j)) +
          (S.energy (f i) + ε ^ 2) := by
      rw [← Finset.sum_erase_add U
        (fun j => S.energy (f j)) hiU]
      ring
    _ ≤
        (∑ j ∈ U.erase i, (S.refineBy A).energy (f j)) +
          (S.refineBy A).energy (f i) :=
      add_le_add hother hgain
    _ = ∑ j ∈ U, (S.refineBy A).energy (f j) := by
      exact Finset.sum_erase_add U
        (fun j => (S.refineBy A).energy (f j)) hiU

theorem exists_index_booleanCut_of_not_familyRegular
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) {ε : ℝ}
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    ∃ i : ι, ∃ A ∈ cuts,
      ε < |S.booleanCutCorrelation (f i) A| := by
  classical
  unfold IsFamilyRegularAgainst at h
  obtain ⟨i, hi⟩ := not_forall.mp h
  obtain ⟨A, hA, hcorr⟩ :=
    S.exists_booleanCut_of_not_regular (f i) cuts hi
  exact ⟨i, A, hA, hcorr⟩

structure FamilyIrregularWitness
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) where
  index : ι
  cut : BooleanCutTest Ω
  mem_cuts : cut ∈ cuts
  correlation :
    ε < |S.booleanCutCorrelation (f index) cut|

noncomputable def chosenFamilyIrregularWitness
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    S.FamilyIrregularWitness f cuts ε := by
  classical
  let hex :=
    S.exists_index_booleanCut_of_not_familyRegular f cuts h
  let i : ι := Classical.choose hex
  let hi := Classical.choose_spec hex
  let A : BooleanCutTest Ω := Classical.choose hi
  have hA :=
    (Classical.choose_spec hi).1
  have hcorr :=
    (Classical.choose_spec hi).2
  exact ⟨i, A, hA, hcorr⟩

noncomputable def chosenFamilyIrregularCut
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    BooleanCutTest Ω := by
  classical
  exact
    if h : S.IsFamilyRegularAgainst f cuts ε then ∅
    else (S.chosenFamilyIrregularWitness f cuts ε h).cut

theorem chosenFamilyIrregularCut_mem
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    S.chosenFamilyIrregularCut f cuts ε ∈ cuts := by
  simp only [chosenFamilyIrregularCut, dite_eq_right h]
  exact
    (S.chosenFamilyIrregularWitness f cuts ε h).mem_cuts

theorem exists_chosenFamilyIrregularCut_correlation
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    ∃ i : ι,
      ε <
        |S.booleanCutCorrelation (f i)
          (S.chosenFamilyIrregularCut f cuts ε)| := by
  let W := S.chosenFamilyIrregularWitness f cuts ε h
  refine ⟨W.index, ?_⟩
  simp only [chosenFamilyIrregularCut, dite_eq_right h]
  exact W.correlation

theorem familyEnergy_increment_chosenFamilyCut [Fintype ι] [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) {ε : ℝ}
    (hε : 0 ≤ ε)
    (h : ¬S.IsFamilyRegularAgainst f cuts ε) :
    S.familyEnergy f + ε ^ 2 ≤
      (S.refineBy
        (S.chosenFamilyIrregularCut f cuts ε)).familyEnergy f := by
  obtain ⟨i, hcorr⟩ :=
    S.exists_chosenFamilyIrregularCut_correlation f cuts ε h
  apply S.familyEnergy_refineBy_increment f i
  exact S.energy_increment_of_booleanCut
    (f i) (S.chosenFamilyIrregularCut f cuts ε)
    hε (le_of_lt hcorr)

noncomputable def familyRegularityRun
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    ℕ → FaceRegularityState Ω
  | 0 => S
  | n + 1 =>
      let T := familyRegularityRun S f cuts ε n
      T.refineBy (T.chosenFamilyIrregularCut f cuts ε)

@[simp]
theorem familyRegularityRun_zero
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.familyRegularityRun f cuts ε 0 = S :=
  rfl

@[simp]
theorem familyRegularityRun_succ
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    S.familyRegularityRun f cuts ε (n + 1) =
      (S.familyRegularityRun f cuts ε n).refineBy
        ((S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
          f cuts ε) :=
  rfl

theorem familyRegularityRun_partition_le
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    (S.familyRegularityRun f cuts ε n).partition ≤
      S.partition := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      exact le_trans
        ((S.familyRegularityRun f cuts ε n).refineBy_le
          ((S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
            f cuts ε))
        ih

theorem familyRegularityRun_complexity_le
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    FacePartition.complexity
        (S.familyRegularityRun f cuts ε n).partition ≤
      2 ^ n * FacePartition.complexity S.partition := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        FacePartition.complexity
            (S.familyRegularityRun f cuts ε (n + 1)).partition ≤
            2 * FacePartition.complexity
              (S.familyRegularityRun f cuts ε n).partition := by
          rw [familyRegularityRun_succ]
          exact
            (S.familyRegularityRun f cuts ε n).complexity_refineBy_le
              ((S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
                f cuts ε)
        _ ≤ 2 * (2 ^ n *
              FacePartition.complexity S.partition) :=
          Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) *
              FacePartition.complexity S.partition := by
          rw [pow_succ]
          ring

noncomputable def familyRegularityRunCuts
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    Finset (BooleanCutTest Ω) := by
  classical
  exact (Finset.range n).image fun i =>
    (S.familyRegularityRun f cuts ε i).chosenFamilyIrregularCut
      f cuts ε

@[simp]
theorem familyRegularityRunCuts_zero
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.familyRegularityRunCuts f cuts ε 0 = ∅ := by
  simp [familyRegularityRunCuts]

@[simp]
theorem familyRegularityRunCuts_succ
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    S.familyRegularityRunCuts f cuts ε (n + 1) =
      insert
        ((S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
          f cuts ε)
        (S.familyRegularityRunCuts f cuts ε n) := by
  classical
  simp [familyRegularityRunCuts, Finset.range_add_one]

theorem chosenFamilyIrregularCut_mem_of_empty_mem
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (hempty : (∅ : BooleanCutTest Ω) ∈ cuts) :
    S.chosenFamilyIrregularCut f cuts ε ∈ cuts := by
  by_cases hregular :
      S.IsFamilyRegularAgainst f cuts ε
  · simpa [chosenFamilyIrregularCut, hregular] using hempty
  · exact S.chosenFamilyIrregularCut_mem f cuts ε hregular

theorem familyRegularityRunCuts_subset
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (hempty : (∅ : BooleanCutTest Ω) ∈ cuts) (n : ℕ) :
    S.familyRegularityRunCuts f cuts ε n ⊆ cuts := by
  classical
  intro A hA
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
  exact chosenFamilyIrregularCut_mem_of_empty_mem
    (S.familyRegularityRun f cuts ε i) f cuts ε hempty

theorem familyRegularityRun_partition_eq_join_generatedBy
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) (n : ℕ) :
    (S.familyRegularityRun f cuts ε n).partition =
      FacePartition.join S.partition
        (FacePartition.generatedBy
          (S.familyRegularityRunCuts f cuts ε n)) := by
  induction n with
  | zero =>
      rw [familyRegularityRun_zero, familyRegularityRunCuts_zero,
        FacePartition.generatedBy_empty]
      change S.partition = S.partition ⊓ ⊤
      exact (inf_top_eq S.partition).symm
  | succ n ih =>
      let A : BooleanCutTest Ω :=
        (S.familyRegularityRun f cuts ε n).chosenFamilyIrregularCut
          f cuts ε
      calc
        (S.familyRegularityRun f cuts ε (n + 1)).partition =
            FacePartition.join
              (S.familyRegularityRun f cuts ε n).partition
              (FacePartition.generatedBy
                ({A} : Finset (Finset Ω))) := by
          rfl
        _ =
            FacePartition.join
              (FacePartition.join S.partition
                (FacePartition.generatedBy
                  (S.familyRegularityRunCuts f cuts ε n)))
              (FacePartition.generatedBy
                ({A} : Finset (Finset Ω))) := by
          rw [ih]
        _ =
            FacePartition.join S.partition
              (FacePartition.join
                (FacePartition.generatedBy
                  (S.familyRegularityRunCuts f cuts ε n))
                (FacePartition.generatedBy
                  ({A} : Finset (Finset Ω)))) := by
          exact inf_assoc _ _ _
        _ =
            FacePartition.join S.partition
              (FacePartition.generatedBy
                (insert A
                  (S.familyRegularityRunCuts f cuts ε n))) := by
          rw [FacePartition.generatedBy_insert]
        _ =
            FacePartition.join S.partition
              (FacePartition.generatedBy
                (S.familyRegularityRunCuts f cuts ε (n + 1))) := by
          rw [familyRegularityRunCuts_succ]

theorem exists_familyRegular_run_index_before [Fintype ι] [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω))
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ i x, 0 ≤ f i x)
    (hf1 : ∀ i x, f i x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card ι : ℝ) < (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ, n < m ∧
      (S.familyRegularityRun f cuts ε n).IsFamilyRegularAgainst
        f cuts ε := by
  by_contra hregular
  have hnotregular :
      ∀ n, n < m →
        ¬(S.familyRegularityRun f cuts ε n).IsFamilyRegularAgainst
          f cuts ε := by
    intro n hn hreg
    exact hregular ⟨n, hn, hreg⟩
  have hgain :
      ∀ n, n < m →
        (S.familyRegularityRun f cuts ε n).familyEnergy f +
            ε ^ 2 ≤
          (S.familyRegularityRun f cuts ε (n + 1)).familyEnergy
            f := by
    intro n hn
    rw [familyRegularityRun_succ]
    exact
      familyEnergy_increment_chosenFamilyCut
        (S.familyRegularityRun f cuts ε n)
        f cuts hε (hnotregular n hn)
  have growth :
      ∀ n : ℕ,
        (∀ i, i < n →
          (S.familyRegularityRun f cuts ε i).familyEnergy f +
              ε ^ 2 ≤
            (S.familyRegularityRun f cuts ε (i + 1)).familyEnergy f) →
          (S.familyRegularityRun f cuts ε 0).familyEnergy f +
              (n : ℝ) * ε ^ 2 ≤
            (S.familyRegularityRun f cuts ε n).familyEnergy f := by
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
          (S.familyRegularityRun f cuts ε 0).familyEnergy f +
                (↑(Nat.succ n) : ℝ) * ε ^ 2 =
              ((S.familyRegularityRun f cuts ε 0).familyEnergy f +
                (n : ℝ) * ε ^ 2) + ε ^ 2 := by
            push_cast
            ring
          _ ≤
              (S.familyRegularityRun f cuts ε n).familyEnergy f +
                ε ^ 2 := by linarith
          _ ≤
              (S.familyRegularityRun f cuts ε (n + 1)).familyEnergy
                f := hstep
  have hgrowth := growth m hgain
  have hnonneg :
      0 ≤ (S.familyRegularityRun f cuts ε 0).familyEnergy f :=
    (S.familyRegularityRun f cuts ε 0).familyEnergy_nonneg f
  have hupper :
      (S.familyRegularityRun f cuts ε m).familyEnergy f ≤
        (Fintype.card ι : ℝ) :=
    (S.familyRegularityRun f cuts ε m).familyEnergy_le_card
      f hf0 hf1
  linarith

theorem exists_familyRegular_refinement_with_generators_before [Fintype ι] [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : ι → Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω))
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ i x, 0 ≤ f i x)
    (hf1 : ∀ i x, f i x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card ι : ℝ) < (m : ℝ) * ε ^ 2)
    (hempty : (∅ : BooleanCutTest Ω) ∈ cuts) :
    ∃ n : ℕ, ∃ T : FaceRegularityState Ω,
      ∃ F : Finset (BooleanCutTest Ω),
        n < m ∧
        T.partition =
          FacePartition.join S.partition
            (FacePartition.generatedBy F) ∧
        F ⊆ cuts ∧
        F.card ≤ n ∧
        T.IsFamilyRegularAgainst f cuts ε ∧
        FacePartition.complexity T.partition ≤
          2 ^ n * FacePartition.complexity S.partition := by
  obtain ⟨n, hn, hregular⟩ :=
    S.exists_familyRegular_run_index_before f cuts
      hf0 hf1 hε hlong
  let T := S.familyRegularityRun f cuts ε n
  let F := S.familyRegularityRunCuts f cuts ε n
  refine ⟨n, T, F, hn, ?_, ?_, ?_, hregular, ?_⟩
  · exact S.familyRegularityRun_partition_eq_join_generatedBy
      f cuts ε n
  · exact S.familyRegularityRunCuts_subset f cuts ε hempty n
  · unfold F familyRegularityRunCuts
    exact Finset.card_image_le.trans_eq (Finset.card_range n)
  · exact S.familyRegularityRun_complexity_le f cuts ε n

def IsFaceCutRegularFamily
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : ι → (Fin r → G) → ℝ) (ε : ℝ) : Prop :=
  ∀ i, S.IsFaceCutRegular (f i) ε

theorem isFaceCutRegularFamily_of_familyRegularAgainst_supports
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : ι → (Fin r → G) → ℝ) {ε : ℝ}
    (hregular :
      S.IsFamilyRegularAgainst f
        (booleanFaceCutSupports G r) ε) :
    S.IsFaceCutRegularFamily f ε := by
  intro i
  exact S.isFaceCutRegular_of_regularAgainst_supports
    (f i) (hregular i)

theorem exists_faceCutRegularFamily_refinement_with_generators_before [Fintype ι]
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r : ℕ} (hr : 0 < r)
    (S : FaceRegularityState (Fin r → G))
    (f : ι → (Fin r → G) → ℝ)
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ i x, 0 ≤ f i x)
    (hf1 : ∀ i x, f i x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card ι : ℝ) < (m : ℝ) * ε ^ 2) :
    ∃ n : ℕ,
      ∃ T : FaceRegularityState (Fin r → G),
      ∃ F : Finset (BooleanCutTest (Fin r → G)),
        n < m ∧
        T.partition =
          FacePartition.join S.partition
            (FacePartition.generatedBy F) ∧
        F ⊆ booleanFaceCutSupports G r ∧
        F.card ≤ n ∧
        T.IsFaceCutRegularFamily f ε ∧
        FacePartition.complexity T.partition ≤
          2 ^ n * FacePartition.complexity S.partition := by
  obtain ⟨n, T, F, hn, hpart, hsubset, hcard,
      hregular, hcomplexity⟩ :=
    S.exists_familyRegular_refinement_with_generators_before
      f (booleanFaceCutSupports G r)
      hf0 hf1 hε hlong
      (empty_mem_booleanFaceCutSupports hr)
  exact
    ⟨n, T, F, hn, hpart, hsubset, hcard,
      T.isFaceCutRegularFamily_of_familyRegularAgainst_supports
        f hregular,
      hcomplexity⟩

end FaceRegularityState

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) :
    Ω → ℝ :=
  finsetIndicator a.1

@[simp]
theorem partitionAtomIndicator_of_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) {x : Ω}
    (hx : x ∈ a.1) :
    partitionAtomIndicator Q a x = 1 :=
  finsetIndicator_of_mem hx

@[simp]
theorem partitionAtomIndicator_of_not_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) {x : Ω}
    (hx : x ∉ a.1) :
    partitionAtomIndicator Q a x = 0 :=
  finsetIndicator_of_not_mem hx

theorem partitionAtomIndicator_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    0 ≤ partitionAtomIndicator Q a x := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

theorem partitionAtomIndicator_le_one
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    partitionAtomIndicator Q a x ≤ 1 := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

theorem partitionAtomIndicator_sq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    partitionAtomIndicator Q a x ^ 2 =
      partitionAtomIndicator Q a x := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

theorem sum_partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (x : Ω) :
    ∑ a : Q.parts, partitionAtomIndicator Q a x = 1 := by
  classical
  let ax : Q.parts :=
    ⟨Q.part x, Q.part_mem.2 (Finset.mem_univ x)⟩
  rw [Finset.sum_eq_single ax]
  · exact partitionAtomIndicator_of_mem Q ax
      (Q.mem_part (Finset.mem_univ x))
  · intro b _hb hba
    apply partitionAtomIndicator_of_not_mem
    intro hxb
    have heq :
        b = ax := by
      apply Subtype.ext
      exact Q.eq_of_mem_parts b.2 ax.2 hxb
        (Q.mem_part (Finset.mem_univ x))
    exact hba heq
  · intro hax
    exact (hax (Finset.mem_univ ax)).elim

theorem conditionalMean_fintype_sum
    {Ω κ : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype κ]
    (P : FacePartition Ω) (f : κ → Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => ∑ i : κ, f i y) x =
      ∑ i : κ, conditionalMean P (f i) x := by
  unfold conditionalMean
  exact Finset.expect_sum_comm
    (P.part x) (Finset.univ : Finset κ)
    (fun y i => f i y)

theorem sum_conditionalMean_partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FacePartition Ω) (x : Ω) :
    ∑ a : Q.parts,
        conditionalMean P (partitionAtomIndicator Q a) x =
      1 := by
  rw [← conditionalMean_fintype_sum]
  convert conditionalMean_const P 1 x using 2
  funext y
  exact sum_partitionAtomIndicator Q y

noncomputable def partitionAtomEnergy
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FacePartition Ω) : ℝ :=
  ∑ a : Q.parts,
    Erdos3.FixedDensity.partitionEnergy P
      (partitionAtomIndicator Q a)

theorem partitionAtomEnergy_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : FacePartition Ω) :
    0 ≤ partitionAtomEnergy P Q := by
  unfold partitionAtomEnergy
  exact Finset.sum_nonneg fun a _ =>
    Erdos3.FixedDensity.partitionEnergy_nonneg P
      (partitionAtomIndicator Q a)

theorem partitionAtomEnergy_le_one
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P Q : FacePartition Ω) :
    partitionAtomEnergy P Q ≤ 1 := by
  unfold partitionAtomEnergy
  calc
    (∑ a : Q.parts,
        Erdos3.FixedDensity.partitionEnergy P
          (partitionAtomIndicator Q a)) ≤
        ∑ a : Q.parts,
          mean (fun x =>
            partitionAtomIndicator Q a x ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      exact partitionEnergy_le_mean_sq P
        (partitionAtomIndicator Q a)
    _ =
        ∑ a : Q.parts,
          mean (partitionAtomIndicator Q a) := by
      apply Finset.sum_congr rfl
      intro a _
      apply congrArg mean
      funext x
      exact partitionAtomIndicator_sq Q a x
    _ =
        mean (fun x =>
          ∑ a : Q.parts, partitionAtomIndicator Q a x) := by
      unfold mean
      exact
        (Finset.expect_sum_comm
          (Finset.univ : Finset Ω)
          (Finset.univ : Finset Q.parts)
          (fun x a => partitionAtomIndicator Q a x)).symm
    _ = mean (fun _x : Ω => (1 : ℝ)) := by
      apply congrArg mean
      funext x
      exact sum_partitionAtomIndicator Q x
    _ = 1 := mean_const 1

theorem partitionAtomEnergy_mono
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P R : FacePartition Ω} (hPR : P ≤ R)
    (Q : FacePartition Ω) :
    partitionAtomEnergy R Q ≤ partitionAtomEnergy P Q := by
  unfold partitionAtomEnergy
  apply Finset.sum_le_sum
  intro a _
  exact partitionEnergy_mono P R hPR
    (partitionAtomIndicator Q a)

theorem partitionAtomEnergy_sub_eq_sum_mean_sq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P R : FacePartition Ω} (hPR : P ≤ R)
    (Q : FacePartition Ω) :
    partitionAtomEnergy P Q - partitionAtomEnergy R Q =
      ∑ a : Q.parts,
        mean (fun x =>
          (conditionalMean P (partitionAtomIndicator Q a) x -
            conditionalMean R (partitionAtomIndicator Q a) x) ^ 2) := by
  unfold partitionAtomEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact partitionEnergy_sub_eq_mean_sq P R hPR
    (partitionAtomIndicator Q a)

noncomputable def orderedAtomEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) : ℝ :=
  partitionAtomEnergy (orderedBoundaryPartition lower e) upper

theorem orderedAtomEnergy_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    0 ≤ orderedAtomEnergy lower e upper :=
  partitionAtomEnergy_nonneg _ _

theorem orderedAtomEnergy_le_one
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy lower e upper ≤ 1 :=
  partitionAtomEnergy_le_one _ _

theorem orderedAtomEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy coarse e upper ≤
      orderedAtomEnergy fine e upper := by
  exact partitionAtomEnergy_mono
    (orderedBoundaryPartition_mono hfc e) upper

theorem orderedAtomEnergy_sub_eq_sum_mean_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy fine e upper -
        orderedAtomEnergy coarse e upper =
      ∑ a : upper.parts,
        mean (fun x =>
          (orderedBoundaryStructured fine e
                (partitionAtomIndicator upper a) x -
            orderedBoundaryStructured coarse e
                (partitionAtomIndicator upper a) x) ^ 2) := by
  exact partitionAtomEnergy_sub_eq_sum_mean_sq
    (orderedBoundaryPartition_mono hfc e) upper

end Erdos3.FixedDensity

end

end OAI

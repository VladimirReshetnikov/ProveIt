-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.FixedDensity.BooleanCutReduction
import OAI.Compat.Core

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

abbrev BooleanCutTest (Ω : Type*) [DecidableEq Ω] :=
  Finset Ω

namespace BooleanCutTest

def eval (A : BooleanCutTest Ω) : Ω → ℝ :=
  finsetIndicator A

omit [Fintype Ω] in
@[simp]
theorem eval_of_mem (A : BooleanCutTest Ω) {x : Ω} (hx : x ∈ A) :
    A.eval x = 1 :=
  finsetIndicator_of_mem hx

omit [Fintype Ω] in
@[simp]
theorem eval_of_not_mem (A : BooleanCutTest Ω) {x : Ω} (hx : x ∉ A) :
    A.eval x = 0 :=
  finsetIndicator_of_not_mem hx

omit [Fintype Ω] in
theorem eval_sq (A : BooleanCutTest Ω) (x : Ω) :
    A.eval x ^ 2 = A.eval x := by
  by_cases hx : x ∈ A <;> simp [hx]

omit [Fintype Ω] in
theorem eval_nonneg (A : BooleanCutTest Ω) (x : Ω) :
    0 ≤ A.eval x := by
  by_cases hx : x ∈ A <;> simp [hx]

omit [Fintype Ω] in
theorem eval_le_one (A : BooleanCutTest Ω) (x : Ω) :
    A.eval x ≤ 1 := by
  by_cases hx : x ∈ A <;> simp [hx]

end BooleanCutTest

def IsPartitionMeasurable (P : FacePartition Ω) (g : Ω → ℝ) : Prop :=
  ∀ x y, y ∈ P.part x → g y = g x

namespace IsPartitionMeasurable

theorem of_le {P Q : FacePartition Ω} {g : Ω → ℝ}
    (hPQ : P ≤ Q) (hg : IsPartitionMeasurable Q g) :
    IsPartitionMeasurable P g := by
  intro x y hy
  exact hg x y (FacePartition.part_subset_of_le hPQ x hy)

theorem conditionalMean_eq {P : FacePartition Ω} {g : Ω → ℝ}
    (hg : IsPartitionMeasurable P g) (x : Ω) :
    conditionalMean P g x = g x := by
  rw [conditionalMean]
  calc
    Finset.expect (P.part x) g =
        Finset.expect (P.part x) (fun _ => g x) := by
      apply Finset.expect_congr rfl
      intro y hy
      exact hg x y hy
    _ = g x := Finset.expect_const (by simp) _

theorem conditionalMean (P : FacePartition Ω) (f : Ω → ℝ) :
    IsPartitionMeasurable P (conditionalMean P f) := by
  intro x y hy
  exact conditionalMean_eq_of_mem_part P f hy

end IsPartitionMeasurable

theorem booleanCut_measurable_generatedBy (A : BooleanCutTest Ω) :
    IsPartitionMeasurable
      (FacePartition.generatedBy ({A} : Finset (Finset Ω))) A.eval := by
  intro x y hy
  have hxy : x ∈ A ↔ y ∈ A := by
    have hsignature :=
      (FacePartition.mem_part_generatedBy_iff
        ({A} : Finset (Finset Ω)) x y).1 hy
    exact hsignature A (by simp)
  by_cases hx : x ∈ A
  · have hyA : y ∈ A := hxy.mp hx
    simp [hx, hyA]
  · have hyA : y ∉ A := by
      intro hy
      exact hx (hxy.mpr hy)
    simp [hx, hyA]

structure FaceRegularityState (Ω : Type*) [Fintype Ω] [DecidableEq Ω] where
  partition : FacePartition Ω

abbrev FaceRegularitySystem
    (ι : Type*) (face : ι → Type*)
    [∀ i, Fintype (face i)] [∀ i, DecidableEq (face i)] :=
  ∀ i, FaceRegularityState (face i)

namespace FaceRegularityState

noncomputable def structured (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : Ω → ℝ :=
  conditionalMean S.partition f

noncomputable def residual (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : Ω → ℝ :=
  fun x => f x - S.structured f x

noncomputable def energy (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : ℝ :=
  partitionEnergy S.partition f

noncomputable def booleanCutCorrelation
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) : ℝ :=
  mean fun x => S.residual f x * A.eval x

def refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) : FaceRegularityState Ω where
  partition :=
    FacePartition.join S.partition
      (FacePartition.generatedBy ({A} : Finset (Finset Ω)))

@[simp]
theorem partition_refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).partition =
      FacePartition.join S.partition
        (FacePartition.generatedBy ({A} : Finset (Finset Ω))) :=
  rfl

theorem refineBy_le (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).partition ≤ S.partition :=
  FacePartition.join_le_left _ _

theorem booleanCut_measurable_refineBy (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    IsPartitionMeasurable (S.refineBy A).partition A.eval := by
  apply IsPartitionMeasurable.of_le
    (FacePartition.join_le_right S.partition
      (FacePartition.generatedBy ({A} : Finset (Finset Ω))))
  exact booleanCut_measurable_generatedBy A

theorem complexity_refineBy_le (S : FaceRegularityState Ω)
    (A : BooleanCutTest Ω) :
    FacePartition.complexity (S.refineBy A).partition ≤
      2 * FacePartition.complexity S.partition := by
  have hgenerated :
      FacePartition.complexity
          (FacePartition.generatedBy ({A} : Finset (Finset Ω))) ≤ 2 := by
    simpa using
      FacePartition.complexity_generatedBy_le
        ({A} : Finset (Finset Ω))
  calc
    FacePartition.complexity (S.refineBy A).partition ≤
        FacePartition.complexity S.partition *
          FacePartition.complexity
            (FacePartition.generatedBy
              ({A} : Finset (Finset Ω))) :=
      FacePartition.complexity_join_le _ _
    _ ≤ FacePartition.complexity S.partition * 2 :=
      Nat.mul_le_mul_left _ hgenerated
    _ = 2 * FacePartition.complexity S.partition := by
      omega

theorem structured_nonneg (S : FaceRegularityState Ω)
    {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Ω) :
    0 ≤ S.structured f x :=
  conditionalMean_nonneg S.partition hf x

theorem structured_le_one (S : FaceRegularityState Ω)
    {f : Ω → ℝ} (hf : ∀ x, f x ≤ 1) (x : Ω) :
    S.structured f x ≤ 1 :=
  conditionalMean_le_one S.partition hf x

@[simp]
theorem conditionalMean_residual (S : FaceRegularityState Ω)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean S.partition (S.residual f) x = 0 := by
  change
    conditionalMean S.partition
      (fun y => f y - conditionalMean S.partition f y) x = 0
  rw [conditionalMean_sub]
  rw [conditionalMean_idem]
  ring

@[simp]
theorem mean_residual (S : FaceRegularityState Ω) (f : Ω → ℝ) :
    mean (S.residual f) = 0 := by
  change
    mean (fun x => f x - conditionalMean S.partition f x) = 0
  rw [mean_sub]
  rw [mean_conditionalMean]
  ring

theorem conditionalMean_residual_refineBy
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) (x : Ω) :
    conditionalMean (S.refineBy A).partition (S.residual f) x =
      (S.refineBy A).structured f x - S.structured f x := by
  change
    conditionalMean (S.refineBy A).partition
        (fun y => f y - conditionalMean S.partition f y) x =
      conditionalMean (S.refineBy A).partition f x -
        conditionalMean S.partition f x
  rw [conditionalMean_sub]
  rw [conditionalMean_reverse_tower_of_le
    (S.refineBy A).partition S.partition (S.refineBy_le A)]

theorem mean_mul_eq_mean_conditionalMean_mul
    (P : FacePartition Ω) (u v : Ω → ℝ)
    (hv : IsPartitionMeasurable P v) :
    mean (fun x => u x * v x) =
      mean (fun x => conditionalMean P u x * v x) := by
  calc
    mean (fun x => u x * v x) =
        mean (conditionalMean P (fun x => u x * v x)) :=
      (mean_conditionalMean P _).symm
    _ = mean (fun x => conditionalMean P u x * v x) := by
      apply congrArg mean
      funext x
      exact conditionalMean_mul_right_of_constant_on_part
        P u v x (hv x)

theorem booleanCutCorrelation_eq_projection
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    S.booleanCutCorrelation f A =
      mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) := by
  rw [booleanCutCorrelation]
  calc
    mean (fun x => S.residual f x * A.eval x) =
        mean (fun x =>
          conditionalMean (S.refineBy A).partition (S.residual f) x *
            A.eval x) :=
      mean_mul_eq_mean_conditionalMean_mul
        (S.refineBy A).partition (S.residual f) A.eval
        (S.booleanCut_measurable_refineBy A)
    _ = mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) := by
      apply congrArg mean
      funext x
      rw [S.conditionalMean_residual_refineBy f A x]

omit [DecidableEq Ω] in

theorem mean_mul_sq_le_sq_mul_sq (u v : Ω → ℝ) :
    mean (fun x => u x * v x) ^ 2 ≤
      mean (fun x => u x ^ 2) * mean (fun x => v x ^ 2) := by
  simpa [mean] using
    (Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) u v)

theorem mean_booleanCut_sq_le_one [Nonempty Ω]
    (A : BooleanCutTest Ω) :
    mean (fun x => A.eval x ^ 2) ≤ 1 := by
  apply mean_le_of_le_const
  intro x
  rw [A.eval_sq x]
  exact A.eval_le_one x

theorem energy_refineBy_sub_eq_mean_sq
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    (S.refineBy A).energy f - S.energy f =
      mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) ^ 2) := by
  simpa [energy, structured] using
    partitionEnergy_sub_eq_mean_sq
      (S.refineBy A).partition S.partition (S.refineBy_le A) f

theorem booleanCutCorrelation_sq_le_energyIncrement [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) :
    S.booleanCutCorrelation f A ^ 2 ≤
      (S.refineBy A).energy f - S.energy f := by
  rw [S.booleanCutCorrelation_eq_projection f A]
  let d : Ω → ℝ :=
    fun x => (S.refineBy A).structured f x - S.structured f x
  have hcs :
      mean (fun x => d x * A.eval x) ^ 2 ≤
        mean (fun x => d x ^ 2) *
          mean (fun x => A.eval x ^ 2) :=
    mean_mul_sq_le_sq_mul_sq d A.eval
  have hd : 0 ≤ mean (fun x => d x ^ 2) :=
    mean_nonneg fun x => sq_nonneg _
  have hA := mean_booleanCut_sq_le_one A
  calc
    mean (fun x =>
        ((S.refineBy A).structured f x - S.structured f x) *
          A.eval x) ^ 2 =
        mean (fun x => d x * A.eval x) ^ 2 := rfl
    _ ≤ mean (fun x => d x ^ 2) *
        mean (fun x => A.eval x ^ 2) := hcs
    _ ≤ mean (fun x => d x ^ 2) := by
      nlinarith
    _ = (S.refineBy A).energy f - S.energy f := by
      exact (S.energy_refineBy_sub_eq_mean_sq f A).symm

theorem energy_increment_of_booleanCut [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hcorrelation : ε ≤ |S.booleanCutCorrelation f A|) :
    S.energy f + ε ^ 2 ≤ (S.refineBy A).energy f := by
  have hsquare :
      ε ^ 2 ≤ S.booleanCutCorrelation f A ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hε] using hcorrelation
  have hincrement :=
    S.booleanCutCorrelation_sq_le_energyIncrement f A
  linarith

def IsRegularAgainst (S : FaceRegularityState Ω)
    (f : Ω → ℝ) (cuts : Finset (BooleanCutTest Ω))
    (ε : ℝ) : Prop :=
  ∀ A ∈ cuts, |S.booleanCutCorrelation f A| ≤ ε

theorem exists_booleanCut_of_not_regular
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) {ε : ℝ}
    (h : ¬ S.IsRegularAgainst f cuts ε) :
    ∃ A ∈ cuts, ε < |S.booleanCutCorrelation f A| := by
  classical
  by_contra hnone
  apply h
  intro A hA
  by_contra hle
  apply hnone
  exact ⟨A, hA, lt_of_not_ge hle⟩

theorem energy_increment_budget [Nonempty Ω]
    (states : ℕ → FaceRegularityState Ω)
    (f : Ω → ℝ) {ε : ℝ} {m : ℕ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hgain : ∀ i, i < m →
      (states i).energy f + ε ^ 2 ≤ (states (i + 1)).energy f) :
    (m : ℝ) * ε ^ 2 ≤ 1 := by
  have growth :
      ∀ n : ℕ,
        (∀ i, i < n →
          (states i).energy f + ε ^ 2 ≤
            (states (i + 1)).energy f) →
        (states 0).energy f + (n : ℝ) * ε ^ 2 ≤
          (states n).energy f := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have hprevious := ih (fun i hi =>
          hn i (Nat.lt_trans hi (Nat.lt_succ_self n)))
        have hstep := hn n (Nat.lt_succ_self n)
        calc
          (states 0).energy f + (↑(Nat.succ n) : ℝ) * ε ^ 2 =
              ((states 0).energy f + (n : ℝ) * ε ^ 2) +
                ε ^ 2 := by
            push_cast
            ring
          _ ≤ (states n).energy f + ε ^ 2 :=
            by linarith
          _ ≤ (states (Nat.succ n)).energy f := by
            simpa [Nat.succ_eq_add_one] using hstep
  have hgrowth := growth m hgain
  have hnonneg :
      0 ≤ (states 0).energy f :=
    partitionEnergy_nonneg (states 0).partition f
  have hupper :
      (states m).energy f ≤ 1 :=
    partitionEnergy_le_one (states m).partition hf0 hf1
  linarith

theorem no_long_energy_increment_run [Nonempty Ω]
    (states : ℕ → FaceRegularityState Ω)
    (f : Ω → ℝ) {ε : ℝ} {m : ℕ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hlong : 1 < (m : ℝ) * ε ^ 2)
    (hgain : ∀ i, i < m →
      (states i).energy f + ε ^ 2 ≤
        (states (i + 1)).energy f) :
    False := by
  have hbudget :=
    energy_increment_budget states f hf0 hf1 hgain
  linarith

theorem exists_regular_state_in_refinement_run [Nonempty Ω]
    (states : ℕ → FaceRegularityState Ω)
    (witness : ℕ → BooleanCutTest Ω)
    (f : Ω → ℝ) (cuts : Finset (BooleanCutTest Ω))
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong : 1 < (m : ℝ) * ε ^ 2)
    (hrefine : ∀ i, i < m →
      states (i + 1) = (states i).refineBy (witness i))
    (hchoose : ∀ i, i < m →
      ¬(states i).IsRegularAgainst f cuts ε →
      witness i ∈ cuts ∧
        ε ≤ |(states i).booleanCutCorrelation f (witness i)|) :
    ∃ i, i < m ∧ (states i).IsRegularAgainst f cuts ε := by
  by_contra hregular
  have hnotregular :
      ∀ i, i < m →
        ¬(states i).IsRegularAgainst f cuts ε := by
    intro i hi hisRegular
    exact hregular ⟨i, hi, hisRegular⟩
  have hgain :
      ∀ i, i < m →
        (states i).energy f + ε ^ 2 ≤
          (states (i + 1)).energy f := by
    intro i hi
    have hcorrelation :=
      (hchoose i hi (hnotregular i hi)).2
    have hincrement :=
      (states i).energy_increment_of_booleanCut
        f (witness i) hε hcorrelation
    rw [hrefine i hi]
    exact hincrement
  exact no_long_energy_increment_run
    states f hf0 hf1 hlong hgain

noncomputable def chosenIrregularCut
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    BooleanCutTest Ω := by
  classical
  exact
    if h : S.IsRegularAgainst f cuts ε then ∅
    else
      Classical.choose
        (S.exists_booleanCut_of_not_regular f cuts h)

theorem chosenIrregularCut_mem
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (h : ¬S.IsRegularAgainst f cuts ε) :
    S.chosenIrregularCut f cuts ε ∈ cuts := by
  simp only [chosenIrregularCut, dite_eq_right h]
  exact
    (Classical.choose_spec
      (S.exists_booleanCut_of_not_regular f cuts h)).1

theorem chosenIrregularCut_correlation
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (h : ¬S.IsRegularAgainst f cuts ε) :
    ε <
      |S.booleanCutCorrelation f
        (S.chosenIrregularCut f cuts ε)| := by
  simp only [chosenIrregularCut, dite_eq_right h]
  exact
    (Classical.choose_spec
      (S.exists_booleanCut_of_not_regular f cuts h)).2

noncomputable def regularityRun
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    ℕ → FaceRegularityState Ω
  | 0 => S
  | n + 1 =>
      let T := regularityRun S f cuts ε n
      T.refineBy (T.chosenIrregularCut f cuts ε)

@[simp]
theorem regularityRun_zero
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.regularityRun f cuts ε 0 = S :=
  rfl

@[simp]
theorem regularityRun_succ
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    S.regularityRun f cuts ε (n + 1) =
      (S.regularityRun f cuts ε n).refineBy
        ((S.regularityRun f cuts ε n).chosenIrregularCut
          f cuts ε) :=
  rfl

theorem regularityRun_partition_le
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    (S.regularityRun f cuts ε n).partition ≤ S.partition := by
  induction n with
  | zero =>
      exact le_rfl
  | succ n ih =>
      exact
        le_trans
          ((S.regularityRun f cuts ε n).refineBy_le
            ((S.regularityRun f cuts ε n).chosenIrregularCut
              f cuts ε))
          ih

theorem regularityRun_complexity_le
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    FacePartition.complexity
        (S.regularityRun f cuts ε n).partition ≤
      2 ^ n * FacePartition.complexity S.partition := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        FacePartition.complexity
            (S.regularityRun f cuts ε (n + 1)).partition ≤
            2 * FacePartition.complexity
              (S.regularityRun f cuts ε n).partition := by
          rw [regularityRun_succ]
          exact
            (S.regularityRun f cuts ε n).complexity_refineBy_le
              ((S.regularityRun f cuts ε n).chosenIrregularCut
                f cuts ε)
        _ ≤ 2 * (2 ^ n *
              FacePartition.complexity S.partition) :=
          Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) *
              FacePartition.complexity S.partition := by
          rw [pow_succ]
          ring

noncomputable def regularityRunCuts
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    Finset (BooleanCutTest Ω) := by
  classical
  exact (Finset.range n).image fun i =>
    (S.regularityRun f cuts ε i).chosenIrregularCut
      f cuts ε

@[simp]
theorem regularityRunCuts_zero
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ) :
    S.regularityRunCuts f cuts ε 0 = ∅ := by
  simp [regularityRunCuts]

@[simp]
theorem regularityRunCuts_succ
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    S.regularityRunCuts f cuts ε (n + 1) =
      insert
        ((S.regularityRun f cuts ε n).chosenIrregularCut
          f cuts ε)
        (S.regularityRunCuts f cuts ε n) := by
  classical
  simp [regularityRunCuts, Finset.range_add_one]

theorem chosenIrregularCut_mem_of_empty_mem
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (hempty : (∅ : BooleanCutTest Ω) ∈ cuts) :
    S.chosenIrregularCut f cuts ε ∈ cuts := by
  by_cases hregular : S.IsRegularAgainst f cuts ε
  · simpa [chosenIrregularCut, hregular] using hempty
  · exact S.chosenIrregularCut_mem f cuts ε hregular

theorem regularityRunCuts_subset
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (hempty : (∅ : BooleanCutTest Ω) ∈ cuts)
    (n : ℕ) :
    S.regularityRunCuts f cuts ε n ⊆ cuts := by
  classical
  intro A hA
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
  exact chosenIrregularCut_mem_of_empty_mem
    (S.regularityRun f cuts ε i) f cuts ε hempty

theorem regularityRun_partition_eq_join_generatedBy
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω)) (ε : ℝ)
    (n : ℕ) :
    (S.regularityRun f cuts ε n).partition =
      FacePartition.join S.partition
        (FacePartition.generatedBy
          (S.regularityRunCuts f cuts ε n)) := by
  induction n with
  | zero =>
      rw [regularityRun_zero, regularityRunCuts_zero,
        FacePartition.generatedBy_empty]
      change S.partition = S.partition ⊓ ⊤
      exact (inf_top_eq S.partition).symm
  | succ n ih =>
      let A : BooleanCutTest Ω :=
        (S.regularityRun f cuts ε n).chosenIrregularCut
          f cuts ε
      calc
        (S.regularityRun f cuts ε (n + 1)).partition =
            FacePartition.join
              (S.regularityRun f cuts ε n).partition
              (FacePartition.generatedBy
                ({A} : Finset (Finset Ω))) := by
          rfl
        _ =
            FacePartition.join
              (FacePartition.join S.partition
                (FacePartition.generatedBy
                  (S.regularityRunCuts f cuts ε n)))
              (FacePartition.generatedBy
                ({A} : Finset (Finset Ω))) := by
          rw [ih]
        _ =
            FacePartition.join S.partition
              (FacePartition.join
                (FacePartition.generatedBy
                  (S.regularityRunCuts f cuts ε n))
                (FacePartition.generatedBy
                  ({A} : Finset (Finset Ω)))) := by
          exact inf_assoc _ _ _
        _ =
            FacePartition.join S.partition
              (FacePartition.generatedBy
                (insert A
                  (S.regularityRunCuts f cuts ε n))) := by
          rw [FacePartition.generatedBy_insert]
        _ =
            FacePartition.join S.partition
              (FacePartition.generatedBy
                (S.regularityRunCuts f cuts ε (n + 1))) := by
          rw [regularityRunCuts_succ]

theorem exists_regular_run_index_before [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω))
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong : 1 < (m : ℝ) * ε ^ 2) :
    ∃ i : ℕ, i < m ∧
      (S.regularityRun f cuts ε i).IsRegularAgainst
        f cuts ε := by
  exact
    exists_regular_state_in_refinement_run
      (S.regularityRun f cuts ε)
      (fun n =>
        (S.regularityRun f cuts ε n).chosenIrregularCut
          f cuts ε)
      f cuts hf0 hf1 hε hlong
      (fun n _ => S.regularityRun_succ f cuts ε n)
      (fun n _ hn =>
        ⟨(S.regularityRun f cuts ε n).chosenIrregularCut_mem
            f cuts ε hn,
          le_of_lt
            (chosenIrregularCut_correlation
              (S.regularityRun f cuts ε n) f cuts ε hn)⟩)

theorem exists_regular_refinement_before [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω))
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong : 1 < (m : ℝ) * ε ^ 2) :
    ∃ i : ℕ, ∃ T : FaceRegularityState Ω,
      i < m ∧
      T.partition ≤ S.partition ∧
      T.IsRegularAgainst f cuts ε ∧
      FacePartition.complexity T.partition ≤
        2 ^ i * FacePartition.complexity S.partition := by
  obtain ⟨i, hi, hregular⟩ :=
    S.exists_regular_run_index_before f cuts
      hf0 hf1 hε hlong
  exact
    ⟨i, S.regularityRun f cuts ε i, hi,
      S.regularityRun_partition_le f cuts ε i,
      hregular,
      S.regularityRun_complexity_le f cuts ε i⟩

theorem exists_regular_refinement [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (cuts : Finset (BooleanCutTest Ω))
    {ε : ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 < ε) :
    ∃ m i : ℕ, ∃ T : FaceRegularityState Ω,
      1 < (m : ℝ) * ε ^ 2 ∧
      i < m ∧
      T.partition ≤ S.partition ∧
      T.IsRegularAgainst f cuts ε ∧
      FacePartition.complexity T.partition ≤
        2 ^ i * FacePartition.complexity S.partition := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε ^ 2)
  have hlong : 1 < (m : ℝ) * ε ^ 2 := by
    calc
      1 = (1 / ε ^ 2) * ε ^ 2 := by
        field_simp
      _ < (m : ℝ) * ε ^ 2 :=
        mul_lt_mul_of_pos_right hm hεsq
  obtain ⟨i, T, hi, hTS, hregular, hcomplexity⟩ :=
    S.exists_regular_refinement_before f cuts
      hf0 hf1 hε.le hlong
  exact
    ⟨m, i, T, hlong, hi, hTS, hregular, hcomplexity⟩

theorem exists_regular_refinement_allCuts [Nonempty Ω]
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    {ε : ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 < ε) :
    ∃ m i : ℕ, ∃ T : FaceRegularityState Ω,
      1 < (m : ℝ) * ε ^ 2 ∧
      i < m ∧
      T.partition ≤ S.partition ∧
      (∀ A : BooleanCutTest Ω,
        |T.booleanCutCorrelation f A| ≤ ε) ∧
      FacePartition.complexity T.partition ≤
        2 ^ i * FacePartition.complexity S.partition := by
  classical
  obtain ⟨m, i, T, hlong, hi, hTS, hregular, hcomplexity⟩ :=
    S.exists_regular_refinement f
      (Finset.univ : Finset (BooleanCutTest Ω))
      hf0 hf1 hε
  refine ⟨m, i, T, hlong, hi, hTS, ?_, hcomplexity⟩
  intro A
  exact hregular A (Finset.mem_univ A)

end FaceRegularityState

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) :
    BooleanCutTest (Fin r → G) := by
  classical
  exact Finset.univ.filter fun x =>
    ∀ i, b ⟨i, eraseCoordinate i x⟩ = true

@[simp]
theorem mem_booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) (x : Fin r → G) :
    x ∈ booleanFaceCutSupport b ↔
      ∀ i, b ⟨i, eraseCoordinate i x⟩ = true := by
  simp [booleanFaceCutSupport]

theorem booleanFaceCutSupport_eval
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) (x : Fin r → G) :
    (booleanFaceCutSupport b).eval x =
      cutTestProduct (cutTestFamilyOfBooleanAssignment b) x := by
  classical
  by_cases h : ∀ i, b ⟨i, eraseCoordinate i x⟩ = true
  · have hx : x ∈ booleanFaceCutSupport b := by
      simp [booleanFaceCutSupport, h]
    rw [BooleanCutTest.eval_of_mem _ hx]
    unfold cutTestProduct
    symm
    apply Finset.prod_eq_one
    intro i _
    simp [cutTestFamilyOfBooleanAssignment, booleanValue, h i]
  · have hx : x ∉ booleanFaceCutSupport b := by
      simpa [booleanFaceCutSupport] using h
    rw [BooleanCutTest.eval_of_not_mem _ hx]
    obtain ⟨i, hi⟩ := not_forall.mp h
    cases hb : b ⟨i, eraseCoordinate i x⟩ with
    | false =>
        unfold cutTestProduct
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [cutTestFamilyOfBooleanAssignment,
          booleanValue, hb]
    | true =>
        exact (hi hb).elim

noncomputable def booleanFaceCutSupports
    (G : Type*) [Fintype G] [DecidableEq G] (r : ℕ) :
    Finset (BooleanCutTest (Fin r → G)) := by
  classical
  exact Finset.univ.image booleanFaceCutSupport

theorem booleanFaceCutSupport_mem_supports
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) :
    booleanFaceCutSupport b ∈ booleanFaceCutSupports G r := by
  classical
  exact Finset.mem_image.mpr
    ⟨b, Finset.mem_univ b, rfl⟩

theorem booleanFaceCutSupport_false
    {G : Type*} [Fintype G] [DecidableEq G]
    {r : ℕ} (hr : 0 < r) :
    booleanFaceCutSupport
        (fun _ : CutTestCoordinate G r => false) =
      ∅ := by
  classical
  ext x
  constructor
  · intro hx
    have hall :=
      (mem_booleanFaceCutSupport
        (fun _ : CutTestCoordinate G r => false) x).1 hx
    have hfalse := hall ⟨0, hr⟩
    simp at hfalse
  · intro hx
    simp at hx

theorem empty_mem_booleanFaceCutSupports
    {G : Type*} [Fintype G] [DecidableEq G]
    {r : ℕ} (hr : 0 < r) :
    (∅ : BooleanCutTest (Fin r → G)) ∈
      booleanFaceCutSupports G r := by
  classical
  apply Finset.mem_image.mpr
  refine
    ⟨(fun _ : CutTestCoordinate G r => false),
      Finset.mem_univ _, ?_⟩
  exact booleanFaceCutSupport_false hr

namespace FaceRegularityState

noncomputable def faceCutCorrelation
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x => S.residual f x * cutTestProduct u x

theorem faceCutCorrelation_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ)
    (b : BooleanCutAssignment G r) :
    S.faceCutCorrelation f
        (cutTestFamilyOfBooleanAssignment b) =
      S.booleanCutCorrelation f (booleanFaceCutSupport b) := by
  unfold faceCutCorrelation booleanCutCorrelation
  apply congrArg mean
  funext x
  rw [booleanFaceCutSupport_eval]

theorem faceCutCorrelation_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : CutTestFamily G r) :
    S.faceCutCorrelation f u =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          S.faceCutCorrelation f
            (cutTestFamilyOfBooleanAssignment b) := by
  unfold faceCutCorrelation
  calc
    mean (fun x : Fin r → G =>
        S.residual f x * cutTestProduct u x) =
        mean (fun x : Fin r → G =>
          ∑ b : BooleanCutAssignment G r,
            bernoulliAssignmentWeight
                (cutTestCoordinateValue u) b *
              (S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x)) := by
      apply congrArg mean
      funext x
      rw [cutTestProduct_eq_sum_boolean u x,
        Finset.mul_sum]
      apply Fintype.sum_congr
      intro b
      ring
    _ =
        ∑ b : BooleanCutAssignment G r,
          mean (fun x : Fin r → G =>
            bernoulliAssignmentWeight
                (cutTestCoordinateValue u) b *
              (S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x)) := by
      unfold mean
      exact Finset.expect_sum_comm Finset.univ Finset.univ _
    _ =
        ∑ b : BooleanCutAssignment G r,
          bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            mean (fun x : Fin r → G =>
              S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x) := by
      apply Fintype.sum_congr
      intro b
      exact mean_smul
        (bernoulliAssignmentWeight
          (cutTestCoordinateValue u) b) _
    _ = _ := by
      rfl

def IsFaceCutRegular
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (ε : ℝ) : Prop :=
  ∀ u : CutTestFamily G r,
    IsBoundedCutTest u →
      |S.faceCutCorrelation f u| ≤ ε

theorem isFaceCutRegular_of_regularAgainst_supports
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) {ε : ℝ}
    (hregular :
      S.IsRegularAgainst f (booleanFaceCutSupports G r) ε) :
    S.IsFaceCutRegular f ε := by
  intro u hu
  rw [faceCutCorrelation_eq_sum_boolean]
  calc
    |∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          S.faceCutCorrelation f
            (cutTestFamilyOfBooleanAssignment b)| ≤
        ∑ b : BooleanCutAssignment G r,
          |bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            S.faceCutCorrelation f
              (cutTestFamilyOfBooleanAssignment b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ b : BooleanCutAssignment G r,
          bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b * ε := by
      apply Finset.sum_le_sum
      intro b _
      have hw :
          0 ≤ bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b :=
        bernoulliAssignmentWeight_nonneg
          (p := cutTestCoordinateValue u)
          (fun q => hu.nonneg q.1 q.2)
          (fun q => hu.le_one q.1 q.2) b
      rw [abs_mul, abs_of_nonneg hw]
      apply mul_le_mul_of_nonneg_left _ hw
      rw [faceCutCorrelation_boolean]
      exact hregular (booleanFaceCutSupport b)
        (booleanFaceCutSupport_mem_supports b)
    _ = ε := by
      rw [← Finset.sum_mul,
        sum_bernoulliAssignmentWeight, one_mul]

theorem exists_faceCutRegular_refinement
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ)
    {ε : ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 < ε) :
    ∃ m i : ℕ, ∃ T : FaceRegularityState (Fin r → G),
      1 < (m : ℝ) * ε ^ 2 ∧
      i < m ∧
      T.partition ≤ S.partition ∧
      T.IsFaceCutRegular f ε ∧
      FacePartition.complexity T.partition ≤
        2 ^ i * FacePartition.complexity S.partition := by
  obtain ⟨m, i, T, hlong, hi, hTS, hregular, hcomplexity⟩ :=
    S.exists_regular_refinement f
      (booleanFaceCutSupports G r) hf0 hf1 hε
  exact
    ⟨m, i, T, hlong, hi, hTS,
      T.isFaceCutRegular_of_regularAgainst_supports f hregular,
      hcomplexity⟩

theorem exists_faceCutRegular_refinement_with_generators_before
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r : ℕ} (hr : 0 < r)
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ)
    {ε : ℝ} {m : ℕ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 ≤ ε)
    (hlong : 1 < (m : ℝ) * ε ^ 2) :
    ∃ i : ℕ,
      ∃ T : FaceRegularityState (Fin r → G),
      ∃ F : Finset (BooleanCutTest (Fin r → G)),
        i < m ∧
        T.partition =
          FacePartition.join S.partition
            (FacePartition.generatedBy F) ∧
        F ⊆ booleanFaceCutSupports G r ∧
        F.card ≤ i ∧
        T.IsFaceCutRegular f ε ∧
        FacePartition.complexity T.partition ≤
          2 ^ i * FacePartition.complexity S.partition := by
  let cuts := booleanFaceCutSupports G r
  obtain ⟨i, hi, hregular⟩ :=
    S.exists_regular_run_index_before f cuts
      hf0 hf1 hε hlong
  let T := S.regularityRun f cuts ε i
  let F := S.regularityRunCuts f cuts ε i
  have hpart :
      T.partition =
        FacePartition.join S.partition
          (FacePartition.generatedBy F) :=
    S.regularityRun_partition_eq_join_generatedBy
      f cuts ε i
  have hsubset :
      F ⊆ booleanFaceCutSupports G r := by
    exact S.regularityRunCuts_subset f cuts ε
      (by
        dsimp [cuts]
        exact empty_mem_booleanFaceCutSupports hr)
      i
  have hcard : F.card ≤ i := by
    unfold F regularityRunCuts
    exact Finset.card_image_le.trans_eq (Finset.card_range i)
  have hface : T.IsFaceCutRegular f ε :=
    T.isFaceCutRegular_of_regularAgainst_supports
      f hregular
  have hcomplexity :
      FacePartition.complexity T.partition ≤
        2 ^ i * FacePartition.complexity S.partition :=
    S.regularityRun_complexity_le f cuts ε i
  exact
    ⟨i, T, F, hi, hpart, hsubset,
      hcard, hface, hcomplexity⟩

theorem exists_faceCutRegular_refinement_with_generators
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r : ℕ} (hr : 0 < r)
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ)
    {ε : ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (hε : 0 < ε) :
    ∃ m i : ℕ,
      ∃ T : FaceRegularityState (Fin r → G),
      ∃ F : Finset (BooleanCutTest (Fin r → G)),
        1 < (m : ℝ) * ε ^ 2 ∧
        i < m ∧
        T.partition =
          FacePartition.join S.partition
            (FacePartition.generatedBy F) ∧
        F ⊆ booleanFaceCutSupports G r ∧
        F.card ≤ i ∧
        T.IsFaceCutRegular f ε ∧
        FacePartition.complexity T.partition ≤
          2 ^ i * FacePartition.complexity S.partition := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε ^ 2)
  have hlong : 1 < (m : ℝ) * ε ^ 2 := by
    calc
      1 = (1 / ε ^ 2) * ε ^ 2 := by
        field_simp
      _ < (m : ℝ) * ε ^ 2 :=
        mul_lt_mul_of_pos_right hm hεsq
  obtain ⟨i, T, F, hi, hpart, hsubset, hcard,
      hface, hcomplexity⟩ :=
    S.exists_faceCutRegular_refinement_with_generators_before
      hr f hf0 hf1 hε.le hlong
  exact
    ⟨m, i, T, F, hlong, hi, hpart, hsubset,
      hcard, hface, hcomplexity⟩

end FaceRegularityState

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

noncomputable def representingBooleanFaceCutAssignment
    (G : Type*) [Fintype G] [DecidableEq G] (r : ℕ)
    (A : BooleanCutTest (Fin r → G)) :
    BooleanCutAssignment G r := by
  classical
  exact
    if hA : A ∈ booleanFaceCutSupports G r then
      Classical.choose
        (show ∃ b : BooleanCutAssignment G r,
            booleanFaceCutSupport b = A by
          obtain ⟨b, _hb, hsupport⟩ :=
            Finset.mem_image.mp hA
          exact ⟨b, hsupport⟩)
    else
      fun _ => false

theorem booleanFaceCutSupport_representing
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    {A : BooleanCutTest (Fin r → G)}
    (hA : A ∈ booleanFaceCutSupports G r) :
    booleanFaceCutSupport
        (representingBooleanFaceCutAssignment G r A) = A := by
  classical
  simp only [representingBooleanFaceCutAssignment, dite_eq_left hA]
  exact
    Classical.choose_spec
      (show ∃ b : BooleanCutAssignment G r,
          booleanFaceCutSupport b = A by
        obtain ⟨b, _hb, hsupport⟩ :=
          Finset.mem_image.mp hA
        exact ⟨b, hsupport⟩)

abbrev GeneratorBranch
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G))) :=
  F → Fin r

@[simp]
theorem card_generatorBranch
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G))) :
    Fintype.card (GeneratorBranch F) = r ^ F.card := by
  simp [GeneratorBranch]

noncomputable def lowerGeneratorCell
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G)))
    (y : Fin r → G) (w : GeneratorBranch F) (i : Fin r) :
    BooleanCutTest (Fin (r - 1) → G) := by
  classical
  exact Finset.univ.filter fun z =>
    ∀ A : F,
      (y ∈ A.1 →
        representingBooleanFaceCutAssignment G r A.1
            ⟨i, z⟩ = true) ∧
      (y ∉ A.1 → w A = i →
        representingBooleanFaceCutAssignment G r A.1
            ⟨i, z⟩ = false)

@[simp]
theorem mem_lowerGeneratorCell
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G)))
    (y : Fin r → G) (w : GeneratorBranch F) (i : Fin r)
    (z : Fin (r - 1) → G) :
    z ∈ lowerGeneratorCell F y w i ↔
      ∀ A : F,
        (y ∈ A.1 →
          representingBooleanFaceCutAssignment G r A.1
              ⟨i, z⟩ = true) ∧
        (y ∉ A.1 → w A = i →
          representingBooleanFaceCutAssignment G r A.1
              ⟨i, z⟩ = false) := by
  simp [lowerGeneratorCell]

theorem mem_generatedBy_part_iff_exists_lowerGeneratorCells
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (hr : 0 < r)
    (F : Finset (BooleanCutTest (Fin r → G)))
    (hF : F ⊆ booleanFaceCutSupports G r)
    (y x : Fin r → G) :
    x ∈ (FacePartition.generatedBy F).part y ↔
      ∃ w : GeneratorBranch F,
        ∀ i,
          eraseCoordinate i x ∈
            lowerGeneratorCell F y w i := by
  classical
  constructor
  · intro hpart
    have hsignature :
        ∀ A ∈ F, (y ∈ A ↔ x ∈ A) :=
      (FacePartition.mem_part_generatedBy_iff F y x).1 hpart
    have hwitness :
        ∀ A : F, y ∉ A.1 →
          ∃ i : Fin r,
            representingBooleanFaceCutAssignment G r A.1
                ⟨i, eraseCoordinate i x⟩ = false := by
      intro A hyA
      have hxA : x ∉ A.1 := by
        intro hx
        exact hyA ((hsignature A.1 A.2).2 hx)
      have hsupport :
          booleanFaceCutSupport
              (representingBooleanFaceCutAssignment G r A.1) =
            A.1 :=
        booleanFaceCutSupport_representing (hF A.2)
      have hnotall :
          ¬∀ i,
            representingBooleanFaceCutAssignment G r A.1
                ⟨i, eraseCoordinate i x⟩ = true := by
        intro hall
        apply hxA
        rw [← hsupport]
        exact
          (mem_booleanFaceCutSupport
            (representingBooleanFaceCutAssignment G r A.1) x).2
            hall
      obtain ⟨i, hi⟩ := not_forall.mp hnotall
      refine ⟨i, ?_⟩
      cases hb :
          representingBooleanFaceCutAssignment G r A.1
            ⟨i, eraseCoordinate i x⟩ with
      | false => rfl
      | true => exact (hi hb).elim
    let w : GeneratorBranch F := fun A =>
      if hyA : y ∉ A.1 then
        Classical.choose (hwitness A hyA)
      else
        ⟨0, hr⟩
    refine ⟨w, ?_⟩
    intro i
    rw [mem_lowerGeneratorCell]
    intro A
    constructor
    · intro hyA
      have hxA : x ∈ A.1 :=
        (hsignature A.1 A.2).1 hyA
      have hsupport :
          booleanFaceCutSupport
              (representingBooleanFaceCutAssignment G r A.1) =
            A.1 :=
        booleanFaceCutSupport_representing (hF A.2)
      have hxSupport :
          x ∈ booleanFaceCutSupport
            (representingBooleanFaceCutAssignment G r A.1) := by
        simpa only [hsupport] using hxA
      exact
        (mem_booleanFaceCutSupport
          (representingBooleanFaceCutAssignment G r A.1) x).1
          hxSupport i
    · intro hyA hwi
      have hchosen :=
        Classical.choose_spec (hwitness A hyA)
      have hw :
          w A = Classical.choose (hwitness A hyA) := by
        simp [w, hyA]
      rw [hw] at hwi
      simpa only [hwi] using hchosen
  · rintro ⟨w, hcells⟩
    apply
      (FacePartition.mem_part_generatedBy_iff F y x).2
    intro A hAF
    let A' : F := ⟨A, hAF⟩
    have hsupport :
        booleanFaceCutSupport
            (representingBooleanFaceCutAssignment G r A) =
          A :=
      booleanFaceCutSupport_representing (hF hAF)
    constructor
    · intro hyA
      have hall :
          ∀ i,
            representingBooleanFaceCutAssignment G r A
                ⟨i, eraseCoordinate i x⟩ = true := by
        intro i
        exact
          ((mem_lowerGeneratorCell F y w i
            (eraseCoordinate i x)).1 (hcells i) A').1 hyA
      rw [← hsupport]
      exact
        (mem_booleanFaceCutSupport
          (representingBooleanFaceCutAssignment G r A) x).2
          hall
    · intro hxA
      by_contra hyA
      have hxSupport :
          x ∈ booleanFaceCutSupport
            (representingBooleanFaceCutAssignment G r A) := by
        simpa only [hsupport] using hxA
      have htrue :=
        (mem_booleanFaceCutSupport
          (representingBooleanFaceCutAssignment G r A) x).1
          hxSupport (w A')
      have hfalse :=
        ((mem_lowerGeneratorCell F y w (w A')
          (eraseCoordinate (w A') x)).1
          (hcells (w A')) A').2 hyA rfl
      rw [htrue] at hfalse
      simp at hfalse

end Erdos3.FixedDensity

end

end OAI

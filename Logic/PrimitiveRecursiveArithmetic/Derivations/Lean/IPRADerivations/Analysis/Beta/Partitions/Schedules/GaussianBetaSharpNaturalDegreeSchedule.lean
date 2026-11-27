import IPRADerivations.Analysis.Beta.Partitions.Schedules.GaussianBetaSharpCofinalSchedule

/-!
# Original sharp schedule guards at every natural beta degree N>=2

The cutoff, multiplier, counts and all precision thresholds are the
unchanged original cofinal schedule. The numerical guard proofs need
only the native positive real-part source and N>=2. In particular neither
R>=1 nor 2R<=N is required by these schedule guards.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaSharpNaturalDegreeSchedule

open_ipra
open GaussianBetaSharpCofinalSchedule (cutoff factor supportCount minimumH minimumPrecision
  cutoff_bounds factor_positive support_cells_from_degree middle_time_budget_from_partition)
open GaussianCoefficientNameBounds (unit)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianBetaSharpPartition (lowWidth middleWidth)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A N : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏ le two N

theorem degree_positive (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx] le one N :=
  le_trans (le_succ_self one) h.andE₂

theorem original_partition (t z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    GaussianBetaSharpPartition.source (cutoff t A N) A R N :=
  .andI h.andE₁.andE₁ (.andI h.andE₂ (cutoff_bounds t A R N).andE₂.andE₂)

theorem support_cells (t H z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N)
    (hH : Γ ⊢[PRAAx] le (minimumH t z R B A N) H) : Γ ⊢[PRAAx]
    le (GaussianBetaFiniteEulerAtCutoff.minimumCells t (cutoff t A N) z R B A N) (supportCount t H A R N) :=
  support_cells_from_degree t H z R B A N h.andE₂ hH

theorem low_count_positive (t H z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N)
    (hH : Γ ⊢[PRAAx] le (minimumH t z R B A N) H) : Γ ⊢[PRAAx]
    le one (lowWidth (cutoff t A N) A R*factor t H A R N) :=
  positive_product _ _
    (GaussianBetaSharpPartition.low_width_positive (cutoff t A N) A R h.andE₁.andE₁)
    (factor_positive t H z R B A N hH)

theorem middle_time_budget (p t H z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t H z R B A N) p) : Γ ⊢[PRAAx]
    le (two*middleWidth (cutoff t A N) A R N*unit t) (etaDen (cutoff t A N) A R*unit p) :=
  middle_time_budget_from_partition p t H z R B A N (original_partition t z R B A N h) hp

theorem tail_source (t H z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N)
    (hH : Γ ⊢[PRAAx] le (minimumH t z R B A N) H) : Γ ⊢[PRAAx]
    GaussianBetaContiguousUpperTail.source z R B A N (top (cutoff t A N) A R) (factor t H A R N) :=
  .andI h.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁ (.andI h.andE₂
    (.andI (cutoff_bounds t A R N).andE₂.andE₂ (factor_positive t H z R B A N hH))))

theorem original_natural_degree_source_support_schedule_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((source (var 2) (var 3) (var 4) (var 5) (var 6) ⋏
        le (minimumH (var 0) (var 2) (var 3) (var 4) (var 5) (var 6)) (var 1)) ⟶
        (le (GaussianBetaFiniteEulerAtCutoff.minimumCells (var 0) (cutoff (var 0) (var 5) (var 6))
            (var 2) (var 3) (var 4) (var 5) (var 6)) (supportCount (var 0) (var 1) (var 5) (var 3) (var 6)) ⋏
          (le one (lowWidth (cutoff (var 0) (var 5) (var 6)) (var 5) (var 3)*factor (var 0) (var 1) (var 5) (var 3) (var 6)) ⋏
            GaussianBetaSharpPartition.source (cutoff (var 0) (var 5) (var 6)) (var 5) (var 3) (var 6)))) :=
  closeUniv 7 (.impI (.andI (support_cells _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (.andI (low_count_positive _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
      (original_partition _ _ _ _ _ _ Prf.hyp0.andE₁))))

theorem original_natural_degree_middle_sampling_budget_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      ((source (var 3) (var 4) (var 5) (var 6) (var 7) ⋏
        le (minimumPrecision (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) (var 0)) ⟶
        le (two*middleWidth (cutoff (var 1) (var 6) (var 7)) (var 6) (var 4) (var 7)*unit (var 1))
          (etaDen (cutoff (var 1) (var 6) (var 7)) (var 6) (var 4)*unit (var 0))) :=
  closeUniv 8 (.impI (middle_time_budget _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaSharpNaturalDegreeSchedule

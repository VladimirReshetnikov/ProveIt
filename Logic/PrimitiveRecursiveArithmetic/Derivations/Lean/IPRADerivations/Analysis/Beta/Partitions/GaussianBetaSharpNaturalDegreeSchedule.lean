import IPRADerivations.Analysis.Beta.Partitions.GaussianBetaSharpCofinalSchedule

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
  cutoff_bounds mesh_budgets factor_positive support_width_positive finite_binding_time_budget)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianBetaSharpPartition (lowWidth middleWidth)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

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
    le (GaussianBetaFiniteEulerAtCutoff.minimumCells t (cutoff t A N) z R B A N) (supportCount t H A R N) := by
  have positive := support_width_positive (etaDen (cutoff t A N) A R) N
    (GaussianGammaIntegralCutoffs.eta_den_positive _ _ _) h.andE₂
  have grow : Γ ⊢[PRAAx] le (factor t H A R N) (supportCount t H A R N) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (factor t H A R N) positive)
  exact le_trans (mesh_budgets t H z R B A N hH).andE₂.andE₁ grow

theorem low_count_positive (t H z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N)
    (hH : Γ ⊢[PRAAx] le (minimumH t z R B A N) H) : Γ ⊢[PRAAx]
    le one (lowWidth (cutoff t A N) A R*factor t H A R N) := by
  let k := cutoff t A N
  have even := GaussianBetaSharpPartition.even_denominator (Γ := Γ) k A R h.andE₁.andE₁
  have twoBound : Γ ⊢[PRAAx] le two (etaDen k A R) :=
    le_congr (one_mul two) ((mul_comm _ _).eqTrans even.eqSymm)
      (mul_le_mul_right two (unit_positive (LeanProofs.IPRA.PTm.monus (A*GaussianGammaIntegralCutoffs.height k A R) one)))
  have endpoint := (GaussianBetaSharpPartition.exact_partition k A R N (original_partition t z R B A N h)).andE₁
  have widthPos : Γ ⊢[PRAAx] le one (lowWidth k A R) := by
    have eq := natEq endpoint
    ipra_simps
    ipra_le sl twoBound using
      linear_combination eq
  exact positive_product _ _ widthPos (factor_positive t H z R B A N hH)

theorem middle_time_budget (p t H z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t H z R B A N) p) : Γ ⊢[PRAAx]
    le (two*middleWidth (cutoff t A N) A R N*unit t) (etaDen (cutoff t A N) A R*unit p) := by
  let k := cutoff t A N
  let C := middleWidth k A R N
  let E := etaDen k A R
  have part := original_partition t z R B A N h
  have endpoint := (GaussianBetaSharpPartition.exact_partition k A R N part).andE₂.andE₁
  have halfBound := (GaussianBetaSharpPartition.half_boundary_order k A R N part.andE₁ part.andE₂.andE₁).andE₂
  have right : Γ ⊢[PRAAx] le (E*N) (E*top k A R) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right E part.andE₂.andE₂)
  have width : Γ ⊢[PRAAx] le C (E*top k A R) := le_trans (le_add_left C E)
    (le_trans (le_congr endpoint.eqSymm (.eqRefl _) halfBound) right)
  have clock := finite_binding_time_budget p t H z R B A N hp
  ipra_le (𝔞 E)*sl clock+(2*𝔞(unit t))*sl width

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

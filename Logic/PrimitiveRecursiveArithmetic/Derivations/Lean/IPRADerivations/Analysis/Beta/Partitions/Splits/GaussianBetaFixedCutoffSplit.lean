import IPRADerivations.Analysis.Beta.Partitions.Alignment.GaussianBetaRefinedFixedCompactComparison
import IPRADerivations.Analysis.Beta.Partitions.Splits.GaussianBetaIntegralThreeSplit

/-!
# Actual beta split at one fixed original cutoff

The original interval [1/eta(k),N] is split at original top(k).
Its exact counts are C*S, width(k)*S and ((N-top(k))*eta(k))*S.
Original beta encoding errors give exactly 2C/(eta(k)*2^p), hence
the coarse bound 2N/2^p. The upper sample has precisely the original
upper-tail program's start, width and common-step count. Choosing
S=conservativeCells(q,k)*factor returns the SAME middle quadrature to
the actual original fixed compact Euler observation, with all clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaFixedCutoffSplit

open_ipra
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCompactRiemannName (quadrature)
open GaussianBetaKernelGridComparison (evaluatorF sampleDataBeta)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianGammaEulerCompactQuadrature (conservativeCells)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def upperWidth (k A R N : PTm n) : PTm n := monus N (top k A R)*etaDen k A R
def fullWidth (k A R N : PTm n) : PTm n := monus (etaDen k A R*N) one
def full (p z B k A R N S : PTm n) : PTm n :=
  quadrature evaluatorF p (fullWidth k A R N*S) one (fullWidth k A R N) (etaDen k A R) (sampleDataBeta z B N)
def middle (p z B k A R N S : PTm n) : PTm n :=
  quadrature evaluatorF p (width k A R*S) one (width k A R) (etaDen k A R) (sampleDataBeta z B N)
def upper (p z B k A R N S : PTm n) : PTm n :=
  quadrature evaluatorF p (upperWidth k A R N*S) (top k A R*etaDen k A R) (upperWidth k A R N) (etaDen k A R) (sampleDataBeta z B N)
def source (z R B k A N S : PTm n) : Fm PTm n := GaussianGammaEulerCompactQuadrature.source z R B ⋏
  (lt (top k A R) N ⋏ le one S)
def commonMultiplier (q k A R factor : PTm n) : PTm n := conservativeCells q k A R*factor
def middleFactor (k A R factor : PTm n) : PTm n := width k A R*factor

theorem degree_positive (k A R N : PTm n) (h : Γ ⊢[PRAAx] lt (top k A R) N) : Γ ⊢[PRAAx] le one N :=
  le_trans (GaussianGammaIntegralCutoffs.top_positive _ _ _) (le_of_lt h)
theorem upper_width_positive (k A R N : PTm n) (h : Γ ⊢[PRAAx] lt (top k A R) N) : Γ ⊢[PRAAx] le one (upperWidth k A R N) :=
  positive_product _ _ (GaussianGammaCompactCutoffGeometry.gap_positive _ _ h) (GaussianGammaIntegralCutoffs.eta_den_positive _ _ _)

theorem exact_upper_endpoint (k A R N : PTm n) (h : Γ ⊢[PRAAx] le (top k A R) N) : Γ ⊢[PRAAx]
    one+(width k A R+upperWidth k A R N) ≐ etaDen k A R*N :=
  (by ipra_ring : Γ ⊢[PRAAx] one+(width k A R+upperWidth k A R N) ≐ (one+width k A R)+upperWidth k A R N).eqTrans
    ((congrAdd (exact_right_endpoint _ _ _) (.eqRefl _)).eqTrans
      ((by unfold upperWidth; ipra_ring : Γ ⊢[PRAAx] etaDen k A R*top k A R+upperWidth k A R N ≐
        etaDen k A R*(top k A R+monus N (top k A R))).eqTrans
          (congrMul (.eqRefl _) (eq_add_of_le h).eqSymm)))

theorem exact_width_sum (k A R N : PTm n) (h : Γ ⊢[PRAAx] le (top k A R) N) : Γ ⊢[PRAAx]
    width k A R+upperWidth k A R N ≐ fullWidth k A R N :=
  ((congrMonus (exact_upper_endpoint _ _ _ _ h).eqSymm (.eqRefl one)).eqTrans (add_monus' _ _)).eqSymm

theorem full_width_positive (k A R N : PTm n) (h : Γ ⊢[PRAAx] le (top k A R) N) : Γ ⊢[PRAAx] le one (fullWidth k A R N) :=
  le_congr (.eqRefl _) (exact_width_sum _ _ _ _ h)
    (le_trans (GaussianGammaCompactCutoffGeometry.width_positive _ _ _) (le_add_right _ _))

theorem original_split (p z R B k A N S : PTm n) (h : Γ ⊢[PRAAx] source z R B k A N S) : Γ ⊢[PRAAx]
    distanceBounded (full p z B k A R N S) (qadd (middle p z B k A R N S) (upper p z B k A R N S))
      (two*fullWidth k A R N) (etaDen k A R*unit p) := by
  let C1 := width k A R
  let C2 := upperWidth k A R N
  let E := etaDen k A R
  let L := GaussianBetaKernelCompactModulus.lipschitz R E N
  let x := sampleDataBeta z B N
  have he := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have hN := degree_positive k A R N h.andE₂.andE₁
  have sourceBeta : Γ ⊢[PRAAx] GaussianBetaKernelCompactModulus.compactSource z R B E N one (C1+C2) N :=
    .andI (.andI h.andE₁.andE₁ (.andI he h.andE₁.andE₂))
      (.andI (.andI hN (le_refl N)) (.andI (le_refl one)
        (le_congr (exact_upper_endpoint _ _ _ _ (le_of_lt h.andE₂.andE₁)).eqSymm (.eqRefl _) (le_refl _))))
  have input : Γ ⊢[PRAAx] GaussianCompactRiemannAdditivity.input evaluatorF one C1 C2 E S L x :=
    .andI (le_refl one) (.andI he (.andI h.andE₂.andE₂
      (.andI (GaussianGammaCompactCutoffGeometry.width_positive _ _ _) (.andI (upper_width_positive _ _ _ _ h.andE₂.andE₁)
        (GaussianBetaKernelCompactModulus.sampled_modulus _ _ _ _ _ _ _ _ sourceBeta)))))
  have sumWidth := exact_width_sum k A R N (le_of_lt h.andE₂.andE₁)
  have atTop := (exact_right_endpoint (Γ := Γ) k A R).eqTrans (mul_comm _ _)
  exact distance_congr
    (GaussianBetaIntegralThreeSplit.quadrature_congr evaluatorF (.eqRefl _) (congrMul sumWidth (.eqRefl _)) (.eqRefl _) sumWidth (.eqRefl _) (.eqRefl _))
    (qadd_congr (.eqRefl _) (GaussianBetaIntegralThreeSplit.quadrature_congr evaluatorF (.eqRefl _) (.eqRefl _) atTop (.eqRefl _) (.eqRefl _) (.eqRefl _)))
    (congrMul (.eqRefl _) sumWidth) (.eqRefl _)
      (GaussianCompactRiemannAdditivity.shared_step_additivity evaluatorF p one C1 C2 E S L x input)

theorem original_coarse_split (p z R B k A N S : PTm n) (h : Γ ⊢[PRAAx] source z R B k A N S) : Γ ⊢[PRAAx]
    distanceBounded (full p z B k A R N S) (qadd (middle p z B k A R N S) (upper p z B k A R N S))
      (two*N) (unit p) :=
  distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (GaussianGammaIntegralCutoffs.eta_den_positive _ _ _) (unit_positive p)) (unit_positive p)
    (le_congr (by unfold fullWidth; ipra_ring) (by ipra_ring)
      (mul_le_mul_right (two*unit p) (GaussianRationalMonicReconstruction.monus_le_left (etaDen k A R*N) one)))
      (original_split p z R B k A N S h)

theorem exact_common_middle_count (q k A R factor : PTm n) : Γ ⊢[PRAAx]
    width k A R*commonMultiplier q k A R factor ≐
      GaussianBetaRefinedFixedCompactComparison.refinedCells q (middleFactor k A R factor) k A R := by
  unfold commonMultiplier middleFactor GaussianBetaRefinedFixedCompactComparison.refinedCells; ipra_ring

theorem middle_is_original_refined_beta (p q factor z R B k A N : PTm n) : Γ ⊢[PRAAx]
    middle p z B k A R N (commonMultiplier q k A R factor) ≐
      GaussianBetaRefinedFixedCompactComparison.refinedBeta p q (middleFactor k A R factor) z R B k A N :=
  GaussianCompactRiemannName.quadrature_index_congr _ _ _ _ _ _ _ _ (exact_common_middle_count _ _ _ _ _)

theorem original_middle_compact_comparison (p q factor z R B k A N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBetaRefinedFixedCompactComparison.source p q factor z R B k A N) : Γ ⊢[PRAAx]
    distanceBounded (middle p z B k A R N (commonMultiplier q k A R factor))
      (GaussianBetaRefinedFixedCompactComparison.compactObservation q z R B k A)
      (GaussianBetaRefinedFixedCompactComparison.numerator p q R k A N)
      (GaussianBetaRefinedFixedCompactComparison.denominator p q k A R N) :=
  distance_congr (middle_is_original_refined_beta _ _ _ _ _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianBetaRefinedFixedCompactComparison.original_refined_beta_comparison p q (middleFactor k A R factor) z R B k A N
      (.andI h.andE₁ (.andI (positive_product _ _ (GaussianGammaCompactCutoffGeometry.width_positive _ _ _) h.andE₂.andE₁)
        h.andE₂.andE₂)))

theorem common_multiplier_positive (q k A R factor : PTm n) (h : Γ ⊢[PRAAx] le one factor) : Γ ⊢[PRAAx]
    le one (commonMultiplier q k A R factor) :=
  positive_product _ _ (GaussianCompactRiemannName.mesh_positive _ _ _) h

theorem source_from_middle_comparison (p q factor z R B k A N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBetaRefinedFixedCompactComparison.source p q factor z R B k A N) : Γ ⊢[PRAAx]
    source z R B k A N (commonMultiplier q k A R factor) := by
  have positive := GaussianGammaIntegralCutoffs.top_positive (Γ := Γ) k A R
  have strict : Γ ⊢[PRAAx] lt (top k A R) (two*top k A R) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (top k A R) positive)
  exact .andI h.andE₁ (.andI (le_trans strict h.andE₂.andE₂.andE₂.andE₂)
    (common_multiplier_positive q k A R factor h.andE₂.andE₁))

theorem exact_upper_tail_endpoint (k A R N : PTm n) (h : Γ ⊢[PRAAx] le (top k A R) N) : Γ ⊢[PRAAx]
    top k A R*etaDen k A R+upperWidth k A R N ≐ etaDen k A R*N :=
  (by unfold upperWidth; ipra_ring : Γ ⊢[PRAAx] top k A R*etaDen k A R+upperWidth k A R N ≐
    etaDen k A R*(top k A R+monus N (top k A R))).eqTrans
      (congrMul (.eqRefl _) (eq_add_of_le h).eqSymm)

theorem original_full_mesh_divisibility (q k A R N M extra : PTm n) : Γ ⊢[PRAAx]
    fullWidth k A R N*commonMultiplier q k A R (M*extra) ≐ (fullWidth k A R N*conservativeCells q k A R*extra)*M := by
  unfold commonMultiplier; ipra_ring

theorem original_fixed_eta_to_N_beta_two_piece_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (full (var 0) (var 1) (var 3) (var 4) (var 5) (var 2) (var 6) (var 7))
        (qadd (middle (var 0) (var 1) (var 3) (var 4) (var 5) (var 2) (var 6) (var 7))
          (upper (var 0) (var 1) (var 3) (var 4) (var 5) (var 2) (var 6) (var 7)))
        (two*fullWidth (var 4) (var 5) (var 2) (var 6)) (etaDen (var 4) (var 5) (var 2)*unit (var 0))) :=
  closeUniv 8 (.impI (original_split _ _ _ _ _ _ _ _ Prf.hyp0))
theorem original_fixed_cutoff_beta_split_coarse_dyadic_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (full (var 0) (var 1) (var 3) (var 4) (var 5) (var 2) (var 6) (var 7))
        (qadd (middle (var 0) (var 1) (var 3) (var 4) (var 5) (var 2) (var 6) (var 7))
          (upper (var 0) (var 1) (var 3) (var 4) (var 5) (var 2) (var 6) (var 7)))
        (two*var 6) (unit (var 0))) := closeUniv 8 (.impI (original_coarse_split _ _ _ _ _ _ _ _ Prf.hyp0))
theorem original_two_piece_middle_is_fixed_compact_Euler_observation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (GaussianBetaRefinedFixedCompactComparison.source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        distanceBounded (middle (var 0) (var 3) (var 5) (var 6) (var 7) (var 4) (var 8) (commonMultiplier (var 1) (var 6) (var 7) (var 4) (var 2)))
          (GaussianBetaRefinedFixedCompactComparison.compactObservation (var 1) (var 3) (var 4) (var 5) (var 6) (var 7))
          (GaussianBetaRefinedFixedCompactComparison.numerator (var 0) (var 1) (var 4) (var 6) (var 7) (var 8))
          (GaussianBetaRefinedFixedCompactComparison.denominator (var 0) (var 1) (var 6) (var 7) (var 4) (var 8))) :=
  closeUniv 9 (.impI (original_middle_compact_comparison _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaFixedCutoffSplit

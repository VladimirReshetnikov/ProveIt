import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteName
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.Normalization.GaussianEulerUnitNormalization
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.Bounds.GaussianEulerUnitEndpointDecay

/-!
# The original upper incomplete Euler integral at parameter one

The actual upper-piece sampler is its original compact quadrature at
its computed rational-interior cutoff. At parameter one the unchanged
Euler evaluator is exactly the decay evaluator. Its finite
antiderivative retains the decay at the original split a/b; only the
external integer endpoint tends to zero. Regularity and a finite gap
then give the independent-precision identity. No Gamma normalization
or incomplete recurrence is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteUnitUpper

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianEulerDecayMesh (observation observation_rescale)
open GaussianEulerIncompleteName (upperF)
open GaussianEulerIncompleteCutoff (clock denominator splitPoint upperWidth)
open GaussianGammaIntegralCutoffs (height etaDen top)
open GaussianEulerCompactModulus (lipschitz)
open GaussianRationalMetric (distanceBounded qsub qnegative bounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent point_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (a b : PTm n) : Fm PTm n := le one a ⋏ le one b
def data (a b : PTm n) : PTm n := GaussianEulerIncompleteName.data oneCode one one one a b
ipra_subst source
ipra_subst data

private theorem subst_decayData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (decayData a b) = decayData (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [decayData,GaussianGammaFiniteApproximantName.exponentialInputData,
    GaussianRadiusExponentialName.subst_data,GaussianNameBounds.subst_U,
    GaussianEulerIntegrandName.subst_decayPoint]

theorem unit_source (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    GaussianEulerIncompleteCofinalRate.source oneCode one one one a b :=
  .andI (.andI GaussianEulerUnitNormalization.unit_lower_source (le_refl one)) h

theorem cutoff_source (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    GaussianEulerIncompleteCutoff.source oneCode one one one a b :=
  .andI GaussianEulerUnitNormalization.unit_lower_source.andE₂.andE₁ (.andI (le_refl one) h)

theorem top_later (t a b : PTm n) : Γ ⊢[PRAAx] le (t+one) (top (clock t a b) one one) := by
  have late := GaussianEulerIncompleteCutoff.clock_later (Γ := Γ) t a b
  have step : Γ ⊢[PRAAx] le (clock t a b+one) (height (clock t a b) one one) :=
    le_of_eq_add (d := GaussianGammaIntegralCutoffs.tailCoefficient one+num 10) (by unfold height; ipra_ring)
  have twice : Γ ⊢[PRAAx] le (height (clock t a b) one one) (top (clock t a b) one one) :=
    le_of_eq_add (d := height (clock t a b) one one) (by unfold top; ipra_ring)
  exact le_trans (add_le_add_right one late) (le_trans step twice)

theorem compact_endpoints (p t a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 GaussianEulerCompactAdditivity.nameF p
        (GaussianEulerIncompleteCutoffParts.upperData oneCode one one (clock t a b) one a b))
      (qsub (observation a b (t+one)) (observation (top (clock t a b) one one) one (t+one)))
      (unit p+unit t) (unit p*unit t) := by
  let k := clock t a b
  let E := etaDen k one one
  let D := denominator k one one b
  let x := splitPoint k one one a
  let C := upperWidth k one one a b
  let T := top k one one
  have hE := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k one one
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ h.andE₂ hE
  have hPiece := (GaussianEulerIncompleteCutoffParts.piece_sources t k oneCode one one one a b
    (cutoff_source a b h) (le_refl k)).andE₂
  have hC := (GaussianEulerIncompleteCutoff.original_partition t k oneCode one one one a b
    (cutoff_source a b h) (le_refl k)).andE₂.andE₂.andE₂.andE₂
  have width : Γ ⊢[PRAAx] le C (D*T) := le_trans (le_add_left C x) hPiece.andE₂.andE₂
  have actual := GaussianEulerUnitNormalizationCompact.original_compact_endpoint p t x C D
    (lipschitz one D T) T zero hPiece.andE₂.andE₁ hC hD
    (GaussianEulerUnitNormalization.lipschitz_positive one D T) width
  have left : Γ ⊢[PRAAx] observation x D (t+one) ≐ observation a b (t+one) :=
    observation_rescale a b E (t+one) h.andE₂ hE
  have endp := GaussianEulerIncompleteCutoffRefinement.early_upper_endpoint t k one one a b
    h.andE₁ h.andE₂ (le_refl one) (le_refl k)
  have prepared : Γ ⊢[PRAAx] observation (x+C) D (t+one) ≐ observation (T*D) (one*D) (t+one) := by
    simpa using Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (observation (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![x+C,D,t+one]) (σ' := ![T*D,one*D,t+one]) (fun i => by
        fin_cases i
        · exact endp.eqTrans (mul_comm _ _)
        · exact (one_mul D).eqSymm
        · exact .eqRefl _)
  have right := prepared.eqTrans (observation_rescale T one D (t+one) (le_refl one) hD)
  exact distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qsub_congr left right)
    (.eqRefl _) (.eqRefl _) actual

theorem endpoint_error (t a b : PTm n) : Γ ⊢[PRAAx]
    distanceBounded
      (qsub (observation a b (t+one)) (observation (top (clock t a b) one one) one (t+one)))
      (observation a b (t+one)) (num 3) (unit (t+one)) := by
  have hp := unit_positive (Γ := Γ) (t+one)
  have small := GaussianEulerUnitEndpointDecay.right_decay_rate (Γ := Γ)
    (top (clock t a b) one one) (t+one) (top_later t a b)
  have neg := GaussianRationalReciprocal.bounded_negative _ _ _ hp small
  have near := (GaussianReconstructionRoots.distance_zero_iff _ _ _ hp).iffMpr neg
  have add := GaussianNameRingLaws.sum_right_error (observation a b (t+one)) _ _ _ _ hp near
  have canon : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (observation a b (t+one)) :=
    GaussianRadiusExponentialName.sample_canonical GaussianGammaCanonicalExponent.constantF _ (t+one)
      (GaussianEulerIntegrandName.decayPoint a b)
  exact distance_congr (.eqRefl _)
    (GaussianReciprocalHorner.qadd_zero_right _ canon) (.eqRefl _) (.eqRefl _) add

theorem original_diagonal (t a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 upperF t (data a b)) (observation a b t) (num 7) (unit t) := by
  let p := GaussianEulerCutoffCauchyComparison.clock t
  have ht := unit_positive (Γ := Γ) t
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) (t+one)
  have later : Γ ⊢[PRAAx] le (unit t) (unit p) :=
    GaussianExponentialReference.unit_monotone (le_add_right t (num 4) : Γ ⊢[PRAAx] le t p)
  have next := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_add_right t one)
  have raw := compact_endpoints p t a b h
  have first := distance_radius_mono _ _ _ _ two (unit t) (positive_product _ _ hp ht) ht
    (le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (unit p*unit t) (mul_le_mul_right (unit t) later))) raw
  have second := distance_radius_mono _ _ _ _ (num 3) (unit t) hq ht
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (num 3) next)) (endpoint_error t a b)
  have shift := point_at (Γ := Γ) decayF (decayData a b) (t+one) t
    (GaussianEulerDecayQuadraturePrecision.observation_regular a b)
  have third := distance_radius_mono _ _ _ _ two (unit t) (positive_product _ _ hq ht) ht
    (le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (unit (t+one)*unit t) (mul_le_mul_right (unit t) next))) shift
  have joined := distance_triangle_same _ _ _ _ _ _ ht
    (distance_triangle_same _ _ _ _ _ _ ht first second) third
  exact distance_congr (GaussianEulerIncompleteName.upper_at t oneCode one one one a b).eqSymm
    (.eqRefl _) (by ipra_ring) (.eqRefl _) joined

theorem original_upper_at_one (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent upperF decayF (data a b) (decayData a b) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 7)
    (GaussianEulerIncompleteName.original_regular_names oneCode one one one a b (unit_source a b h)).andE₂
    (GaussianEulerDecayQuadraturePrecision.observation_regular a b)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift,subst_source,Syn.shift] using h.shift
  have d := original_diagonal (var 0) (Syn.shift a) (Syn.shift b) hs
  change Γ.map Fm.shift ⊢[PRAAx]
    distanceBounded (ap2 upperF (var 0) (Syn.shift (data a b)))
      (ap2 decayF (var 0) (Syn.shift (decayData a b))) (Syn.shift (num 7)) (unit (var 0))
  rw [show Syn.shift (data a b) = data (Syn.shift a) (Syn.shift b) from subst_data _ a b,
    show Syn.shift (decayData a b) = decayData (Syn.shift a) (Syn.shift b) from subst_decayData _ a b,
    show Syn.shift (num 7 : PTm n) = (num 7 : PTm (n+1)) by simp only [Syn.shift,LeanProofs.IPRA.PTm.subst_num]]
  exact d

theorem original_upper_incomplete_Euler_at_one_is_decay_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source (var 0) (var 1) ⟶ crossEquivalent upperF decayF
        (data (var 0) (var 1)) (decayData (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_upper_at_one _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteUnitUpper

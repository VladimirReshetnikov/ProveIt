import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaRecurrenceWeightName
import IPRADerivations.Analysis.Names.GaussianNameEquivalence

/-!
# Original recurrence weights and full original zeta names

At N=0 the actual reconstructed scalar sample is literally the original
zeta sample. C17's original independent reconstruction error therefore
compares every source weight at N with that full weight at zero, with
the exact standard observation budget. The actual PR2 weight names are
cross equivalent, and every high full coefficient is the literal signed
original zeta sample. No equality of limits or recurrence is a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaRecurrenceWeightCompatibility

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianGammaRecurrenceWeights (weight)
open GaussianGammaRecurrenceWeightName (nameF data name_at)
open GaussianCoefficientNameBounds (unit)
open RationalValueBounds (radius)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_reconstructed_zero (p m : PTm n) : Γ ⊢[PRAAx]
    RationalReciprocalPowerName.reconstructedSample p m zero ≐ RationalReciprocalPowerName.zetaSample p m :=
  (RationalReciprocalPowerName.reconstruction_sample_at p m zero).eqTrans
    ((RationalReciprocalPowerName.reconstruction_prefix p m zero).eqSymm.eqTrans
      ((RationalReciprocalPowerName.tail_congr (.eqRefl m) (.eqRefl zero) (zero_add (RationalReciprocalPowerName.cutoff p))).eqTrans
        (RationalReciprocalPowerName.zeta_sample_at p m).eqSymm))

theorem original_scalar_source_full_error (p q N m : PTm n) (hm : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx]
    radius (RationalReciprocalPowerName.reconstructedSample p m N)
      (RationalReciprocalPowerName.reconstructedSample q m zero) (unit p+unit q) (unit p*unit q) :=
  RationalValueBounds.radius_congr (.eqRefl _) (original_reconstructed_zero q m).eqSymm
    (add_comm _ _) (mul_comm _ _)
      (RationalValueBounds.radius_symmetric _ _ _ _ (RationalReciprocalPowerName.reconstruction_error q p m N hm))

theorem original_source_full_error (p q N m : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (weight p N m) (weight q zero m) (unit p+unit q) (unit p*unit q) :=
  GaussianGammaRecurrenceWeightName.from_scalar_error p q N zero m
    (.impI (original_scalar_source_full_error p q N m Prf.hyp0))

theorem original_full_high_weight (p m : PTm n) (hm : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx]
    weight p zero m ≐ qmul (parityPoint (pred m)) (RationalGaussianEmbedding.embed (RationalReciprocalPowerName.zetaSample p m)) :=
  (GaussianGammaRecurrenceWeightName.weight_high p zero m hm).eqTrans
    (qmul_congr (.eqRefl _) (RationalGaussianRealPart.embed_congr (original_reconstructed_zero p m)))

theorem original_source_full_names (N m : PTm n) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent nameF nameF (data N m) (data zero m) := by
  refine .allI (.allI ?_)
  have h := distance_congr (name_at (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1) (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift m))).eqSymm
    (name_at (var 0) zero (Syn.shift (Syn.shift m))).eqSymm (.eqRefl _) (.eqRefl _)
      (original_source_full_error _ _ _ _)
  simpa only [GaussianNameEquivalence.crossEquivalent,GaussianEuclideanPointDistance.unit,
    GaussianCoefficientNameBounds.unit,GaussianGammaRecurrenceWeightName.subst_data,Syn.shift,PTm.subst_zero] using h

theorem original_Gamma_source_weights_full_zeta_independent_observation_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (distanceBounded (weight (var 0) (var 2) (var 3)) (weight (var 1) zero (var 3))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) := closeUniv 4 (original_source_full_error _ _ _ _)

theorem original_Gamma_full_high_weight_is_signed_original_zeta_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le two (var 1) ⟶ weight (var 0) zero (var 1) ≐ qmul (parityPoint (pred (var 1)))
        (RationalGaussianEmbedding.embed (RationalReciprocalPowerName.zetaSample (var 0) (var 1)))) :=
  closeUniv 2 (.impI (original_full_high_weight _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaRecurrenceWeightCompatibility

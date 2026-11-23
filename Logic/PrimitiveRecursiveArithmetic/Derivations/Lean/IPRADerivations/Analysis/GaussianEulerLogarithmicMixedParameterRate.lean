import IPRADerivations.Analysis.GaussianEulerLogarithmicContinuity
import IPRADerivations.Analysis.GaussianEulerLogarithmicImproperInputProperness
import IPRADerivations.Analysis.GaussianNamedRateTransport

/-!
# Uniform variation for independent native representations and certificates

Recover a literal native increment from the canonical difference of the two
given inputs. The uniform shift estimate applies at the first certificate.
Improper properness transports its shifted name to the given second input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicMixedParameterRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicImproperName (data nameF name_regular)
open GaussianEulerLogarithmicContinuity (modulus)
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical qzero)
open GaussianRationalMetric (bounded qsub)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "certificate" => GaussianEulerLowerPowerCoefficients.source
local notation "continuitySource" => GaussianEulerLogarithmicContinuity.source

def difference (z w B D : PTm n) : PTm n := qsub (ofGaussian w D) (ofGaussian z B)
def source (r j z w R S B D A V : PTm n) : Fm PTm n :=
  certificate z R B A ⋏ (certificate w S D V ⋏ bounded (difference z w B D) one (modulus r j R A))
@[simp] theorem subst_difference {m : ℕ} (σ : Fin n → PTm m) (z w B D : PTm n) :
    Syn.subst σ (difference z w B D) = difference (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ B) (Syn.subst σ D) := by
  simp [difference]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (r j z w R S B D A V : PTm n) :
    (source r j z w R S B D A V).subst σ = source (Syn.subst σ r) (Syn.subst σ j)
      (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ R) (Syn.subst σ S) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ A) (Syn.subst σ V) := by simp [source]

theorem native_difference (z w B D : PTm n) : Γ ⊢[PRAAx]
    ofGaussian (rawGaussian (difference z w B D)) (rawDen (difference z w B D)) ≐ difference z w B D :=
  GaussianExponentialReference.recode_fixed _ (GaussianRationalMetric.qsub_canonical _ _)

theorem native_shift (z w B D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] ofGaussian (shifted z B (rawGaussian (difference z w B D)) (rawDen (difference z w B D)))
      (B*rawDen (difference z w B D)) ≐ ofGaussian w D := by
  let Z := ofGaussian z B
  let W := ofGaussian w D
  let δ := difference z w B D
  have Z0 : Γ ⊢[PRAAx] qsub Z qzero ≐ Z := GaussianRationalReconstruction.qsub_zero_right _ (ofGaussian_canonical z B hB)
  have W0 : Γ ⊢[PRAAx] qsub W qzero ≐ W := GaussianRationalReconstruction.qsub_zero_right _ (ofGaussian_canonical w D hD)
  have add := GaussianEulerLogarithmicParameterTaylor.encoded_sum z B (rawGaussian δ) (rawDen δ) hB (raw_den_positive δ)
  exact add.eqTrans ((qadd_congr (.eqRefl Z) (native_difference z w B D)).eqTrans
    ((GaussianReciprocalHorner.qadd_commutative Z δ).eqTrans
      ((qadd_congr (.eqRefl δ) Z0.eqSymm).eqTrans ((GaussianReconstructionRoots.difference_chain W Z qzero).eqTrans W0))))

theorem original_mixed_parameter_rate (r j z w R S B D A V : PTm n)
    (hs : Γ ⊢[PRAAx] source r j z w R S B D A V) : Γ ⊢[PRAAx]
    independentRate nameF nameF (data j w S D V) (data j z R B A) (num 5) (unit r) := by
  let δ := difference z w B D
  let h := rawGaussian δ
  let F := rawDen δ
  let u := shifted z B h F
  have cs : Γ ⊢[PRAAx] continuitySource r j z R B A h F :=
    .andI hs.andE₁ (.andI (raw_den_positive δ)
      (bound_congr (native_difference z w B D).eqSymm (.eqRefl _) (.eqRefl _) hs.andE₂.andE₂))
  have proper := GaussianEulerLogarithmicImproperInputProperness.original_improper_proper j w u S (R+one) D (B*F) V (two*A)
    (.andI hs.andE₂.andE₁ (.andI (GaussianEulerLogarithmicContinuity.shifted_certificate r j z R B A h F cs)
      (native_shift z w B D hs.andE₁.andE₂.andE₁.andE₁ hs.andE₂.andE₁.andE₂.andE₁.andE₁).eqSymm))
  exact GaussianNamedRateTransport.transport nameF nameF nameF nameF (data j u (R+one) (B*F) (two*A)) (data j z R B A)
    (data j w S D V) (data j z R B A) (num 5) (unit r) (unit_positive r)
    (GaussianEulerLogarithmicContinuity.original_parameter_rate r j z R B A h F cs) proper
    (GaussianNameEquivalence.cross_refl nameF (data j z R B A) (name_regular j z R B A hs.andE₁))

theorem actual_original_mixed_logarithmic_parameter_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      independentRate nameF nameF (data (var 1) (var 3) (var 5) (var 7) (var 9))
        (data (var 1) (var 2) (var 4) (var 6) (var 8)) (num 5) (unit (var 0))) :=
  closeUniv 10 (.impI (original_mixed_parameter_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicMixedParameterRate

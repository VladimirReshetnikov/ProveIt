import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGamma
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate

/-!
# The original named Gamma at any sufficiently late rational input

The frozen input query only meets the supplied margin and continuity
demand. It need not follow the requested output clock. Actual named
regularity and one finite rational gap remove the auxiliary clock used
to compare with this fixed decoded input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaLateInput

open_ipra
open GaussianNamedRightHalfPlane (source threshold radius numerator denominator actual_late_source)
open GaussianGammaHalfPlaneInputContinuity (modulus original_gamma_observations)
open GaussianNamedGamma (nameF data sample clock clock_margin clock_demand name_at name_regular input_observations)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def encodedData (f : PR 2) (r x A : PTm n) : PTm n :=
  gammaData (numerator f r x) (radius f x) (denominator f r x) (two*A)
def input (f : PR 2) (s r x A : PTm n) : Fm PTm n := source f x A ⋏
  (le (threshold A) r ⋏ le (succ (modulus s (radius f x) (two*A))) r)
ipra_subst encodedData
ipra_subst input [GaussianNamedRightHalfPlane.threshold, GaussianNamedRightHalfPlane.precision]

theorem encoded_source (f : PR 2) (s r x A : PTm n) (h : Γ ⊢[PRAAx] input f s r x A) : Γ ⊢[PRAAx]
    GaussianGammaHalfPlaneInputContinuity.source (numerator f r x) (radius f x) (denominator f r x) (two*A) :=
  .andI (actual_late_source f x A r h.andE₁ h.andE₂.andE₁) (GaussianNameBounds.U_positive f x)

theorem encoded_regular (f : PR 2) (s r x A : PTm n) (h : Γ ⊢[PRAAx] input f s r x A) : Γ ⊢[PRAAx]
    pointCN gammaF (encodedData f r x A) :=
  GaussianGammaReciprocalInverse.gamma_regular _ _ _ one (two*A)
    (GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _ (encoded_source f s r x A h))

theorem sample_step (f : PR 2) (u q s r x A : PTm n) (h : Γ ⊢[PRAAx] input f s r x A)
    (hs : Γ ⊢[PRAAx] le s (succ u)) : Γ ⊢[PRAAx]
    distanceBounded (sample f u x A) (ap2 gammaF q (encodedData f r x A))
      (rateNumerator one (unit s) (succ u) q) (rateDenominator (unit s) (succ u) q) := by
  have close := input_observations f x (clock f u x A) r (modulus s (radius f x) (two*A))
    h.andE₁.andE₁ (clock_demand f u x A s hs) h.andE₂.andE₂
  have left : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source
      (numerator f (clock f u x A) x) (radius f x) (denominator f (clock f u x A) x) (two*A) :=
    .andI (actual_late_source f x A _ h.andE₁ (clock_margin f u x A)) (GaussianNameBounds.U_positive f x)
  exact original_gamma_observations (succ u) q s _ _ _ _ _ _ left (encoded_source f s r x A h) close

theorem diagonal_distance (f : PR 2) (t s r x A : PTm n) (h : Γ ⊢[PRAAx] input f s r x A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) t (data x A)) (ap2 gammaF t (encodedData f r x A))
      (GaussianNamedLipschitzRate.diagonalNumerator one (unit s) (num 4) t)
      (GaussianNamedLipschitzRate.diagonalDenominator (unit s) t) := by
  let u := s+t
  let D := unit s*unit t
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) (unit_positive _)
  have later : Γ ⊢[PRAAx] le t u := le_add_left t s
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) later
  have grow' := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_trans later (le_succ_self u))
  have actual := GaussianNameEquivalence.point_at (nameF f) (data x A) t u (name_regular f x A h.andE₁)
  have left := distance_radius_mono _ _ _ _ (two*unit s) D
    (positive_product _ _ (unit_positive _) (unit_positive _)) hD
    (by dsimp only [D]; ipra_le (𝔞(unit s)*𝔞(unit t))*sl grow)
    (distance_congr (.eqRefl _) (name_at f u x A) (.eqRefl _) (.eqRefl _) actual)
  have step := sample_step f u t s r x A h (le_trans (le_add_right s t) (le_succ_self u))
  have right := distance_radius_mono _ _ _ _ (unit t+two*unit s) D
    (GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive s)) hD
    (by unfold rateNumerator rateDenominator; dsimp only [D]; ipra_le (𝔞(unit s)*𝔞(unit s)*𝔞(unit t))*sl grow') step
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNamedLipschitzRate.diagonalNumerator; ipra_ring)
    (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ hD left right)

theorem diagonal_envelope (f : PR 2) (s r x A : PTm n) (h : Γ ⊢[PRAAx] input f s r x A) : Γ ⊢[PRAAx]
    GaussianNamedLipschitzRate.diagonalEnvelope (nameF f) gammaF (data x A) (encodedData f r x A) one (unit s) (num 4) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift s) (Syn.shift r) (Syn.shift x) (Syn.shift A) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,subst_encodedData,GaussianNamedGamma.subst_data,
    GaussianCoefficientNameBounds.subst_unit,one,LeanProofs.IPRA.PTm.subst_num,Syn.shift,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      diagonal_distance f (var 0) (Syn.shift s) (Syn.shift r) (Syn.shift x) (Syn.shift A) hs

theorem original_independent_rate (f : PR 2) (s r x A : PTm n) (h : Γ ⊢[PRAAx] input f s r x A) : Γ ⊢[PRAAx]
    independentRate (nameF f) gammaF (data x A) (encodedData f r x A) one (unit s) :=
  GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 4) (unit_positive s)
    (name_regular f x A h.andE₁) (encoded_regular f s r x A h) (diagonal_envelope f s r x A h)

theorem original_observations (f : PR 2) (p q s r x A : PTm n) (h : Γ ⊢[PRAAx] input f s r x A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data x A)) (ap2 gammaF q (encodedData f r x A))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_independent_rate f s r x A h)

theorem original_named_Gamma_arbitrary_late_input_rate_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input f (var 0) (var 1) (var 2) (var 3) ⟶
      independentRate (nameF f) gammaF (data (var 2) (var 3))
        (encodedData f (var 1) (var 2) (var 3)) one (unit (var 0))) :=
  closeUniv 4 (.impI (original_independent_rate f _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaLateInput

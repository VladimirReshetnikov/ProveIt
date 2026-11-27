import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmName
import IPRADerivations.Analysis.Series.Harmonic.RationalHarmonicIntervalVariation

/-!
# The original logarithm is bounded by its positive time above one

The actual finite harmonic interval is bounded by a/b on b<=a, directly
from the original harmonic rectangle inequality. Its actual native
factorial representation supplies the Euclidean bound. Independent
comparison with the unchanged logarithm and one finite gap then leave
only that logarithm observation's requested dyadic allowance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianUpperTimeLogarithmBound

open_ipra
open RationalHarmonicInterval (interval horizon numerator)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (represents represents_congr positive_product)
open GaussianRationalReciprocal (bound_congr)
open RationalGaussianEmbedding (embed native)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (source sample)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

/-- The actual finite harmonic numerator needs no analytic error term. -/
theorem finite_interval_bound (a b Q : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hQ : Γ ⊢[PRAAx] le one Q) (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    bounded (embed (interval a b Q)) a b := by
  let L := horizon a b Q
  let F := fact L
  let u := Q*a
  let v := Q*b
  let d := monus (S u F) (S v F)
  have vu : Γ ⊢[PRAAx] le v u := le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right Q hba)
  have mono := AnalyticNumberTheory.HarmonicChebyshev.S_mono (Γ := Γ) F vu
  have equation := natEq (eq_add_of_le mono)
  have increment := RationalHarmonicIntervalVariation.harmonic_increment u v F vu
  have weak := le_trans increment (add_le_add₂ (le_refl (v*S v F))
    (mul_le_mul_right F (GaussianRationalMonicReconstruction.monus_le_left u v)))
  have delta : Γ ⊢[PRAAx] le (v*d) (u*F) := by
    dsimp only [d]
    ipra_le sl weak with 𝔞 v*equation
  have clear : Γ ⊢[PRAAx] le (b*d) (a*F) := RationalValueBounds.positive_cancel hQ
    (le_congr (by dsimp only [u,v]; ipra_ring) (by dsimp only [u,v]; ipra_ring) delta)
  have old := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (interval a b Q) (numerator a b Q L) F
    (RationalHarmonicInterval.common_value a b Q L)
  have rep : Γ ⊢[PRAAx] represents (embed (interval a b Q))
      (ComplexLogarithmRemainder.scale d ComplexLogarithmRemainder.oneCode) F := by
    apply represents_congr (.eqRefl _) ?_ (.eqRefl _) old
    apply GaussianRootAlgebra.equal_of_values
    · simp only [native,ComplexLogarithmRemainder.eval_re_code,
        GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
      simp only [numerator,ZT.toZ]
      dsimp only [d,u,v,F,L] at equation ⊢
      ipra_simps
      linear_combination equation
    · simp only [native,ComplexLogarithmRemainder.eval_im_code,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one,
        ZT.toZ_ofNat]
      ipra_simps
      ring
  apply GaussianRationalMetric.bounded_of_cleared _ _ F a b (GammaEulerMesh.factorial_positive L) hb rep
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (ComplexLogarithmRemainder.scale d ComplexLogarithmRemainder.oneCode) ≐ d*d :=
    (ComplexLogarithmRemainder.normSq_scale (Γ := Γ) d ComplexLogarithmRemainder.oneCode).eqTrans
    ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  exact le_congr ((congrMul (.eqRefl _) norm).eqTrans (by ipra_ring)).eqSymm (by ipra_ring) (sq_le_sq clear)

theorem harmonic_sample_bound (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    bounded (GaussianHarmonicLogarithmName.sample p a b) a b :=
  bound_congr (GaussianHarmonicLogarithmName.sample_at p a b).eqSymm (.eqRefl _) (.eqRefl _)
    (finite_interval_bound a b _ hb (GammaEulerConstantName.mesh_positive _) hba)

theorem original_slack (p q a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (sample p a b) (a*unit p+b) (b*unit p) one q := by
  have old := GaussianHarmonicLogarithmName.independent_original p q a b hs
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ a b
    (positive_product _ _ (unit_positive p) (unit_positive q)) hs.andE₂ old (harmonic_sample_bound q a b hs.andE₂ hba)
  exact bound_congr (.eqRefl _) (by dsimp only [unit]; ipra_ring) (by dsimp only [unit]; ipra_ring) raw

/-- The value is the unchanged original positive-rational logarithm
observation. The only error is its original requested dyadic. -/
theorem original_sample_bound (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    bounded (sample p a b) (a*unit p+b) (b*unit p) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ one
    (positive_product _ _ hs.andE₂ (unit_positive p)) (original_slack p _ a b hs hba)

theorem actual_finite_harmonic_interval_upper_time_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 1) ⋏ le one (var 2) ⋏ le (var 1) (var 0)) ⟶ bounded (embed (interval (var 0) (var 1) (var 2))) (var 0) (var 1)) :=
  closeUniv 3 (.impI (finite_interval_bound _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem actual_original_logarithm_upper_time_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((source (var 1) (var 2) ⋏ le (var 2) (var 1)) ⟶
      bounded (sample (var 0) (var 1) (var 2)) (var 1*unit (var 0)+var 2) (var 2*unit (var 0))) :=
  closeUniv 3 (.impI (original_sample_bound _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianUpperTimeLogarithmBound

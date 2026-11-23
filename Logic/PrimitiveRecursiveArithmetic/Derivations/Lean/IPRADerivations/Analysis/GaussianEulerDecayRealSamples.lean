import IPRADerivations.Analysis.GaussianEulerIntegrandName
import IPRADerivations.Analysis.GaussianNameConjugation
import IPRADerivations.Analysis.GaussianGammaRealValues

/-!
# Exact reality of the original rational decay observations

The original fixed-radius exponential sampler evaluates a finite scalar
Taylor sum of the literal constant negative real fraction. Conjugation
therefore fixes each original observation exactly. Its actual raw L1
numerator has square equal to the Euclidean squared norm of that same
raw numerator. No sign claim about negative Taylor partial sums is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayRealSamples

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianRationalConjugation (point point_congr point_represents)
open GaussianRationalHorner (represents represents_congr canonical canonical_unique canonical_congr)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalReciprocal (conjugate)
open GaussianRationalMetric (bounded)
open ComplexLogarithmRemainder (re im normSq)
open GaussianL1 (norm1)
open RationalGaussianEmbedding (embed axis native)
open GaussianGammaCanonicalExponent (constantF constant_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def observation (p a b : PTm n) : PTm n := ap2 decayF p (decayData a b)
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (p a b : PTm n) :
    Syn.subst σ (observation p a b) = observation (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [observation,decayData,GaussianGammaFiniteApproximantName.exponentialInputData]

theorem fixed_raw_imaginary_zero (q : PTm n) (h : Γ ⊢[PRAAx] point q ≐ q) : Γ ⊢[PRAAx]
    ZT.eq (im (rawGaussian q)) (ZT.ofNat zero) := by
  have other := represents_congr h (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
    (point_represents q (rawGaussian q) (rawDen q) (raw_den_positive q) (raw_represents q))
  have same := GaussianReciprocalHorner.numerator_unique q (rawGaussian q) (conjugate (rawGaussian q)) (rawDen q)
    (raw_represents q) other
  have eq := GaussianRootAlgebra.equal_im same
  simp only [GaussianRationalReciprocal.im_conjugate] at eq
  apply RationalNormalForm.positive_integer_cancel two _ _ (le_succ_self one)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  linear_combination eq

theorem fixed_axis_embedding (q : PTm n) (h : Γ ⊢[PRAAx] point q ≐ q) : Γ ⊢[PRAAx]
    embed (fstT q) ≐ q := by
  have imZero := fixed_raw_imaginary_zero q h
  have realValue : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (rawGaussian q) (native (re (rawGaussian q))) := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [native,ComplexLogarithmRemainder.eval_re_code]
    · simpa only [native,ComplexLogarithmRemainder.eval_im_code] using ZT.toZ_eq imZero
  exact canonical_unique _ _ _ (rawDen q) (RationalGaussianEmbedding.embed_canonical _)
    (canonical_congr h.eqSymm (GaussianRationalConjugation.point_canonical q)) (raw_den_positive q)
    (GaussianGammaRealValues.projection_represents q (rawGaussian q) (rawDen q) (raw_represents q))
    (represents_congr (.eqRefl _) realValue (.eqRefl _) (raw_represents q))

/-- For an exactly real raw Gaussian value, its literal L1 numerator
is exactly its Euclidean absolute numerator, expressed without a root. -/
theorem fixed_norm_square (q : PTm n) (h : Γ ⊢[PRAAx] point q ≐ q) : Γ ⊢[PRAAx]
    norm1 (rawGaussian q)*norm1 (rawGaussian q) ≐ normSq (rawGaussian q) := by
  have imZero := fixed_raw_imaginary_zero q h
  have absZero := (Foundations.GapDecision.zabs_congr (ZT.toZ_eq imZero)).eqTrans (GaussianL1.abs_ofNat zero)
  have absEq := natEq absZero
  have square := Foundations.GapDecision.zabs_sq (Γ := Γ) (re (rawGaussian q))
  have imEq := ZT.toZ_eq imZero
  apply deriveNat
  dsimp only [norm1]
  ipra_simps
  rw [absEq,ComplexLogarithmRemainder.normSq_eval,imEq]
  linear_combination square

theorem fixed_bound_iff_raw_radius (q X Y : PTm n)
    (h : Γ ⊢[PRAAx] point q ≐ q) (hY : Γ ⊢[PRAAx] le one Y) : Γ ⊢[PRAAx]
    Fm.iff (bounded q X Y) (le (Y*norm1 (rawGaussian q)) (X*rawDen q)) := by
  have eq := fixed_norm_square q h
  have lhs : Γ ⊢[PRAAx] (Y*Y)*normSq (rawGaussian q) ≐
      (Y*norm1 (rawGaussian q))*(Y*norm1 (rawGaussian q)) :=
    (congrMul (.eqRefl _) eq.eqSymm).eqTrans (by ipra_ring)
  have rhs : Γ ⊢[PRAAx] (X*X)*(rawDen q*rawDen q) ≐ (X*rawDen q)*(X*rawDen q) := by ipra_ring
  refine .andI (.impI ?_) (.impI ?_)
  · exact nat_sqrt_mono (le_congr lhs.wk rhs.wk
      (GaussianRationalMetric.bounded_to_cleared q (rawGaussian q) (rawDen q) X Y
        (raw_den_positive q) hY.wk (raw_represents q) Prf.hyp0))
  · exact GaussianRationalMetric.bounded_of_cleared q (rawGaussian q) (rawDen q) X Y
      (raw_den_positive q) hY.wk (raw_represents q)
      (le_congr lhs.eqSymm.wk rhs.eqSymm.wk (sq_le_sq Prf.hyp0))

theorem fixed_scalar_norm_square (q : PTm n) (h : Γ ⊢[PRAAx] point q ≐ q) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qnormSq q ≐
      RationalArithmetic.multiply (GaussianRationalL1.qL1 q) (GaussianRationalL1.qL1 q) := by
  have hd := raw_den_positive (Γ := Γ) q
  have rep := GaussianRationalL1.qL1_represents q (rawGaussian q) (rawDen q) hd (raw_represents q)
  have square := RationalRepresentations.represents_multiply _ _ _ _ _ _ rep rep
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (GaussianRationalMetric.qnormSq_canonical q)
    (RationalArithmetic.multiply_guard _ _) (GaussianRationalMetric.qnormSq_represents q (rawGaussian q) (rawDen q) hd (raw_represents q))
    square (GaussianRationalHorner.positive_product _ _ hd hd) (GaussianRationalHorner.positive_product _ _ hd hd)
  apply ZT.derive
  have eq := natEq (fixed_norm_square q h)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  linear_combination -(Groth.ι (IPRA.Q.mk Γ (rawDen q)))^2*eq

theorem decay_point_fixed (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    point (decayPoint a b) ≐ decayPoint a b := by
  let g := ComplexLogarithmRemainder.neg (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode)
  have rep : Γ ⊢[PRAAx] represents (decayPoint a b) g b :=
    GaussianRationalMetric.qnegative_represents _ _ _ (GaussianRationalHorner.ofGaussian_represents _ _ hb)
  have fixed : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (conjugate g) g := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [GaussianRationalReciprocal.re_conjugate]
    · simp only [GaussianRationalReciprocal.im_conjugate,g,GaussianRootAlgebra.im_neg,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.im_one]
      ring
  exact canonical_unique _ _ g b (GaussianRationalConjugation.point_canonical _)
    (GaussianRationalMetric.qnegative_canonical _) hb
    (represents_congr (.eqRefl _) fixed (.eqRefl _) (point_represents _ _ _ hb rep)) rep

theorem original_observation_at (p a b : PTm n) : Γ ⊢[PRAAx]
    observation p a b ≐ GaussianRationalPolynomialExponential.scalarSum (decayPoint a b)
      (GaussianRadiusExponentialName.index (GaussianNameBounds.U constantF (decayPoint a b)) p) :=
  (GaussianRadiusExponentialName.sample_at constantF (GaussianNameBounds.U constantF (decayPoint a b)) p (decayPoint a b)).eqTrans
    (GaussianNameConjugation.scalar_sum_congr _ (constant_at _ _))

theorem original_observation_fixed (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    point (observation p a b) ≐ observation p a b :=
  (point_congr (original_observation_at p a b)).eqTrans
    ((GaussianRationalConjugation.point_scalar_sum _ _).eqTrans
      ((GaussianNameConjugation.scalar_sum_congr _ (decay_point_fixed a b hb)).eqTrans (original_observation_at p a b).eqSymm))

theorem original_observation_real (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    embed (fstT (observation p a b)) ≐ observation p a b :=
  fixed_axis_embedding _ (original_observation_fixed p a b hb)
theorem original_observation_axis (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    axis (observation p a b) :=
  RationalGaussianEmbedding.axis_congr (original_observation_real p a b hb) (RationalGaussianEmbedding.embed_axis _)
theorem original_observation_imaginary_zero (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    sndT (observation p a b) ≐ RationalGaussianEmbedding.scalarZero :=
  ((congrSnd (original_observation_real p a b hb)).eqSymm).eqTrans (snd_pair _ _)
theorem original_observation_norm_square (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    norm1 (rawGaussian (observation p a b))*norm1 (rawGaussian (observation p a b)) ≐ normSq (rawGaussian (observation p a b)) :=
  fixed_norm_square _ (original_observation_fixed p a b hb)
theorem original_observation_bound_iff (p a b X Y : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hY : Γ ⊢[PRAAx] le one Y) : Γ ⊢[PRAAx]
    Fm.iff (bounded (observation p a b) X Y)
      (le (Y*norm1 (rawGaussian (observation p a b))) (X*rawDen (observation p a b))) :=
  fixed_bound_iff_raw_radius _ X Y (original_observation_fixed p a b hb) hY
theorem original_observation_scalar_norm_square (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qnormSq (observation p a b) ≐
      RationalArithmetic.multiply (GaussianRationalL1.qL1 (observation p a b)) (GaussianRationalL1.qL1 (observation p a b)) :=
  fixed_scalar_norm_square _ (original_observation_fixed p a b hb)

theorem original_decay_each_sample_exactly_real_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ (embed (fstT (observation (var 0) (var 1) (var 2))) ≐ observation (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_observation_real _ _ _ Prf.hyp0))
theorem original_decay_raw_L1_is_exact_absolute_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ norm1 (rawGaussian (observation (var 0) (var 1) (var 2)))*
      norm1 (rawGaussian (observation (var 0) (var 1) (var 2))) ≐ normSq (rawGaussian (observation (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (original_observation_norm_square _ _ _ Prf.hyp0))
theorem original_decay_exact_Euclidean_raw_L1_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 2) ⋏ le one (var 4)) ⟶
      Fm.iff (bounded (observation (var 0) (var 1) (var 2)) (var 3) (var 4))
        (le ((var 4)*norm1 (rawGaussian (observation (var 0) (var 1) (var 2))))
          ((var 3)*rawDen (observation (var 0) (var 1) (var 2))))) :=
  closeUniv 5 (.impI (original_observation_bound_iff _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayRealSamples

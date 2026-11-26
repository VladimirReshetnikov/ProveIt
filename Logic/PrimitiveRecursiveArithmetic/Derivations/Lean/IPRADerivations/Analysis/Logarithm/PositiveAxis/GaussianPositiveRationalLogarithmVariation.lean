import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmProperness
import IPRADerivations.Analysis.Series.Harmonic.RationalHarmonicIntervalVariation
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate

/-!
# Original positive-rational logarithm variation

The original scalar time-distance is reflected to its actual natural
cross numerator. Existing finite harmonic interval variation then
controls unchanged logarithm observations at a shared numerical clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmVariation

open_ipra
open GaussianPositiveRationalLogarithm (source sample logF data name_regular)
open GaussianPositiveRationalLogarithmProperness (sample_interval_error)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalHarmonicIntervalVariation (gap)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def time (a b : PTm n) : PTm n := RationalCubeMidpoint.fraction a b
def native (a : PTm n) : PTm n := RationalGaussianEmbedding.native (ZT.ofNat a)
def crossNumerator (a b c d : PTm n) : PTm n := GaussianRootAlgebra.sub
  (ComplexLogarithmRemainder.scale d (native a)) (ComplexLogarithmRemainder.scale b (native c))

theorem cross_norm (a b c d : PTm n) : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (crossNumerator a b c d) ≐
    gap a b c d*gap a b c d := by
  have absolute := natEq (Probability.Variance.ad_sq (Γ := Γ) (a*d) (b*c))
  apply deriveNat
  rw [ComplexLogarithmRemainder.normSq_eval]
  simp only [crossNumerator,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
    GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale]
  simp only [native,RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code]
  simp only [ZT.toZ_ofNat]
  simp only [gap,Probability.Variance.ad] at absolute ⊢
  ipra_simps
  linear_combination -absolute

/-- Reflect the actual original scalar rational distance, preserving both
positive original denominators and its exact numerator tolerance. -/
theorem original_time_distance (a b c d A D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] RationalValueBounds.radius (time a b) (time c d) A D) : Γ ⊢[PRAAx]
    le (D*gap a b c d) (A*b*d) := by
  let q := RationalGaussianEmbedding.embed (time a b)
  let r := RationalGaussianEmbedding.embed (time c d)
  let E := b*d
  have e := positive_product (Γ := Γ) _ _ hb hd
  have left := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (time a b) (ZT.ofNat a) b
    (RationalCubeMidpoint.fraction_represents a b hb)
  have right := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (time c d) (ZT.ofNat c) d
    (RationalCubeMidpoint.fraction_represents c d hd)
  have l := GaussianRationalSyntheticDivision.rescale_to q (native a) b d E left (.eqRefl _)
  have rr := GaussianRationalSyntheticDivision.rescale_to r (native c) d b E right (mul_comm _ _)
  have metric := RationalGaussianNameEmbedding.distance_from_radius (time a b) (time c d) A D hD h
  have clear := (GaussianRationalMetric.bounded_difference_iff q r
    (ComplexLogarithmRemainder.scale d (native a)) (ComplexLogarithmRemainder.scale b (native c)) E A D e hD l rr).iffMp metric
  have square : Γ ⊢[PRAAx] le ((D*gap a b c d)*(D*gap a b c d)) ((A*b*d)*(A*b*d)) :=
    le_congr ((congrMul (.eqRefl (D*D)) (cross_norm (Γ := Γ) a b c d)).eqTrans (by ipra_ring))
      (by dsimp [E]; ipra_ring) clear
  exact nat_sqrt_mono square

/-- Original observation errors and the exact finite relative-time
estimate give this actual shared-clock bound, with coefficient 17. -/
theorem diagonal_native (p a b c d M A D : PTm n)
    (hab : Γ ⊢[PRAAx] source a b) (hcd : Γ ⊢[PRAAx] source c d) (hD : Γ ⊢[PRAAx] le one D)
    (hl : Γ ⊢[PRAAx] le b (M*a)) (hr : Γ ⊢[PRAAx] le d (M*c))
    (hclose : Γ ⊢[PRAAx] le (D*gap a b c d) (A*b*d)) : Γ ⊢[PRAAx]
    distanceBounded (sample p a b) (sample p c d) ((M*A)*unit p+num 17*D) (D*unit p) := by
  let Q := GammaEulerConstantName.mesh p
  have hQ := GammaEulerConstantName.mesh_positive (Γ := Γ) p
  have den := positive_product _ _ hD (unit_positive p)
  have old := RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ (positive_product _ _ hD hQ)
    (RationalHarmonicIntervalVariation.finite_variation a b c d Q M A D hab.andE₁ hab.andE₂ hcd.andE₁ hcd.andE₂ hQ hD hl hr hclose)
  have middle : Γ ⊢[PRAAx] distanceBounded
      (RationalGaussianEmbedding.embed (RationalHarmonicInterval.interval a b Q))
      (RationalGaussianEmbedding.embed (RationalHarmonicInterval.interval c d Q)) ((M*A)*unit p+D) (D*unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hD hQ) den
      (le_of_eq_add (d := two*D*D*unit p) (by
        dsimp [Q,GammaEulerConstantName.mesh,GammaEulerConstantName.unit,unit]; ipra_ring)) old
  have left := distance_radius_mono _ _ _ _ (num 8*D) (D*unit p) (unit_positive p) den
    (le_of_eq_add (d := zero) (by ipra_ring)) (sample_interval_error p a b hab)
  have right := distance_radius_mono _ _ _ _ (num 8*D) (D*unit p) (unit_positive p) den
    (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_symmetric _ _ _ _ (unit_positive p) (sample_interval_error p c d hcd))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den (distance_triangle_same _ _ _ _ _ _ den left middle) right)



def input (a b c d M A D : PTm n) : Fm PTm n := source a b ⋏ (source c d ⋏ (le one D ⋏
  (le b (M*a) ⋏ (le d (M*c) ⋏ RationalValueBounds.radius (time a b) (time c d) A D))))
ipra_subst time
ipra_subst input

theorem diagonal (p a b c d M A D : PTm n) (h : Γ ⊢[PRAAx] input a b c d M A D) : Γ ⊢[PRAAx]
    distanceBounded (sample p a b) (sample p c d) ((M*A)*unit p+num 17*D) (D*unit p) :=
  diagonal_native p a b c d M A D h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₁
    (original_time_distance a b c d A D h.andE₁.andE₂ h.andE₂.andE₁.andE₂ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂)

theorem diagonal_envelope (a b c d M A D : PTm n) (h : Γ ⊢[PRAAx] input a b c d M A D) : Γ ⊢[PRAAx]
    GaussianNamedLipschitzRate.diagonalEnvelope logF logF (data a b) (data c d) (M*A) D (num 17) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d)
      (Syn.shift M) (Syn.shift A) (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,sample,GaussianPositiveRationalLogarithm.subst_data,
    PTm.subst_mul,PTm.subst_num,Syn.shift] using diagonal (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d)
      (Syn.shift M) (Syn.shift A) (Syn.shift D) hs

/-- The original unchanged log evaluator has exact Lipschitz constant M
on positive times at least 1/M, with only ordinary observation errors. -/
theorem original_independent_rate (a b c d M A D : PTm n) (h : Γ ⊢[PRAAx] input a b c d M A D) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.independentRate logF logF (data a b) (data c d) (M*A) D :=
  GaussianNamedLipschitzRate.independent_rate logF logF (data a b) (data c d) (M*A) D (num 17) h.andE₂.andE₂.andE₁
    (name_regular a b h.andE₁) (name_regular c d h.andE₂.andE₁) (diagonal_envelope a b c d M A D h)

theorem original_observations (p q a b c d M A D : PTm n) (h : Γ ⊢[PRAAx] input a b c d M A D) : Γ ⊢[PRAAx]
    distanceBounded (sample p a b) (sample q c d) (GaussianNamedInverseRate.rateNumerator (M*A) D p q)
      (GaussianNamedInverseRate.rateDenominator D p q) :=
  GaussianNamedInverseRate.rate_at logF logF (data a b) (data c d) (M*A) D p q (original_independent_rate a b c d M A D h)

theorem original_positive_time_distance_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 1) ⋏ (le one (var 3) ⋏ (le one (var 5) ⋏
      RationalValueBounds.radius (time (var 0) (var 1)) (time (var 2) (var 3)) (var 4) (var 5)))) ⟶
        le (var 5*gap (var 0) (var 1) (var 2) (var 3)) (var 4*var 1*var 3)) :=
  closeUniv 6 (.impI (original_time_distance _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_original_logarithm_diagonal_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (sample (var 0) (var 1) (var 2)) (sample (var 0) (var 3) (var 4))
        ((var 5*var 6)*unit (var 0)+num 17*var 7) (var 7*unit (var 0))) :=
  closeUniv 8 (.impI (diagonal _ _ _ _ _ _ _ _ Prf.hyp0))
theorem original_positive_rational_logarithm_independent_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      GaussianNamedInverseRate.independentRate logF logF (data (var 0) (var 1)) (data (var 2) (var 3)) (var 4*var 5) (var 6)) :=
  closeUniv 7 (.impI (original_independent_rate _ _ _ _ _ _ _ Prf.hyp0))
theorem original_positive_rational_logarithm_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (sample (var 0) (var 2) (var 3)) (sample (var 1) (var 4) (var 5))
        (GaussianNamedInverseRate.rateNumerator (var 6*var 7) (var 8) (var 0) (var 1))
        (GaussianNamedInverseRate.rateDenominator (var 8) (var 0) (var 1))) :=
  closeUniv 9 (.impI (original_observations _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmVariation

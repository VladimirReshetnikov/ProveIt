import IPRADerivations.Analysis.Beta.CompactKernels.Factors.GaussianBetaKernelLogarithm
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianNamedPositiveExponentialOrder
import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumIntervals

/-!
# Signed remainder of the unchanged beta logarithm

At a native negative real input, the actual cubic Taylor numerator is
exactly the negative of its positive majorant. Thus every original
finite logarithm is below its linear term. The unchanged natural-scale
observation has only its genuine requested dyadic allowance; the old
quadratic norm estimate is retained separately.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelSignedLogarithm

open_ipra
open GaussianBetaKernelLogarithm (negativeNumerator target source localData observation)
open ComplexLogarithmRemainder (re im scale oneCode series)
open GaussianRootAlgebra (equal equal_of_values equal_re equal_im values_of_code re_scale im_scale re_one im_one re_zero im_zero re_neg im_neg re_mul im_mul re_add im_add)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product)
open GaussianRationalNaturalScale (natScale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def positivePowerLaw (a j : PTm n) : Fm PTm n :=
  equal (ComplexLogarithmRemainder.power (ComplexLogarithmRemainder.neg (negativeNumerator a)) j)
    (scale (pw a j) oneCode)
ipra_subst positivePowerLaw

theorem positive_power_zero (a : PTm n) : Γ ⊢[PRAAx] positivePowerLaw a zero := by
  have h := values_of_code (ComplexLogarithmRemainder.power_zero (Γ := Γ) (ComplexLogarithmRemainder.neg (negativeNumerator a)))
  apply equal_of_values
  · rw [h.1]; simp only [re_scale,re_one,natEq (pw_zero (Γ := Γ) a),Q.mk_one,map_one]; ring
  · rw [h.2]; simp only [im_scale,im_one]; ring

theorem positive_power_step (a j : PTm n) (ih : Γ ⊢[PRAAx] positivePowerLaw a j) : Γ ⊢[PRAAx]
    positivePowerLaw a (succ j) := by
  have h := values_of_code (ComplexLogarithmRemainder.power_succ (Γ := Γ) (ComplexLogarithmRemainder.neg (negativeNumerator a)) j)
  have hr := equal_re ih
  have hi := equal_im ih
  apply equal_of_values
  · rw [h.1,re_mul,hr,hi]
    simp only [negativeNumerator,re_neg,im_neg,re_scale,im_scale,re_one,im_one]
    rw [natEq (pw_succ (Γ := Γ) a j)]; ipra_simps; ring
  · rw [h.2,im_mul,hr,hi]
    simp only [negativeNumerator,re_neg,im_neg,re_scale,im_scale,re_one,im_one]
    ring

theorem positive_power (a j : PTm n) : Γ ⊢[PRAAx] positivePowerLaw a j := by
  have all : Γ ⊢[PRAAx] .all (positivePowerLaw (Syn.shift a) (var 0)) := by
    ipra_qfind (⟨trivial,trivial⟩) [subst_positivePowerLaw]
    · exact positive_power_zero a
    · exact positive_power_step _ _ Prf.hyp0
  simpa only [subst_positivePowerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

def seriesLaw (a D L : PTm n) : Fm PTm n :=
  equal (series (negativeNumerator a) D L) (negativeNumerator (LogarithmRemainder.numerator a D L))
ipra_subst seriesLaw

theorem series_zero (a D : PTm n) : Γ ⊢[PRAAx] seriesLaw a D zero := by
  have h := values_of_code (ComplexLogarithmRemainder.series_zero (Γ := Γ) (negativeNumerator a) D)
  have e := natEq (LogarithmRemainder.numerator_zero (Γ := Γ) a D)
  apply equal_of_values
  · rw [h.1,re_zero]; simp only [negativeNumerator,re_neg,re_scale,re_one,e,Q.mk_zero,map_zero]; ring
  · rw [h.2,im_zero]; simp only [negativeNumerator,im_neg,im_scale,im_one]; ring

theorem series_step (a D L : PTm n) (ih : Γ ⊢[PRAAx] seriesLaw a D L) : Γ ⊢[PRAAx]
    seriesLaw a D (succ L) := by
  have h := values_of_code (ComplexLogarithmRemainder.series_succ (Γ := Γ) (negativeNumerator a) D L)
  have hr := equal_re ih
  have hi := equal_im ih
  have pr := equal_re (positive_power (Γ := Γ) a (L+LogarithmRemainder.three))
  have pi := equal_im (positive_power (Γ := Γ) a (L+LogarithmRemainder.three))
  apply equal_of_values
  · rw [h.1,re_add,re_scale,re_neg,re_scale,hr,pr]
    simp only [negativeNumerator,re_neg,re_scale,re_one]
    rw [natEq (LogarithmRemainder.numerator_succ (Γ := Γ) a D L)]; ipra_simps; ring
  · rw [h.2,im_add,im_scale,im_neg,im_scale,hi,pi]
    simp only [negativeNumerator,im_neg,im_scale,im_one]; ring

theorem negative_series (a D L : PTm n) : Γ ⊢[PRAAx] seriesLaw a D L := by
  have all : Γ ⊢[PRAAx] .all (seriesLaw (Syn.shift a) (Syn.shift D) (var 0)) := by
    ipra_qfind (⟨trivial,trivial⟩) [subst_seriesLaw]
    · exact series_zero a D
    · exact series_step _ _ _ Prf.hyp0
  simpa only [subst_seriesLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE L

/-- The ORIGINAL factor numerator has exactly its negative majorant,
including its quadratic term and every internal Taylor cutoff. -/
theorem negative_factor (a D L : PTm n) : Γ ⊢[PRAAx]
    equal (GammaCanonicalFactors.factorNumerator (negativeNumerator a) D L)
      (negativeNumerator (GammaCanonicalFactors.factorRadius a D L)) := by
  have hr := equal_re (negative_series (Γ := Γ) a D L)
  have hi := equal_im (negative_series (Γ := Γ) a D L)
  apply equal_of_values
  · simp only [GammaCanonicalFactors.factorNumerator,re_add,re_neg,re_scale,re_mul]
    rw [hr]
    simp only [negativeNumerator,re_neg,im_neg,re_scale,im_scale,re_one,im_one]
    unfold GammaCanonicalFactors.factorRadius; ipra_simps; ring
  · simp only [GammaCanonicalFactors.factorNumerator,im_add,im_neg,im_scale,im_mul]
    rw [hi]
    simp only [negativeNumerator,re_neg,im_neg,re_scale,im_scale,re_one,im_one]; ring

/-- Exact order of the SAME actual finite scaled logarithm. No disk
or approximation law is required for this finite signed comparison. -/
theorem finite_scaled_order (a b N L : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (fstT (natScale N (GaussianFiniteLogarithmSampler.sample (negativeNumerator a) (b*N) L)))
      (fstT (target a b)) := by
  let D := b*N
  let F := GammaCanonicalFactors.factorDenominator D L
  let V := ComplexLogarithmName.finiteNumerator (negativeNumerator a) D L
  have hd := positive_product (Γ := Γ) b N hb hN
  have hf := GammaCanonicalFactors.factorDenominator_positive (Γ := Γ) D L hd
  have left := GaussianRationalNaturalScale.natScale_represents N _ V F hf (ofGaussian_represents _ _ hf)
  have right := ofGaussian_represents (Γ := Γ) (negativeNumerator a) b hb
  apply RationalArithmetic.order_of_representations _ _ (re (scale N V)) (re (negativeNumerator a)) F b left.andE₁ right.andE₁ hf hb
  have value := equal_re (GammaLogarithmFactorBridge.source_numerator (Γ := Γ) (negativeNumerator a) D L)
  have factor := equal_re (negative_factor (Γ := Γ) a D L)
  apply zle_of_toZ (D*GammaCanonicalFactors.factorRadius a D L)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,re_scale]
  dsimp only [V] at value ⊢
  rw [value,re_add,re_scale,factor]
  simp only [negativeNumerator,re_neg,re_scale,re_one]
  dsimp only [D,F,GammaCanonicalFactors.factorDenominator,GammaLogarithmFactorBridge.linearScale]
  ipra_simps; ring

def finiteObservation (p a b N : PTm n) : PTm n :=
  natScale N (GaussianFiniteLogarithmSampler.sample (negativeNumerator a) (b*N)
    (DyadicComplexLogarithm.precision (GaussianNamedNaturalScale.clock p N)))

/-- Only the genuine original rounding allowance is amplified, and the
actual capped clock absorbs it at the unchanged requested precision p. -/
theorem observation_finite_distance (p a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    distanceBounded (observation p a b N) (finiteObservation p a b N) one (unit p) := by
  let r := GaussianNamedNaturalScale.clock p N
  let s := GaussianFiniteLogarithmSampler.sample (negativeNumerator a) (b*N) (DyadicComplexLogarithm.precision r)
  have hs := GaussianBetaKernelLogarithm.local_source a b N h
  have raw := GaussianLocalLogarithmName.point_rounding_distance r (negativeNumerator a) a (b*N) hs.andE₁
  have coarsen : Γ ⊢[PRAAx] le (num 4*unit r) (one*DyadicComplexLogarithm.unit r) :=
    le_congr (.eqRefl _) ((one_mul _).eqTrans (GaussianLocalLogarithmName.unit_factor r)).eqSymm
      (le_of_eq_add (d := num 12*unit r) (by ipra_ring))
  have round := distance_radius_mono _ _ _ _ one (unit r) (GaussianLocalLogarithmName.unit_positive r) (unit_positive r) coarsen raw
  have finiteBound : Γ ⊢[PRAAx] bounded s (num 3) one :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ (num 3) (num 4) (num 3) one
      GaussianLocalLogarithmName.four_positive (le_refl one)
      (le_of_eq_add (d := num 9) (by ipra_ring))
      (GaussianLocalLogarithmName.finite_sample_bound _ _ _ _ hs)
  have scaled := GaussianNamedNaturalScale.scaled_distance N _ s one (unit r) (num 3) (unit_positive r) round finiteBound
  have clockBudget : Γ ⊢[PRAAx] le (N*unit p) (unit r) :=
    le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (GaussianNamedNaturalScale.clock_unit p N).eqSymm)
      (mul_le_mul_right (unit p) (GaussianNamedNaturalScale.cap_budget N N (le_refl N)))
  exact distance_congr (GaussianBetaKernelLogarithm.actual_sample p a b N).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ one (unit p) (unit_positive r) (unit_positive p)
      (le_congr (by ipra_ring) (one_mul _).eqSymm clockBudget) scaled)

/-- N log(1-a/(bN)) is below -a/b, with only the requested
observation allowance. Equivalently the signed remainder is >=-eps_p. -/
theorem original_signed_remainder (p a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (observation p a b N)) (fstT (target a b)) one (unit p) :=
  RationalValueBounds.upper_order_right _ _ _ _ _
    (RationalValueBounds.upper_of_radius _ _ _ _
      (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ (unit_positive p)
        (observation_finite_distance p a b N h)))
    (finite_scaled_order a b N _ h.andE₁ h.andE₂.andE₁)

theorem original_signed_quadratic_remainder (p a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (observation p a b N)) (fstT (target a b)) one (unit p) ⋏
      distanceBounded (observation p a b N) (target a b) (a*a*unit p+b*b*N) (b*b*N*unit p) :=
  .andI (original_signed_remainder p a b N h) (GaussianBetaKernelLogarithm.original_logarithm_rate p a b N h)

/-- Real subtraction preserves the exact original rational allowance,
without assuming the raw Gaussian input codes are canonical or real. -/
theorem subtraction_lower (q r A B : PTm n)
    (h : Γ ⊢[PRAAx] RationalValueBounds.upper (fstT q) (fstT r) A B) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (GaussianRationalSyntheticBounds.natCode zero)
      (fstT (GaussianRationalMetric.qsub r q)) A B := by
  let x := fstT q
  let y := fstT r
  let dx := RationalSupMetric.denominatorOf x
  let dy := RationalSupMetric.denominatorOf y
  let value := RationalSupMetric.numeratorOf y*ZT.ofNat dx+(-RationalSupMetric.numeratorOf x)*ZT.ofNat dy
  have code : Γ ⊢[PRAAx] fstT (GaussianRationalMetric.qsub r q) ≐
      RationalArithmetic.add y (RationalArithmetic.negative x) :=
    (fst_pair _ _).eqTrans (RationalAlgebra.add_congr (.eqRefl _) (fst_pair _ _))
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (GaussianRationalMetric.qsub r q)) value (dy*dx) :=
    GaussianRationalHorner.scalar_congr code.eqSymm (.eqRefl _) (.eqRefl _)
      (RationalRepresentations.represents_add _ _ _ _ _ _
        (RationalRepresentations.represents_self y) (RationalArithmetic.negative_value x))
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat zero) value one (dy*dx) A B
    (le_refl one) (positive_product _ _ (RationalArgmin.denominator_positive y) (RationalArgmin.denominator_positive x))
    (GaussianRationalSyntheticBounds.natCode_represents zero) rep
  apply zle_of_toZ (LeanProofs.IPRA.PTm.monus
    (B*RationalValueBounds.crossLeft y x+A*dx*dy) (B*RationalValueBounds.crossLeft x y))
  have e := natEq (eq_add_of_le h)
  dsimp only [x,y,dx,dy,value] at e ⊢
  simp only [RationalValueBounds.crossLeft,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_neg] at e ⊢
  simp only [ZT.toZ]
  ipra_simps
  linear_combination -e

def remainder (p a b N : PTm n) : PTm n := GaussianRationalMetric.qsub (target a b) (observation p a b N)

theorem original_remainder_lower (p a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (GaussianRationalSyntheticBounds.natCode zero) (fstT (remainder p a b N)) one (unit p) :=
  subtraction_lower _ _ one (unit p) (original_signed_remainder p a b N h)

theorem original_remainder_norm (p a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    bounded (remainder p a b N) (a*a*unit p+b*b*N) (b*b*N*unit p) :=
  GaussianRationalDistanceOrder.distance_symmetric _ _ _ _
    (positive_product _ _ (positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁) (unit_positive p))
    (GaussianBetaKernelLogarithm.original_logarithm_rate p a b N h)

theorem actual_negative_real_Taylor_factor_exact_signed_majorant_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (equal (GammaCanonicalFactors.factorNumerator (negativeNumerator (var 0)) (var 1) (var 2))
        (negativeNumerator (GammaCanonicalFactors.factorRadius (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (negative_factor _ _ _)

theorem actual_negative_real_finite_scaled_logarithm_order_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 1) ⋏ le one (var 2)) ⟶ RationalArgmin.rationalLE
        (fstT (natScale (var 2) (GaussianFiniteLogarithmSampler.sample
          (negativeNumerator (var 0)) (var 1*var 2) (var 3))))
        (fstT (target (var 0) (var 1)))) :=
  closeUniv 4 (.impI (finite_scaled_order _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem original_scaled_beta_logarithm_signed_quadratic_remainder_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 1) (var 2) (var 3) ⟶
        (RationalValueBounds.upper (fstT (observation (var 0) (var 1) (var 2) (var 3)))
          (fstT (target (var 1) (var 2))) one (unit (var 0)) ⋏
        distanceBounded (observation (var 0) (var 1) (var 2) (var 3)) (target (var 1) (var 2))
          (var 1*var 1*unit (var 0)+var 2*var 2*var 3) (var 2*var 2*var 3*unit (var 0)))) :=
  closeUniv 4 (.impI (original_signed_quadratic_remainder _ _ _ _ Prf.hyp0))

theorem original_beta_delta_lower_and_quadratic_norm_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 1) (var 2) (var 3) ⟶
        (RationalValueBounds.upper (GaussianRationalSyntheticBounds.natCode zero)
          (fstT (remainder (var 0) (var 1) (var 2) (var 3))) one (unit (var 0)) ⋏
        bounded (remainder (var 0) (var 1) (var 2) (var 3))
          (var 1*var 1*unit (var 0)+var 2*var 2*var 3) (var 2*var 2*var 3*unit (var 0)))) :=
  closeUniv 4 (.impI (.andI (original_remainder_lower _ _ _ _ Prf.hyp0) (original_remainder_norm _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelSignedLogarithm

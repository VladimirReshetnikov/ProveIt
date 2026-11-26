import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentCayleyProjections
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentExtensionAxis
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentPartialTrig
import IPRADerivations.Analysis.Names.GaussianImaginaryNameConjugation

/-!
# Original named sine and cosine of the general arctangent extension

Negation agrees with conjugation at the original imaginary samples.
The two original exponentials agree with the literal Cayley name
and its conjugate. The trigonometric operations read the coordinates
at that name's actual sample schedule.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianArctangentNamedCayleyTrig

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (normSq normSq_eval oneCode eval_re_code eval_im_code)
open GaussianArctangentCayleyTrig (cosineMultiplier sine_readback cosine_readback)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentCayleyProjections (sineProjectionF cosineProjectionF samplePrecision sine_sample_at cosine_sample_at
  conjugate_sample_at)
open GaussianArctangentPartialTrig (cosineF cosineData cosineSumF cosineSumData cosine_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedSineFromExponential (multiplier sineF sineData differenceF differenceData sine_regular)
open GaussianImaginaryNameConjugation (imaginarySamples negative_exponential_conjugate_cross)
open GaussianNameArithmetic (multiplyModulus sum_distance)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans)
open GaussianNameRingLaws (negativeF negativeData add_sample_error multiply_sample_error)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalHorner (positive_product ofGaussian ofGaussian_represents qmul qadd)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qadd_congr)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianRootAlgebra (re_neg im_neg)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def negativeExpF (f : PR 2) : PR 2 :=
  GaussianRadiusExponentialName.nameF (negativeF (GaussianArctangentNamedExtension.nameF f))
def negativeExpData (x : PTm n) : PTm n := GaussianRadiusExponentialName.data two (negativeData x)

theorem extension_imaginary_samples (f : PR 2) (x : PTm n) :
    Γ ⊢[PRAAx] imaginarySamples (GaussianArctangentNamedExtension.nameF f) x :=
  .allI (GaussianArctangentExtensionAxis.extension_axis_at f (var 0) (Syn.shift x))

theorem conjugate_exponential_cross (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (negativeExpF f)
      (GaussianNameConjugation.nameF (GaussianArctangentNamedCayley.nameF f))
      (negativeExpData x) (GaussianArctangentNamedCayley.data x) :=
  cross_trans _ _ _ _ _ _
    (negative_exponential_conjugate_cross _ _ _ (GaussianArctangentNamedCayley.exp_input f x hf)
      (extension_imaginary_samples f x))
    (GaussianNameConjugation.conjugate_cross _ _ _ _ (GaussianArctangentNamedCayley.exponential_cross f x hf))

private theorem same_query_distance (f g : PR 2) (p x y : PTm n)
    (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 g p y) two (unit p) := by
  have hu := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu hu) hu
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)) (cross_at f g x y p p h)

private theorem half_bound (a : PTm n) (ha : Γ ⊢[PRAAx] normSq a ≐ one) :
    Γ ⊢[PRAAx] bounded (ofGaussian a two) one one := by
  have ht : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hk : Γ ⊢[PRAAx] le one (two*two) := by ipra_le 3
  exact bounded_of_cleared _ _ _ _ _ ht (le_refl _) (ofGaussian_represents _ _ ht)
    (le_congr (ha.eqSymm.eqTrans (by ipra_ring)) (by ipra_ring) hk)

private theorem sine_multiplier_bound : Γ ⊢[PRAAx] bounded (multiplier : PTm n) one one := by
  apply half_bound
  apply deriveNat
  rw [normSq_eval]
  simp only [re_neg, im_neg, imaginaryCode, eval_re_code, eval_im_code, ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem cosine_multiplier_bound : Γ ⊢[PRAAx] bounded (cosineMultiplier : PTm n) one one :=
  half_bound oneCode ComplexLogarithmRemainder.normSq_one

def sineBudget (f : PR 2) (x : PTm n) : PTm n :=
  multiplyModulus constantF (differenceF (GaussianArctangentNamedExtension.nameF f)) multiplier (differenceData two x)+num 11

def cosineBudget (f : PR 2) (x : PTm n) : PTm n :=
  multiplyModulus constantF (cosineSumF (GaussianArctangentNamedExtension.nameF f)) cosineMultiplier (cosineSumData two x)+num 8

@[simp] theorem subst_sineBudget {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x : PTm n) :
    Syn.subst σ (sineBudget f x) = sineBudget f (Syn.subst σ x) := by simp [sineBudget]

@[simp] theorem subst_cosineBudget {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x : PTm n) :
    Syn.subst σ (cosineBudget f x) = cosineBudget f (Syn.subst σ x) := by simp [cosineBudget]

theorem sine_observation_error (f : PR 2) (p x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (sineF (GaussianArctangentNamedExtension.nameF f)) p
      (sineData (GaussianArctangentNamedExtension.nameF f) two x))
      (ap2 (sineProjectionF f) p (GaussianArctangentNamedCayley.data x)) (sineBudget f x) (unit p) := by
  let g := GaussianArctangentNamedExtension.nameF f
  let E := GaussianArctangentNamedCayley.exponentialF f
  let N := negativeExpF f
  let e := GaussianArctangentNamedCayley.exponentialData x
  let v := negativeExpData x
  let c := GaussianArctangentNamedCayley.data x
  let C := GaussianArctangentNamedCayley.nameF f
  let Z := GaussianNameConjugation.nameF C
  let B := GaussianArctangentNamedExtension.denominator f (samplePrecision p) x
  let A := GaussianArctangentNamedExtension.numerator f (samplePrecision p) x
  let D := differenceF g
  let d := differenceData two x
  have he := GaussianArctangentNamedCayley.exp_regular f x hf
  have hn := GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianExponentialInverse.negative_input _ _ _ (GaussianArctangentNamedCayley.exp_input f x hf))
  have hc : Γ ⊢[PRAAx] pointCN D d := GaussianNamedDifference.name_regular _ _ _ _ he hn
  have hp := unit_positive (Γ := Γ) p
  have hpos := same_query_distance E C p e c (GaussianArctangentNamedCayley.exponential_cross f x hf)
  have hneg := same_query_distance N Z p v c (conjugate_exponential_cross f x hf)
  have rawDifference := GaussianNamedDifference.sample_error E N e v p he hn
  have replacedDifference := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp hpos hneg
  have mid := distance_triangle_same _ _ _ _ _ _ hp rawDifference replacedDifference
  have scaled := multiply_distance multiplier _ _ one _ _ hp sine_multiplier_bound mid
  have step := multiply_sample_error constantF D multiplier d p (constant_regular _) hc
  have step' := distance_congr (.eqRefl _) (qmul_congr (constant_at p multiplier) (.eqRefl _)) (.eqRefl _) (.eqRefl _) step
  have finish : Γ ⊢[PRAAx] qmul multiplier (qsub (ap2 C p c) (ap2 Z p c)) ≐ ap2 (sineProjectionF f) p c :=
    (qmul_congr (.eqRefl _) (qsub_congr (GaussianArctangentNamedCayley.sample_at f p x) (conjugate_sample_at f p x))).eqTrans
      ((sine_readback B A (GaussianArctangentNamedExtension.denominator_positive _ _ _)).eqTrans (sine_sample_at f p x).eqSymm)
  exact distance_congr (.eqRefl _) finish (by unfold sineBudget; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp step' scaled)

theorem cosine_observation_error (f : PR 2) (p x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (cosineF (GaussianArctangentNamedExtension.nameF f)) p
      (cosineData (GaussianArctangentNamedExtension.nameF f) two x))
      (ap2 (cosineProjectionF f) p (GaussianArctangentNamedCayley.data x)) (cosineBudget f x) (unit p) := by
  let g := GaussianArctangentNamedExtension.nameF f
  let E := GaussianArctangentNamedCayley.exponentialF f
  let N := negativeExpF f
  let e := GaussianArctangentNamedCayley.exponentialData x
  let v := negativeExpData x
  let c := GaussianArctangentNamedCayley.data x
  let C := GaussianArctangentNamedCayley.nameF f
  let Z := GaussianNameConjugation.nameF C
  let B := GaussianArctangentNamedExtension.denominator f (samplePrecision p) x
  let A := GaussianArctangentNamedExtension.numerator f (samplePrecision p) x
  let D := cosineSumF g
  let d := cosineSumData two x
  have he := GaussianArctangentNamedCayley.exp_regular f x hf
  have hn := GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianExponentialInverse.negative_input _ _ _ (GaussianArctangentNamedCayley.exp_input f x hf))
  have hc : Γ ⊢[PRAAx] pointCN D d := GaussianNameArithmetic.add_fast _ _ _ _ he hn
  have hp := unit_positive (Γ := Γ) p
  have hpos := same_query_distance E C p e c (GaussianArctangentNamedCayley.exponential_cross f x hf)
  have hneg := same_query_distance N Z p v c (conjugate_exponential_cross f x hf)
  have rawSum := add_sample_error E N e v p he hn
  have replacedSum := sum_distance _ _ _ _ _ _ _ hp hpos hneg
  have mid := distance_triangle_same _ _ _ _ _ _ hp rawSum replacedSum
  have scaled := multiply_distance cosineMultiplier _ _ one _ _ hp cosine_multiplier_bound mid
  have step := multiply_sample_error constantF D cosineMultiplier d p (constant_regular _) hc
  have step' := distance_congr (.eqRefl _) (qmul_congr (constant_at p cosineMultiplier) (.eqRefl _)) (.eqRefl _) (.eqRefl _) step
  have finish : Γ ⊢[PRAAx] qmul cosineMultiplier (qadd (ap2 C p c) (ap2 Z p c)) ≐ ap2 (cosineProjectionF f) p c :=
    (qmul_congr (.eqRefl _) (qadd_congr (GaussianArctangentNamedCayley.sample_at f p x) (conjugate_sample_at f p x))).eqTrans
      ((cosine_readback B A (GaussianArctangentNamedExtension.denominator_positive _ _ _)).eqTrans (cosine_sample_at f p x).eqSymm)
  exact distance_congr (.eqRefl _) finish (by unfold cosineBudget GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp step' scaled)

theorem sine_cross (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (GaussianArctangentNamedExtension.nameF f)) (sineProjectionF f)
      (sineData (GaussianArctangentNamedExtension.nameF f) two x) (GaussianArctangentNamedCayley.data x) := by
  apply GaussianNamedDiagonalRate.cross_of_diagonal_rate _ _ _ _ (sineBudget f x)
    (sine_regular _ _ _ (GaussianArctangentNamedCayley.exp_input f x hf))
    (GaussianImaginaryCoordinateName.name_regular _ _ (GaussianArctangentNamedCayley.name_regular f x hf))
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by simpa [Fm.shift, Syn.shift] using hf.shift
  simpa only [GaussianNamedDiagonalRate.diagonalRate, Syn.shift, subst_sineBudget, one, sineProjectionF,
    GaussianNamedSineFromExponential.subst_sineData, GaussianArctangentNamedCayley.subst_data, two,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using
    sine_observation_error f (var 0) (Syn.shift x) hs

theorem cosine_cross (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (cosineF (GaussianArctangentNamedExtension.nameF f)) (cosineProjectionF f)
      (cosineData (GaussianArctangentNamedExtension.nameF f) two x) (GaussianArctangentNamedCayley.data x) := by
  apply GaussianNamedDiagonalRate.cross_of_diagonal_rate _ _ _ _ (cosineBudget f x)
    (cosine_regular _ _ _ (GaussianArctangentNamedCayley.exp_input f x hf))
    (GaussianGammaRealValues.axis_regular _ _ (GaussianArctangentNamedCayley.name_regular f x hf))
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by simpa [Fm.shift, Syn.shift] using hf.shift
  simpa only [GaussianNamedDiagonalRate.diagonalRate, Syn.shift, subst_cosineBudget, one, cosineProjectionF,
    GaussianArctangentPartialTrig.subst_cosineData, GaussianArctangentNamedCayley.subst_data, two,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using
    cosine_observation_error f (var 0) (Syn.shift x) hs

theorem actual_named_arctangent_extension_sine_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ crossEquivalent (sineF (GaussianArctangentNamedExtension.nameF f)) (sineProjectionF f)
      (sineData (GaussianArctangentNamedExtension.nameF f) two (var 0)) (GaussianArctangentNamedCayley.data (var 0))) :=
  closeUniv 1 (.impI (sine_cross f _ Prf.hyp0))

theorem actual_named_arctangent_extension_cosine_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ crossEquivalent (cosineF (GaussianArctangentNamedExtension.nameF f)) (cosineProjectionF f)
      (cosineData (GaussianArctangentNamedExtension.nameF f) two (var 0)) (GaussianArctangentNamedCayley.data (var 0))) :=
  closeUniv 1 (.impI (cosine_cross f _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianArctangentNamedCayleyTrig

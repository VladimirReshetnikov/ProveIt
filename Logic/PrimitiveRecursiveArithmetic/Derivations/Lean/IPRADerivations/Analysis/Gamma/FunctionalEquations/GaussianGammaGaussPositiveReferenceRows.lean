import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaGaussReflectionDomain
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegralPositiveLower
import IPRADerivations.Analysis.Names.GaussianNamedPositiveLateLogSource
import IPRADerivations.Analysis.Inequalities.GaussianRationalNonnegativeProducts
import IPRADerivations.Analysis.Gamma.GaussianGammaRealValues

/-!
# Positive real approximants of the original Gauss reference rows

The original Gamma at (r/m) is equivalent to its real-axis projection.
The retained projected observations occur after the explicit Euler
positivity threshold. Each is exactly real and is at least (1/36).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussPositiveReferenceRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaGaussReflectionDomain (referenceData)
open GaussianGammaReciprocalInverse (gammaF gammaHeight)
open GaussianGammaGaussReference (reference_source)
open GaussianGammaRealValues (axisF projection axis_sample_at)
open GaussianNamedPositiveLateLogSource (retimedF retimedData)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianEuclideanDistanceName (pointCN fraction fraction_represents)
open GaussianRationalNonnegativeProducts (nonnegative)
open GaussianRationalLowerBounds (lower_from_representation)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianNamedRightHalfPlane (threshold marginPoint half_margin_from_upper threshold_budget)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper upper_congr)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents)
open RationalArgmin (rationalLE)
open ComplexLogarithmRemainder (scale oneCode im re normSq)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)
open PolynomialBisection (zle_congr zle_trans)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def lowerDen : PTm n := two*num 18
def nameF : PR 2 := retimedF (axisF gammaF)
def nameData (r m : PTm n) : PTm n := retimedData (referenceData r m) (num 18)
def clock (p : PTm n) : PTm n := p+threshold (num 18)

@[simp] theorem subst_lowerDen {l : ℕ} (σ : Fin n → PTm l) :
    Syn.subst σ (lowerDen : PTm n) = (lowerDen : PTm l) := by simp [lowerDen,two]
@[simp] theorem subst_nameData {l : ℕ} (σ : Fin n → PTm l) (r m : PTm n) :
    Syn.subst σ (nameData r m) = nameData (Syn.subst σ r) (Syn.subst σ m) := by simp [nameData]
@[simp] theorem subst_clock {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (clock p) = clock (Syn.subst σ p) := by simp [clock]

theorem denominator_positive : Γ ⊢[PRAAx] le one (lowerDen : PTm n) := by
  unfold lowerDen
  ipra_le 35

private theorem native_fixed (r : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalReciprocal.conjugate (scale r oneCode) ≐ scale r oneCode := by
  let u := ZT.ofNat r*re oneCode
  let v := ZT.ofNat r*im oneCode
  let a := pairT u.pos u.neg
  let b := pairT v.pos v.neg
  let z := scale r oneCode
  have p : Γ ⊢[PRAAx] fstT z ≐ a := fst_pair _ _
  have q : Γ ⊢[PRAAx] sndT z ≐ b := snd_pair _ _
  have iv : ZT.toZ Γ v = 0 := by
    simp [v,ZT.toZ_mul,GaussianRootAlgebra.im_one,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]
  have e : Γ ⊢[PRAAx] v.pos ≐ v.neg := by
    apply deriveNat
    unfold ZT.toZ at iv
    linear_combination iv
  change Γ ⊢[PRAAx] pairT (pairT (fstT (fstT z)) (sndT (fstT z)))
    (pairT (sndT (sndT z)) (fstT (sndT z))) ≐ pairT a b
  exact congrPairT
    (congrPairT ((congrFst p).eqTrans (fst_pair _ _)) ((congrSnd p).eqTrans (snd_pair _ _)))
    (congrPairT ((congrSnd q).eqTrans ((snd_pair _ _).eqTrans e.eqSymm))
      ((congrFst q).eqTrans ((fst_pair _ _).eqTrans e)))

private theorem real_source (r m : PTm n) (hr : Γ ⊢[PRAAx] le one r) (hm : Γ ⊢[PRAAx] le r m) :
    Γ ⊢[PRAAx] GaussianEulerIntegralPositiveLower.realSource (scale r oneCode) one m m := by
  have hs := (reference_source r m hr hm).andE₁
  have hp := le_trans hr hm
  refine .andI (.andI hp (.andI hs.andE₂ ?_)) ?_
  · apply zle_of_toZ (m*LeanProofs.IPRA.PTm.monus r one)
    have e := natEq (eq_add_of_le hr)
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
    ipra_simps
    linear_combination -(𝔞 m)*e
  · apply ZT.derive
    simp [GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]

theorem original_cross (r m : PTm n) (hr : Γ ⊢[PRAAx] le one r) (hm : Γ ⊢[PRAAx] le r m) :
    Γ ⊢[PRAAx] crossEquivalent gammaF nameF (referenceData r m) (nameData r m) := by
  have h := reference_source r m hr hm
  have axis := GaussianGammaRealValues.original_gamma_real (scale r oneCode) one m one m h (native_fixed r)
  have reg := GaussianGammaReciprocalInverse.gamma_regular _ _ _ _ _ h
  exact cross_trans _ _ _ _ _ _ axis (GaussianNamedPositiveLateLogSource.original_cross _ _ _
    (GaussianGammaRealValues.axis_regular _ _ reg))

theorem name_regular (r m : PTm n) (hr : Γ ⊢[PRAAx] le one r) (hm : Γ ⊢[PRAAx] le r m) :
    Γ ⊢[PRAAx] pointCN nameF (nameData r m) :=
  cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (original_cross r m hr hm)) (original_cross r m hr hm)

theorem name_at (p r m : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (nameData r m) ≐ projection (ap2 gammaF (clock p) (referenceData r m)) :=
  (GaussianNamedPositiveLateLogSource.sample_at (axisF gammaF) p (referenceData r m) (num 18)).eqTrans
    (axis_sample_at gammaF (clock p) (referenceData r m))

private theorem margin_scalar : Γ ⊢[PRAAx]
    fstT (marginPoint (num 18 : PTm n)) ≐ fraction one (num 18) := by
  have hD : Γ ⊢[PRAAx] le one (num 18 : PTm n) := by ipra_le 17
  apply RationalFiniteSum.canonical_equal _ _ (re oneCode) (ZT.ofNat one) _ _
    (ofGaussian_canonical oneCode _ hD).andE₂.andE₁ (RationalNormalForm.normalize_well_formed _ _ hD)
    (GaussianRationalHorner.ofGaussian_represents oneCode _ hD).andE₁ (fraction_represents _ _ hD) hD hD
  apply ZT.derive
  simp only [ZT.toZ_mul,GaussianRootAlgebra.re_one,ZT.toZ_ofNat,IPRA.Q.mk_one,map_one]

private theorem sample_margin (p r m : PTm n) (hr : Γ ⊢[PRAAx] le one r) (hm : Γ ⊢[PRAAx] le r m) :
    Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower
      (rawGaussian (ap2 nameF p (nameData r m))) lowerDen (rawDen (ap2 nameF p (nameData r m))) := by
  let z := scale r oneCode
  let y := ap2 gammaF (clock p) (referenceData r m)
  let q := ap2 nameF p (nameData r m)
  have hD : Γ ⊢[PRAAx] le one (num 18 : PTm n) := by ipra_le 17
  have cy : Γ ⊢[PRAAx] GaussianRationalHorner.canonical y :=
    GaussianNameReciprocal.name_canonical GaussianGammaC7Name.nameF (gammaHeight z one m m)
      (GaussianGammaC7Name.data z one m) (clock p)
  have scalar : Γ ⊢[PRAAx] fstT (projection y) ≐ RationalArithmetic.recode (fstT y) := fst_pair _ _
  have recoded : Γ ⊢[PRAAx] RationalArithmetic.recode (fstT y) ≐ fstT y :=
    RationalNormalForm.normalize_fixed_point (fstT y) cy.andE₂.andE₁
  have read : Γ ⊢[PRAAx] fstT q ≐ fstT y :=
    (congrFst (name_at p r m)).eqTrans (scalar.eqTrans recoded)
  have u := GaussianEulerIntegralPositiveLower.original_gamma_positive_lower (clock p) z one m m
    (real_source r m hr hm) (le_refl one)
  exact half_margin_from_upper q (num 18) (unit (clock p)) hD (unit_positive _)
    (threshold_budget (clock p) (num 18) (le_add_left (threshold (num 18)) p))
    (upper_congr margin_scalar.eqSymm read.eqSymm (.eqRefl _) (.eqRefl _) u)

private theorem margin_order (a : ZT n) (D B : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] zle (ZT.ofNat B) (ZT.ofNat D*a)) : Γ ⊢[PRAAx] zle (ZT.ofNat zero) a := by
  have z : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (ZT.ofNat B) := by
    apply zle_of_toZ B
    simp [ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]
  apply PolynomialBisection.zle_scale_cancel (c := D) hD
  apply zle_congr _ rfl (zle_trans z h)
  simp [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]

theorem sample_nonnegative (p r m : PTm n) (hr : Γ ⊢[PRAAx] le one r) (hm : Γ ⊢[PRAAx] le r m) :
    Γ ⊢[PRAAx] nonnegative (ap2 nameF p (nameData r m)) := by
  let q := ap2 nameF p (nameData r m)
  let b := rawDen q
  let a := re (rawGaussian q)
  have s : Γ ⊢[PRAAx] zle (ZT.ofNat zero) a :=
    margin_order a lowerDen b denominator_positive (sample_margin p r m hr hm)
  refine .andI ?_ ((congrSnd (name_at p r m)).eqTrans (snd_pair _ _))
  apply RationalArithmetic.order_of_representations scalarZero (fstT q) (ZT.ofNat zero) a one b
    (scalar_zero_represents one) (raw_represents q).andE₁ (le_refl one) (raw_den_positive q)
  apply zle_congr _ _ s <;> simp [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero,IPRA.Q.mk_one,map_one]

theorem sample_lower (p r m : PTm n) (hr : Γ ⊢[PRAAx] le one r) (hm : Γ ⊢[PRAAx] le r m) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.lower (ap2 nameF p (nameData r m)) lowerDen := by
  let q := ap2 nameF p (nameData r m)
  let b := rawDen q
  let w := rawGaussian q
  let a := re w
  let D : PTm n := lowerDen
  have s : Γ ⊢[PRAAx] zle (ZT.ofNat b) (ZT.ofNat (D*zabs a)) := by
    apply zle_trans (sample_margin p r m hr hm)
    apply zle_congr rfl _ (PolynomialBisection.zle_scale D (GaussianRelativeNormTriangle.signed_le_absolute a))
    simp [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul]
  have bnd : Γ ⊢[PRAAx] le b (D*zabs a) :=
    le_congr (add_zero b) (add_zero (D*zabs a)) s
  have sq : Γ ⊢[PRAAx] le (zabs a*zabs a) (normSq w) :=
    le_congr (.eqRefl _) (GaussianEulerUpperPowerCoefficients.native_absolute_norm w).eqSymm (le_add_right _ _)
  have scaleSq : Γ ⊢[PRAAx] le ((D*zabs a)*(D*zabs a)) (D*D*normSq w) :=
    le_congr (by ipra_ring) (.eqRefl _)
      (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (D*D)) sq)
  apply lower_from_representation _ _ b one D (raw_den_positive q) denominator_positive (raw_represents q)
  exact le_congr (by ipra_ring) (.eqRefl _)
    (le_trans (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono bnd bnd) scaleSq)

end LeanProofs.IPRA.Analysis.GaussianGammaGaussPositiveReferenceRows

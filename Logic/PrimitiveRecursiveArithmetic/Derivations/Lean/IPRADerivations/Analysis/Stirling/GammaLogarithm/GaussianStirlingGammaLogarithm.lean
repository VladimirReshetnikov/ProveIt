import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReference
import IPRADerivations.Analysis.Gamma.GaussianGammaRealValues
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegralPositiveLower
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedPositiveLateLogSource
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalProjection

/-!
# The original Gamma logarithm at a positive encoded rational

At (x=a/b>0), the radius (a) and pole margin (1/b) give the
original Gamma source. Its real projection is equivalent to the
original name. A quantitative Euler lower bound (1/18) makes the
later actual observations admissible for the original positive log.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGammaLogarithm

open_ipra
open ComplexLogarithmRemainder (scale oneCode re im bounded normSq)
open GaussianGammaReciprocalInverse (gammaF gammaHeight)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaRealValues (axisF projection axis_sample_at)
open GaussianNamedRightHalfPlane (marginPoint)
open GaussianNamedPositiveLateLogSource (retimedF retimedData)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianEuclideanDistanceName (pointCN fraction fraction_represents)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (ofGaussian_canonical ofGaussian_represents)
open RationalValueBounds (upper upper_congr upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (a b : PTm n) : Fm PTm n := le one a ⋏ le one b
def arg (a : PTm n) : PTm n := scale a oneCode
def gammaData (a b : PTm n) : PTm n := GaussianGammaReciprocalInverse.gammaData (arg a) a b b
def gammaMargin : PTm n := num 18
def gammaLogMargin : PTm n := two*gammaMargin
def gammaRealF : PR 2 := axisF gammaF
def gammaRetimedF : PR 2 := retimedF gammaRealF
def gammaRetimedData (a b : PTm n) : PTm n := retimedData (gammaData a b) gammaMargin
def logGammaF : PR 2 := GaussianNamedPositiveLogarithm.nameF gammaRetimedF
def logGammaData (a b : PTm n) : PTm n := GaussianNamedPositiveLogarithm.data (gammaRetimedData a b) gammaLogMargin

ipra_subst source [one]
ipra_subst arg
ipra_subst gammaData [GaussianGammaReciprocalInverse.gammaData, GaussianGammaReciprocalInverse.gammaHeight]
ipra_subst gammaMargin
ipra_subst gammaLogMargin [two]
ipra_subst gammaRetimedData
ipra_subst logGammaData

theorem source_shift (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] source (a+b) b :=
  .andI (le_trans h.andE₁ (le_add_right a b)) h.andE₂

theorem native_disk (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] bounded (arg a) (a*b) := by
  have grow : Γ ⊢[PRAAx] le a (a*b) := by ipra_le 𝔞 a*sl h.andE₂
  exact le_congr (GaussianGammaGaussReference.scaled_one_norm a).eqSymm (.eqRefl _)
    (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono grow grow)

theorem gamma_source_at_radius (a b R : PTm n) (h : Γ ⊢[PRAAx] source a b)
    (hR : Γ ⊢[PRAAx] le one R) (hDisk : Γ ⊢[PRAAx] le a (R*b)) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (arg a) R b one b := by
  have boundedDisk : Γ ⊢[PRAAx] bounded (arg a) (R*b) :=
    le_congr (GaussianGammaGaussReference.scaled_one_norm a).eqSymm (.eqRefl _)
      (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono hDisk hDisk)
  refine .andI (.andI hR (.andI h.andE₂ boundedDisk)) (.andI (le_refl one) (.andI h.andE₂ ?_))
  refine .allI (.impI ?_)
  let A := Syn.shift a
  let B := Syn.shift b
  let Δ := le (var 0) (two*Syn.shift R) :: Γ.map Fm.shift
  have hA : Δ ⊢[PRAAx] le one A := by simpa [A,Syn.shift,Fm.shift,one] using h.andE₁.shift.wk
  simpa [GaussianGammaEulerHeadLower.poleGuard,arg,Syn.shift,A,B,Δ,two,one] using
    GaussianGammaGaussReference.reference_pole_at A B (var 0) hA

theorem gamma_source (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (arg a) a b one b :=
  gamma_source_at_radius a b a h h.andE₁ (by ipra_le 𝔞 a*sl h.andE₂)

theorem euler_real_source (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianEulerIntegralPositiveLower.realSource (arg a) a b b := by
  refine .andI (.andI h.andE₂ (.andI (.andI h.andE₂ (native_disk a b h)) ?_)) ?_
  · apply zle_of_toZ (b*monus a one)
    have e := natEq (eq_add_of_le h.andE₁)
    simp only [arg,ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
    ipra_simps
    linear_combination -(𝔞 b)*e
  · apply ZT.derive
    simp [arg,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]

private theorem native_fixed (r : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalReciprocal.conjugate (arg r) ≐ arg r := by
  let u := ZT.ofNat r*re oneCode
  let v := ZT.ofNat r*im oneCode
  let a := pairT u.pos u.neg
  let b := pairT v.pos v.neg
  let z := arg r
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
    (congrPairT p.fstE p.sndE)
    (congrPairT ((congrSnd q).eqTrans ((snd_pair _ _).eqTrans e.eqSymm))
      ((congrFst q).eqTrans ((fst_pair _ _).eqTrans e)))

theorem gamma_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] pointCN gammaF (gammaData a b) :=
  GaussianGammaReciprocalInverse.gamma_regular (arg a) a b one b (gamma_source a b h)

theorem gamma_real_cross (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaRealF (gammaData a b) (gammaData a b) :=
  GaussianGammaRealValues.original_gamma_real (arg a) a b one b (gamma_source a b h) (native_fixed a)

theorem gamma_retimed_cross (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaRetimedF (gammaData a b) (gammaRetimedData a b) :=
  cross_trans _ _ _ _ _ _ (gamma_real_cross a b h)
    (GaussianNamedPositiveLateLogSource.original_cross gammaRealF (gammaData a b) gammaMargin
      (GaussianGammaRealValues.axis_regular gammaF _ (gamma_regular a b h)))

theorem gamma_lower_at (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fraction one gammaMargin) (fstT (ap2 gammaF p (gammaData a b))) one (unit p) :=
  GaussianEulerIntegralPositiveLower.original_gamma_positive_lower p (arg a) a b b (euler_real_source a b h) h.andE₁

private theorem margin_positive : Γ ⊢[PRAAx] le one (gammaMargin : PTm n) := by unfold gammaMargin; ipra_le 17

private theorem margin_scalar : Γ ⊢[PRAAx]
    fstT (marginPoint (gammaMargin : PTm n)) ≐ fraction one gammaMargin := by
  have hD := margin_positive (Γ := Γ)
  apply RationalFiniteSum.canonical_equal _ _ (re oneCode) (ZT.ofNat one) _ _
    (ofGaussian_canonical oneCode _ hD).andE₂.andE₁ (RationalNormalForm.normalize_well_formed _ _ hD)
    (ofGaussian_represents oneCode _ hD).andE₁ (fraction_represents _ _ hD) hD hD
  apply ZT.derive
  simp only [ZT.toZ_mul,GaussianRootAlgebra.re_one,ZT.toZ_ofNat,IPRA.Q.mk_one,map_one]

private theorem real_coordinate (p a b : PTm n) :
    Γ ⊢[PRAAx] fstT (ap2 gammaRealF p (gammaData a b)) ≐ fstT (ap2 gammaF p (gammaData a b)) := by
  let Y := ap2 gammaF p (gammaData a b)
  have cy : Γ ⊢[PRAAx] GaussianRationalHorner.canonical Y :=
    GaussianNameReciprocal.name_canonical GaussianGammaC7Name.nameF (gammaHeight (arg a) a b b)
      (GaussianGammaC7Name.data (arg a) a b) p
  have e : Γ ⊢[PRAAx] fstT (projection Y) ≐ RationalArithmetic.recode (fstT Y) := fst_pair _ _
  have r : Γ ⊢[PRAAx] RationalArithmetic.recode (fstT Y) ≐ fstT Y :=
    RationalNormalForm.normalize_fixed_point (fstT Y) cy.andE₂.andE₁
  exact (congrFst (axis_sample_at gammaF p (gammaData a b))).eqTrans (e.eqTrans r)

private theorem real_lower_at (p q a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (marginPoint gammaMargin))) (fstT (ap2 gammaRealF q (gammaData a b)))
      (unit p+unit q) (unit p*unit q) := by
  let c := fraction (one : PTm n) gammaMargin
  let Y := fstT (ap2 gammaF q (gammaData a b))
  have hC : Γ ⊢[PRAAx] fstT (ap2 constantF p (marginPoint gammaMargin)) ≐ c :=
    (congrFst (constant_at p (marginPoint gammaMargin))).eqTrans margin_scalar
  have g := upper_mono c Y one (unit q) (unit p+unit q) (unit p*unit q) (unit_positive q)
    (gamma_lower_at q a b h) (by ipra_le (𝔞 (unit q))^2)
  exact upper_congr hC.eqSymm (real_coordinate q a b).eqSymm (.eqRefl _) (.eqRefl _) g

theorem gamma_real_positive (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source gammaRealF (gammaData a b) gammaMargin := by
  refine .andI (GaussianGammaRealValues.axis_regular gammaF _ (gamma_regular a b h)) (.andI margin_positive ?_)
  refine .allI (.allI ?_)
  let A := Syn.shift (Syn.shift a)
  let B := Syn.shift (Syn.shift b)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source A B := by simpa [Fm.shift,Syn.shift,A,B,Δ] using h.shift.shift
  simpa [GaussianNamedRightHalfPlane.certificate,GaussianNamedPositiveExponentialOrder.realOrder,
      GaussianNamedRightHalfPlane.marginPoint,gammaMargin,one,Syn.shift,A,B,Δ] using
    real_lower_at (var 1) (var 0) A B hs

theorem log_input (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source gammaRetimedF (gammaRetimedData a b)
      gammaLogMargin (GaussianNameBounds.U gammaRealF (gammaData a b)) :=
  GaussianNamedPositiveLateLogSource.positive_source gammaRealF (gammaData a b) gammaMargin
    (gamma_real_positive a b h) (GaussianEulerVerticalProjection.projected_real_samples gammaF (gammaData a b))

theorem log_gamma_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN logGammaF (logGammaData a b) :=
  GaussianNamedPositiveLogarithm.name_regular _ _ _ _ (log_input a b h)

theorem log_gamma_axis (a b : PTm n) :
    Γ ⊢[PRAAx] GaussianRealNameExponentialInjectivity.axisSamples logGammaF (logGammaData a b) :=
  GaussianNamedPositiveLogarithm.real_samples _ _ _

theorem actual_positive_rational_log_Gamma_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 1) (var 0) ⟶
      (crossEquivalent gammaF gammaRetimedF (gammaData (var 1) (var 0)) (gammaRetimedData (var 1) (var 0)) ⋏
       pointCN logGammaF (logGammaData (var 1) (var 0)))) :=
  closeUniv 2 (.impI (.andI (gamma_retimed_cross _ _ Prf.hyp0) (log_gamma_regular _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingGammaLogarithm

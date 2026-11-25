import IPRADerivations.Analysis.GaussianGammaPositiveNamedDigammaFrozen
import IPRADerivations.Analysis.GaussianGammaDigammaRescale
import IPRADerivations.Analysis.GaussianEulerNamedShiftInput
import IPRADerivations.Analysis.GaussianRationalQuadratureSquareCells
import IPRADerivations.Analysis.GaussianRationalInvertibleNorm
import IPRADerivations.Analysis.GaussianNamedReciprocalFrozenRate

/-!
# The exact rational inputs used in the named digamma recurrence

The original shifted input has a positive real certificate. Its frozen
observation is the base observation plus one at the shift sampler's
actual observation index. The reciprocal of that same positive rational
observation is the fraction with its numerator and denominator exchanged.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedDigammaRecurrenceInput

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode normSq)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerNamedShiftInput (shiftF shiftData clock)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaMinimumFreezeRational (numerator denominator fraction_at)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameReciprocal (anchor input lower lower_norm_positive)
open GaussianNamedPositiveDigamma (source)
open GaussianNamedRightHalfPlane (threshold)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian_canonical ofGaussian_represents positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalReciprocal (qone reciprocal)
open RationalSupMetric (denominatorOf)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "N" => GaussianGammaDigammaNative.nameF
local notation "nd" => GaussianGammaDigammaNative.data
local notation "nativeSource" => GaussianStirlingGammaLogarithm.source

private theorem fraction_one (b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] fraction b b ≐ (qone : PTm n) :=
  GaussianRationalHorner.canonical_unique _ _ _ b (ofGaussian_canonical _ _ hb)
    (ofGaussian_canonical _ _ (le_refl one)) hb
    (ofGaussian_represents _ _ hb) (GaussianRationalReciprocal.qone_represents_scaled b)

theorem shifted_source (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] source (shiftF f) (shiftData x) A :=
  .andI (GaussianEulerNamedShiftInput.original_source f x A h.andE₁)
    (GaussianStirlingNames.add_real f constantF x qone h.andE₂
      (GaussianStirlingNames.constant_real qone
        (ofGaussian_canonical oneCode one (le_refl one))
        (RationalGaussianEmbedding.axis_congr (fraction_one one (le_refl one))
          (GaussianStirlingNames.fraction_axis one one (le_refl one)))))

theorem shifted_fraction (f : PR 2) (k x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hk : Γ ⊢[PRAAx] le (threshold A) k) : Γ ⊢[PRAAx]
    fraction (numerator (shiftF f) k (shiftData x)) (denominator (shiftF f) k (shiftData x)) ≐
      fraction (numerator f (clock k) x + denominator f (clock k) x) (denominator f (clock k) x) := by
  let a := numerator f (clock k) x
  let b := denominator f (clock k) x
  have later := le_trans hk (GaussianEulerNamedShiftInput.clock_later (Γ := Γ) k)
  have hb := (GaussianGammaMinimumFreezeRational.frozen_rational_domain f (clock k) x A h later).andE₁.andE₂
  have sample := (fraction_at (shiftF f) k (shiftData x) A (shifted_source f x A h) hk).eqSymm
  exact sample.eqTrans ((GaussianEulerNamedShiftInput.sample_at f k x).eqTrans
    ((GaussianRationalSyntheticDivision.qadd_congr (fraction_at f (clock k) x A h later)
      (fraction_one b hb).eqSymm).eqTrans (GaussianRationalQuadratureSquareCells.fraction_add_same a b b hb)))

private theorem cross_numerators (a b c d : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (he : Γ ⊢[PRAAx] fraction a b ≐ fraction c d) :
    Γ ⊢[PRAAx] a*d ≐ c*b := by
  let X := fstT (fraction a b)
  have left : Γ ⊢[PRAAx] RationalArithmetic.represents X
      (ComplexLogarithmRemainder.re (ComplexLogarithmRemainder.scale a oneCode)) b :=
    (ofGaussian_represents (ComplexLogarithmRemainder.scale a oneCode) b hb).andE₁
  have right : Γ ⊢[PRAAx] RationalArithmetic.represents X
      (ComplexLogarithmRemainder.re (ComplexLogarithmRemainder.scale c oneCode)) d :=
    GaussianRationalHorner.scalar_congr (congrFst he).eqSymm
      (ZT.derive (by rfl)) (.eqRefl _) (ofGaussian_represents (ComplexLogarithmRemainder.scale c oneCode) d hd).andE₁
  have e := ZT.toZ_eq left
  have g := ZT.toZ_eq right
  have hc : Γ ⊢[PRAAx] le one (denominatorOf X) := RationalArgmin.denominator_positive X
  have eq : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat (a*d)*ZT.ofNat (denominatorOf X))
      (ZT.ofNat (c*b)*ZT.ofNat (denominatorOf X)) := by
    apply ZT.derive
    simp only [ZT.toZ_mul, ZT.toZ_ofNat, GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.re_one, Q.mk_mul, map_mul] at e g ⊢
    linear_combination (Groth.ι (Q.mk Γ d))*e-(Groth.ι (Q.mk Γ b))*g
  have cancel := RationalNormalForm.positive_integer_cancel (denominatorOf X) _ _ hc eq
  apply deriveNat
  simpa only [ZT.toZ_ofNat] using ZT.toZ_eq cancel

theorem native_fraction_proper (a b c d : PTm n) (h : Γ ⊢[PRAAx] nativeSource a b)
    (j : Γ ⊢[PRAAx] nativeSource c d) (he : Γ ⊢[PRAAx] fraction a b ≐ fraction c d) :
    Γ ⊢[PRAAx] crossEquivalent N N (nd a b) (nd c d) := by
  have same := cross_numerators a b c d h.andE₂ j.andE₂ he
  have scaled := GaussianGammaDigammaRescale.datum_congr
    ((mul_comm d a).eqTrans (same.eqTrans (mul_comm c b))) (mul_comm d b)
  have base := GaussianGammaDigammaRescale.native_rescale a b d h j.andE₂
  have alt := GaussianGammaDigammaRescale.native_rescale c d b j h.andE₂
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ base)
    (GaussianGammaCompactCutoffAlignment.cross_data_congr N N _ _ _ _ scaled.eqSymm (.eqRefl _) alt)

theorem reciprocal_input (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] input f (threshold A) x := by
  let p := anchor (threshold A)
  let q := ap2 f p x
  let B := rawDen q
  let U := unit (threshold A)
  have later : Γ ⊢[PRAAx] le (threshold A) p := le_add_right _ _
  have margin := GaussianNamedRightHalfPlane.actual_late_margin f x A p h.andE₁ later
  have pole := GaussianGammaRightHalfPlane.real_margin_pole_at (rawGaussian q) B (two*A) zero margin
  have norm := GaussianRootAlgebra.normSq_equal (GaussianGammaEulerHeadLower.translated_zero (Γ := Γ) (rawGaussian q) B)
  have first : Γ ⊢[PRAAx] le (B*B) ((two*A)*(two*A)*normSq (rawGaussian q)) :=
    le_congr (by ipra_ring) (congrMul (.eqRefl _) norm) pole
  have paid := GaussianNamedRightHalfPlane.precision_budget (Γ := Γ) zero A
  have squares : Γ ⊢[PRAAx] le ((two*A)*(two*A)) (U*U) :=
    le_trans (le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right (two*A) paid)) (mul_le_mul_right U paid)
  exact .andI h.andE₁.andE₁ (GaussianRationalLowerBounds.lower_from_representation q (rawGaussian q) B one U
    (raw_den_positive q) (unit_positive _) (raw_represents q)
    (le_congr (by ipra_ring) (.eqRefl _) (le_trans first (mul_le_mul_right (normSq (rawGaussian q)) squares))))

private theorem fraction_product_inverse (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    GaussianRationalHorner.qmul (fraction a b) (fraction b a) ≐ (qone : PTm n) :=
  (GaussianEulerDampedTimeRate.fraction_product a b b a hb ha).eqTrans
    ((GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (mul_comm b a)).eqTrans
      (fraction_one (a*b) (positive_product _ _ ha hb)))

theorem frozen_reciprocal (f : PR 2) (k x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hk : Γ ⊢[PRAAx] le (anchor (threshold A)) k) : Γ ⊢[PRAAx]
    GaussianNamedReciprocalFrozenRate.frozen f x k ≐ fraction (denominator f k x) (numerator f k x) := by
  let a := numerator f k x
  let b := denominator f k x
  let r := fraction a b
  let s := fraction b a
  let q := ap2 f k x
  let R := GaussianNameReciprocal.R (threshold A)
  have late := le_trans (le_add_right (threshold A) two) hk
  have domain := (GaussianGammaMinimumFreezeRational.frozen_rational_domain f k x A h late).andE₁
  have hr := ofGaussian_canonical (ComplexLogarithmRemainder.scale a oneCode) b domain.andE₂
  have hs := ofGaussian_canonical (ComplexLogarithmRemainder.scale b oneCode) a domain.andE₁
  have sample := fraction_at f k x A h late
  have exactSample := (GaussianExponentialReference.recode_fixed q (GaussianRationalHorner.canonical_congr sample hr)).eqTrans sample
  have freeze : Γ ⊢[PRAAx] GaussianNamedReciprocalFrozenRate.frozen f x k ≐ reciprocal r :=
    GaussianNameReciprocal.reciprocal_congr exactSample
  have low := GaussianNamedReciprocalFrozenRate.late_lower f (threshold A) x k (reciprocal_input f x A h) hk
  have norm := lower_norm_positive r R (GaussianNameReciprocal.R_positive _) (GaussianNameReciprocal.lower_congr sample (.eqRefl _) low)
  have inverse := GaussianRationalReciprocal.reciprocal_identity r norm
  have pivot := (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans inverse
  have c := fraction_product_inverse a b domain.andE₁ domain.andE₂
  have eu := GaussianRationalInvertibleNorm.qmul_roundtrip (reciprocal r) r s pivot hs
  exact freeze.eqTrans ((GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalReciprocal.reciprocal_canonical r)).eqSymm.eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) c.eqSymm).eqTrans eu))

end LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedDigammaRecurrenceInput

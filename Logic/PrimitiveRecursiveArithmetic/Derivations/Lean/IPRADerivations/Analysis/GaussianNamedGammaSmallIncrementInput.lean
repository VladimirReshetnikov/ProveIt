import IPRADerivations.Analysis.GaussianNamedGammaIncrementInput
import IPRADerivations.Analysis.GaussianExponentialSmallPerturbation

/-!
# Original right-half-plane input plus a small certified complex name

The increment is any fixed original regular name K. Its explicit input
contract is the existing all-observation bound |K_q|<=1/(4A). The proof
uses the actual decoded K observation at the original addition clock;
it assumes neither canonical K samples nor a certificate for the sum.
The output is the unchanged normalized addition program with margin
1/(2A), exact native readback, and independent input-observation bounds.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaSmallIncrementInput

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNameArithmetic (addF addData add_at add_fast recode_congr)
open GaussianNamedGammaIncrementInput (clock)
open GaussianNamedRightHalfPlane (numerator denominator radius marginPoint certificate)
open GaussianExponentialSmallPerturbation (smallSamples small_samples_at)
open GaussianGammaCanonicalExponent (constantF)
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianRationalHorner (qadd ofGaussian represents positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper upper_congr)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def sumF (f k : PR 2) : PR 2 := addF f k
def sumData (x y : PTm n) : PTm n := addData x y
def source (f k : PR 2) (x y A : PTm n) : Fm PTm n :=
  GaussianNamedRightHalfPlane.source f x A ⋏ (pointCN k y ⋏ smallSamples k y one (num 4*A))
def observationNumerator (p r s : PTm n) : PTm n := unit r*unit s+unit p*(unit r+unit s)
def observationDenominator (p r s : PTm n) : PTm n := unit p*unit r*unit s

@[simp] theorem subst_sumData {m : ℕ} (σ : Fin n → PTm m) (x y : PTm n) :
    Syn.subst σ (sumData x y) = sumData (Syn.subst σ x) (Syn.subst σ y) := by simp [sumData]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f k : PR 2) (x y A : PTm n) :
    (source f k x y A).subst σ = source f k (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ A) := by simp [source]

theorem sample_at (f k : PR 2) (p x y : PTm n) : Γ ⊢[PRAAx]
    ap2 (sumF f k) p (sumData x y) ≐ qadd (ap2 f (clock p) x) (ap2 k (clock p) y) :=
  (add_at f k x y p).eqTrans (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _))

theorem regular (f k : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hk : Γ ⊢[PRAAx] pointCN k y) : Γ ⊢[PRAAx]
    pointCN (sumF f k) (sumData x y) := add_fast f k x y hf hk

theorem sum_represents (a b : PTm n) : Γ ⊢[PRAAx]
    represents (qadd a b) (shifted (rawGaussian a) (rawDen a) (rawGaussian b) (rawDen b)) (rawDen a*rawDen b) := by
  have left := GaussianRationalSyntheticDivision.rescale_to (Γ := Γ) a (rawGaussian a) (rawDen a) (rawDen b)
    (rawDen a*rawDen b) (raw_represents a) (.eqRefl _)
  have right := GaussianRationalSyntheticDivision.rescale_to (Γ := Γ) b (rawGaussian b) (rawDen b) (rawDen a)
    (rawDen a*rawDen b) (raw_represents b) (mul_comm _ _)
  exact GaussianRationalHorner.qadd_represents _ _ _ _ _ (positive_product _ _ (raw_den_positive a) (raw_den_positive b)) left right

theorem sum_fraction (a b : PTm n) : Γ ⊢[PRAAx]
    qadd a b ≐ ofGaussian (shifted (rawGaussian a) (rawDen a) (rawGaussian b) (rawDen b)) (rawDen a*rawDen b) :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (positive_product _ _ (raw_den_positive a) (raw_den_positive b)))
    (positive_product _ _ (raw_den_positive a) (raw_den_positive b)) (sum_represents a b)
    (GaussianRationalHorner.ofGaussian_represents _ _ (positive_product _ _ (raw_den_positive a) (raw_den_positive b)))

theorem sample_fraction (f k : PR 2) (p x y : PTm n) : Γ ⊢[PRAAx]
    ap2 (sumF f k) p (sumData x y) ≐ ofGaussian
      (shifted (numerator f (clock p) x) (denominator f (clock p) x)
        (numerator k (clock p) y) (denominator k (clock p) y))
      (denominator f (clock p) x*denominator k (clock p) y) :=
  (sample_at f k p x y).eqTrans (sum_fraction _ _)

theorem decoded_sum (f k : PR 2) (p x y : PTm n) : Γ ⊢[PRAAx]
    ofGaussian (numerator (sumF f k) p (sumData x y)) (denominator (sumF f k) p (sumData x y)) ≐ ofGaussian
      (shifted (numerator f (clock p) x) (denominator f (clock p) x)
        (numerator k (clock p) y) (denominator k (clock p) y))
      (denominator f (clock p) x*denominator k (clock p) y) :=
  (GaussianExponentialReference.recode_fixed _ (GaussianNameArithmetic.add_canonical f k x y p)).eqTrans (sample_fraction f k p x y)

theorem native_source_at (f k : PR 2) (x y A q : PTm n) (hs : Γ ⊢[PRAAx] source f k x y A) : Γ ⊢[PRAAx]
    GaussianNamedGammaIncrementInput.source f x A (numerator k q y) (denominator k q y) := by
  have four := positive_product _ _ (le_of_eq_add (d := num 3) (by ipra_ring) : Γ ⊢[PRAAx] le one (num 4)) hs.andE₁.andE₂.andE₁
  have small := (GaussianFastValueCut.recode_bound_iff (ap2 k q y) one (num 4*A) four).iffMpr
    (small_samples_at k y one (num 4*A) q hs.andE₂.andE₂)
  exact .andI hs.andE₁ (.andI (raw_den_positive _) small)

theorem native_sample_alignment (f k : PR 2) (q x y : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianNamedGammaIncrementInput.incrementF f) q
      (GaussianNamedGammaIncrementInput.incrementData x (numerator k (clock q) y) (denominator k (clock q) y)) ≐
        ap2 (sumF f k) q (sumData x y) :=
  (GaussianNamedGammaIncrementInput.sample_fraction f q x _ _ (raw_den_positive _)).eqTrans (sample_fraction f k q x y).eqSymm

theorem certificate_at (f k : PR 2) (x y A p q : PTm n) (hs : Γ ⊢[PRAAx] source f k x y A) : Γ ⊢[PRAAx]
    upper (fstT (ap2 constantF p (marginPoint (two*A)))) (fstT (ap2 (sumF f k) q (sumData x y)))
      (unit p+unit q) (unit p*unit q) :=
  upper_congr (.eqRefl _) (congrFst (native_sample_alignment f k q x y)) (.eqRefl _) (.eqRefl _)
    (GaussianNamedGammaIncrementInput.certificate_at f x A _ _ p q (native_source_at f k x y A (clock q) hs))

theorem original_certificate (f k : PR 2) (x y A : PTm n) (hs : Γ ⊢[PRAAx] source f k x y A) : Γ ⊢[PRAAx]
    certificate (sumF f k) (sumData x y) (two*A) := by
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f k (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y))
      (Syn.shift (Syn.shift A)) := by simpa [Fm.shift,Syn.shift] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [certificate,realOrder,subst_sumData,GaussianNamedRightHalfPlane.subst_marginPoint,
    PTm.subst_mul,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    certificate_at f k (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (Syn.shift (Syn.shift A)) (var 1) (var 0) ss

theorem original_source (f k : PR 2) (x y A : PTm n) (hs : Γ ⊢[PRAAx] source f k x y A) : Γ ⊢[PRAAx]
    GaussianNamedRightHalfPlane.source (sumF f k) (sumData x y) (two*A) :=
  .andI (regular f k x y hs.andE₁.andE₁ hs.andE₂.andE₁)
    (.andI (positive_product _ _ (le_succ_self one) hs.andE₁.andE₂.andE₁) (original_certificate f k x y A hs))

theorem independent_observations (f k : PR 2) (p r s x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hk : Γ ⊢[PRAAx] pointCN k y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (sumF f k) p (sumData x y)) (qadd (ap2 f r x) (ap2 k s y))
      (observationNumerator p r s) (observationDenominator p r s) := by
  let U := unit (clock p)
  let V := unit r
  let W := unit s
  let P := unit p
  have den : Γ ⊢[PRAAx] le one (U*V*W) := positive_product _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _)
  have fnear := GaussianNameEquivalence.point_at f x (clock p) r hf
  have knear := GaussianNameEquivalence.point_at k y (clock p) s hk
  have first := distance_radius_mono _ _ _ _ ((U+V)*W) (U*V*W)
    (positive_product _ _ (unit_positive _) (unit_positive _)) den
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) fnear
  have second := distance_radius_mono _ _ _ _ ((U+W)*V) (U*V*W)
    (positive_product _ _ (unit_positive _) (unit_positive _)) den
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) knear
  have added := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ den first second
  have exactSample := distance_congr (sample_at f k p x y).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) added
  have pays : Γ ⊢[PRAAx] le (two*P) U := GaussianFastValueCut.query_budget two p
  exact distance_radius_mono _ _ _ _ (observationNumerator p r s) (observationDenominator p r s) den
    (positive_product _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _))
    (by dsimp only [observationNumerator,observationDenominator]; ipra_le (𝔞 V*𝔞 W)^2*sl pays) exactSample

theorem frozen_disk (f k : PR 2) (r s x y A : PTm n) (hs : Γ ⊢[PRAAx] source f k x y A) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (shifted (numerator f r x) (denominator f r x) (numerator k s y) (denominator k s y))
      ((radius f x+one)*(denominator f r x*denominator k s y)) :=
  GaussianNamedGammaIncrementInput.frozen_disk f r x A _ _ (native_source_at f k x y A s hs)

theorem actual_named_small_increment_half_plane_source_closed (f k : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f k (var 0) (var 1) (var 2) ⟶
      GaussianNamedRightHalfPlane.source (sumF f k) (sumData (var 0) (var 1)) (two*var 2)) :=
  closeUniv 3 (.impI (original_source f k _ _ _ Prf.hyp0))

theorem actual_named_sum_independent_observations_closed (f k : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((pointCN f (var 3) ⋏ pointCN k (var 4)) ⟶
      distanceBounded (ap2 (sumF f k) (var 0) (sumData (var 3) (var 4)))
        (qadd (ap2 f (var 1) (var 3)) (ap2 k (var 2) (var 4)))
        (observationNumerator (var 0) (var 1) (var 2)) (observationDenominator (var 0) (var 1) (var 2))) :=
  closeUniv 5 (.impI (independent_observations f k _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaSmallIncrementInput

import IPRADerivations.Analysis.GaussianNamedRightHalfPlane
import IPRADerivations.Analysis.GaussianEulerParameterExponentialIncrement
import IPRADerivations.Analysis.RationalRepresentedUpper

/-!
# Actual named Gamma inputs with a fixed complex rational increment

The original normalized addition program uses its own original read clock.
Every observation has the exact canonical native sum fraction; its raw
decoded denominator need not equal the displayed common denominator.
An original margin 1/A and |h/D|<=1/(4A) imply the original named margin
1/(2A). The increment may have arbitrary signed real and imaginary parts.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaIncrementInput

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedRightHalfPlane (certificate marginPoint numerator denominator radius)
open GaussianNameArithmetic (addF addData add_fast add_at recode_congr)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianRationalHorner (qadd ofGaussian represents represents_congr positive_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalMetric (bounded bounded_to_cleared distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedPositiveExponentialOrder (realOrder)
open RationalValueBounds (upper upper_congr upper_mono)
open ComplexLogarithmRemainder (scale re oneCode)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def incrementF (f : PR 2) : PR 2 := addF f constantF
def incrementData (x h D : PTm n) : PTm n := addData x (ofGaussian h D)
def clock (p : PTm n) : PTm n := GaussianFastValueCut.exponent two p
def source (f : PR 2) (x A h D : PTm n) : Fm PTm n :=
  GaussianNamedRightHalfPlane.source f x A ⋏ (le one D ⋏ bounded (ofGaussian h D) one (num 4*A))

@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (x h D : PTm n) :
    Syn.subst σ (incrementData x h D) = incrementData (Syn.subst σ x) (Syn.subst σ h) (Syn.subst σ D) := by simp [incrementData]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (clock p) = clock (Syn.subst σ p) := by simp [clock]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x A h D : PTm n) :
    (source f x A h D).subst σ = source f (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ h) (Syn.subst σ D) := by simp [source]

theorem clock_later (p : PTm n) : Γ ⊢[PRAAx] le p (clock p) := le_add_right _ _

theorem sample_at (f : PR 2) (p x h D : PTm n) : Γ ⊢[PRAAx]
    ap2 (incrementF f) p (incrementData x h D) ≐ qadd (ap2 f (clock p) x) (ofGaussian h D) :=
  (add_at f constantF x (ofGaussian h D) p).eqTrans
    ((recode_congr (qadd_congr (.eqRefl _) (constant_at (clock p) (ofGaussian h D)))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _)))

theorem regular (f : PR 2) (x h D : PTm n) (hs : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    pointCN (incrementF f) (incrementData x h D) := add_fast f constantF x (ofGaussian h D) hs (constant_regular _)

theorem sum_represents (q h D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    represents (qadd q (ofGaussian h D)) (shifted (rawGaussian q) (rawDen q) h D) (rawDen q*D) := by
  let B := rawDen q
  have hB := raw_den_positive (Γ := Γ) q
  have bd := positive_product _ _ hB hD
  have left := GaussianRationalSyntheticDivision.rescale_to (Γ := Γ) q (rawGaussian q) B D (B*D) (raw_represents q) (.eqRefl _)
  have right := GaussianRationalSyntheticDivision.rescale_to (ofGaussian h D) h D B (B*D)
    (GaussianRationalHorner.ofGaussian_represents h D hD) (mul_comm _ _)
  exact GaussianRationalHorner.qadd_represents _ _ _ _ _ bd left right

theorem sum_fraction (q h D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    qadd q (ofGaussian h D) ≐ ofGaussian (shifted (rawGaussian q) (rawDen q) h D) (rawDen q*D) :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (positive_product _ _ (raw_den_positive q) hD))
    (positive_product _ _ (raw_den_positive q) hD) (sum_represents q h D hD)
    (GaussianRationalHorner.ofGaussian_represents _ _ (positive_product _ _ (raw_den_positive q) hD))

theorem sample_fraction (f : PR 2) (p x h D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    ap2 (incrementF f) p (incrementData x h D) ≐ ofGaussian
      (shifted (numerator f (clock p) x) (denominator f (clock p) x) h D) (denominator f (clock p) x*D) :=
  (sample_at f p x h D).eqTrans (sum_fraction _ h D hD)

theorem decoded_increment (f : PR 2) (p x h D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    ofGaussian (numerator (incrementF f) p (incrementData x h D)) (denominator (incrementF f) p (incrementData x h D)) ≐
      ofGaussian (shifted (numerator f (clock p) x) (denominator f (clock p) x) h D) (denominator f (clock p) x*D) :=
  (GaussianExponentialReference.recode_fixed _ (GaussianNameArithmetic.add_canonical f constantF x (ofGaussian h D) p)).eqTrans
    (sample_fraction f p x h D hD)

theorem increment_half_disk (f : PR 2) (x A h D : PTm n) (hs : Γ ⊢[PRAAx] source f x A h D) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (scale (two*A) h) D := by
  have hA := hs.andE₁.andE₂.andE₁
  have h2 := positive_product _ _ (le_succ_self one) hA
  have h4 := positive_product _ _ (le_of_eq_add (d := num 3) (by ipra_ring) : Γ ⊢[PRAAx] le one (num 4)) hA
  have half : Γ ⊢[PRAAx] bounded (ofGaussian h D) one (two*A) :=
    bounded_radius_mono (ofGaussian h D) one (num 4*A) one (two*A) h4 h2
      (le_of_eq_add (d := two*A) (by ipra_ring)) hs.andE₂.andE₂
  have clear := bounded_to_cleared _ _ D one (two*A) hs.andE₂.andE₁ h2
    (GaussianRationalHorner.ofGaussian_represents h D hs.andE₂.andE₁) half
  exact le_congr (ComplexLogarithmRemainder.normSq_scale (two*A) h).eqSymm (by ipra_ring) clear

private theorem shifted_upper (f : PR 2) (x A h D q U : PTm n) (hs : Γ ⊢[PRAAx] source f x A h D)
    (old : Γ ⊢[PRAAx] upper (fstT (marginPoint A)) (fstT q) one U) : Γ ⊢[PRAAx]
    upper (fstT (marginPoint (two*A))) (fstT (qadd q (ofGaussian h D))) one U := by
  let B := rawDen q
  let z := rawGaussian q
  let a := RationalRepresentedUpper.left (re oneCode) B U
  let b := RationalRepresentedUpper.right (re z) A B one U
  let w := re (ComplexLogarithmRemainder.neg (scale (two*A) h))
  let d := ZT.ofNat D
  have ha := hs.andE₁.andE₂.andE₁
  have hd := hs.andE₂.andE₁
  have hb := raw_den_positive (Γ := Γ) q
  have baseOrder := RationalRepresentedUpper.to_signed _ _ (re oneCode) (re z) A B one U
    (GaussianRationalHorner.ofGaussian_represents oneCode A ha).andE₁ (raw_represents q).andE₁ old
  have stepOrder := GaussianEulerUpperPowerCoefficients.native_real_upper (ComplexLogarithmRemainder.neg (scale (two*A) h)) D
    (ComplexLogarithmRemainder.bounded_neg (increment_half_disk f x A h D hs))
  have base : ZT.toZ Γ a+𝔞(PolynomialBisection.slack a b) = ZT.toZ Γ b := zle_toZ baseOrder
  have move : ZT.toZ Γ w+𝔞(PolynomialBisection.slack w d) = ZT.toZ Γ d := zle_toZ stepOrder
  apply RationalRepresentedUpper.from_signed _ _ (re oneCode) (re (shifted z B h D)) (two*A) (B*D) one U
    (positive_product _ _ (le_succ_self one) ha) (positive_product _ _ hb hd)
    (GaussianRationalHorner.ofGaussian_represents oneCode (two*A) (positive_product _ _ (le_succ_self one) ha)).andE₁
    (sum_represents q h D hd).andE₁
  apply zle_of_toZ (two*D*PolynomialBisection.slack a b+B*U*PolynomialBisection.slack w d)
  dsimp only [a,b,RationalRepresentedUpper.left,RationalRepresentedUpper.right,w,d] at base move
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_one,GaussianRootAlgebra.re_neg,
    GaussianRootAlgebra.re_scale] at base move
  dsimp only [a,b,w,d]
  simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,shifted,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,
    GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
  ipra_simps
  linear_combination (2*𝔞 D)*base+(𝔞 B*𝔞 U)*move

theorem certificate_at (f : PR 2) (x A h D p q : PTm n) (hs : Γ ⊢[PRAAx] source f x A h D) : Γ ⊢[PRAAx]
    upper (fstT (ap2 constantF p (marginPoint (two*A)))) (fstT (ap2 (incrementF f) q (incrementData x h D)))
      (unit p+unit q) (unit p*unit q) := by
  have old := GaussianNamedRightHalfPlane.actual_sample_upper f x A (clock q) hs.andE₁.andE₂.andE₂
  have shifted := shifted_upper f x A h D (ap2 f (clock q) x) (unit (clock q)) hs old
  have grow := GaussianExponentialReference.unit_monotone (clock_later (Γ := Γ) q)
  have wide := upper_mono _ _ one (unit (clock q)) (unit p+unit q) (unit p*unit q) (unit_positive _) shifted
    (by ipra_le 𝔞(unit p)*sl grow+𝔞(unit q)*𝔞(unit (clock q)))
  exact upper_congr (congrFst (constant_at p (marginPoint (two*A)))).eqSymm (congrFst (sample_at f q x h D)).eqSymm
    (.eqRefl _) (.eqRefl _) wide

theorem original_certificate (f : PR 2) (x A h D : PTm n) (hs : Γ ⊢[PRAAx] source f x A h D) : Γ ⊢[PRAAx]
    certificate (incrementF f) (incrementData x h D) (two*A) := by
  have hh : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A))
      (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift D)) := by simpa [Fm.shift,Syn.shift] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [certificate,realOrder,subst_incrementData,GaussianNamedRightHalfPlane.subst_marginPoint,
    PTm.subst_mul,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    certificate_at f (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift D)) (var 1) (var 0) hh

theorem original_source (f : PR 2) (x A h D : PTm n) (hs : Γ ⊢[PRAAx] source f x A h D) : Γ ⊢[PRAAx]
    GaussianNamedRightHalfPlane.source (incrementF f) (incrementData x h D) (two*A) :=
  .andI (regular f x h D hs.andE₁.andE₁)
    (.andI (positive_product _ _ (le_succ_self one) hs.andE₁.andE₂.andE₁) (original_certificate f x A h D hs))

theorem sample_to_frozen (f : PR 2) (p r x h D : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (incrementF f) p (incrementData x h D))
      (ofGaussian (shifted (numerator f r x) (denominator f r x) h D) (denominator f r x*D))
      (unit p+unit r) (unit p*unit r) := by
  let U := unit (clock p)
  let V := unit r
  let P := unit p
  have den : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive _) (unit_positive _)
  have raw := GaussianNameEquivalence.point_at f x (clock p) r hf
  have same := GaussianRationalPowerDifference.distance_refl_zero (ofGaussian h D) (U*V) den
  have added := GaussianNameArithmetic.sum_distance _ _ _ _ (U+V) zero (U*V) den raw same
  have exactSample : Γ ⊢[PRAAx] distanceBounded (ap2 (incrementF f) p (incrementData x h D))
      (ofGaussian (shifted (numerator f r x) (denominator f r x) h D) (denominator f r x*D)) (U+V) (U*V) :=
    distance_congr (sample_at f p x h D).eqSymm (sum_fraction (ap2 f r x) h D hD)
    (by ipra_ring) (.eqRefl _) added
  have grow := GaussianExponentialReference.unit_monotone (clock_later (Γ := Γ) p)
  exact distance_radius_mono _ _ _ _ (P+V) (P*V) den (positive_product _ _ (unit_positive _) (unit_positive _))
    (by ipra_le (𝔞 V)^2*sl grow) exactSample

theorem frozen_disk (f : PR 2) (r x A h D : PTm n) (hs : Γ ⊢[PRAAx] source f x A h D) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (shifted (numerator f r x) (denominator f r x) h D)
      ((radius f x+one)*(denominator f r x*D)) := by
  have h4 := positive_product _ _ (le_of_eq_add (d := num 3) (by ipra_ring) : Γ ⊢[PRAAx] le one (num 4)) hs.andE₁.andE₂.andE₁
  have unitH : Γ ⊢[PRAAx] bounded (ofGaussian h D) one one :=
    bounded_radius_mono (ofGaussian h D) one (num 4*A) one one h4 (le_refl one)
      (le_congr (by ipra_ring) (by ipra_ring) h4) hs.andE₂.andE₂
  have clear := bounded_to_cleared _ _ D one one hs.andE₂.andE₁ (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents h D hs.andE₂.andE₁) unitH
  have native : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h D := le_congr (by ipra_ring) (by ipra_ring) clear
  have sum := ComplexLogarithmRemainder.bounded_add
    (ComplexLogarithmRemainder.bounded_scale D (GaussianNamedRightHalfPlane.actual_sample_disk f x r hs.andE₁.andE₁))
    (ComplexLogarithmRemainder.bounded_scale (denominator f r x) native)
  exact le_congr (.eqRefl _) (by ipra_ring) sum

theorem frozen_disk_mono (f : PR 2) (r x A h D S : PTm n) (hs : Γ ⊢[PRAAx] source f x A h D)
    (hS : Γ ⊢[PRAAx] le (radius f x+one) S) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (shifted (numerator f r x) (denominator f r x) h D) (S*(denominator f r x*D)) :=
  le_trans (frozen_disk f r x A h D hs) (sq_le_sq (mul_le_mul_right (denominator f r x*D) hS))

theorem actual_named_complex_increment_half_plane_source_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source f (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianNamedRightHalfPlane.source (incrementF f) (incrementData (var 0) (var 2) (var 3)) (two*var 1)) :=
  closeUniv 4 (.impI (original_source f _ _ _ _ Prf.hyp0))

theorem actual_named_complex_increment_decoded_fraction_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶
      ofGaussian (numerator (incrementF f) (var 0) (incrementData (var 1) (var 2) (var 3)))
        (denominator (incrementF f) (var 0) (incrementData (var 1) (var 2) (var 3))) ≐
      ofGaussian (shifted (numerator f (clock (var 0)) (var 1)) (denominator f (clock (var 0)) (var 1)) (var 2) (var 3))
        (denominator f (clock (var 0)) (var 1)*var 3)) :=
  closeUniv 4 (.impI (decoded_increment f _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaIncrementInput

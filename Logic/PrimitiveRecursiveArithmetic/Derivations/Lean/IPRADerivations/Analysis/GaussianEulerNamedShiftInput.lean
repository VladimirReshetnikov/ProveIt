import IPRADerivations.Analysis.GaussianNamedRightHalfPlane
import IPRADerivations.Analysis.GaussianGammaEulerHeadShift
import IPRADerivations.Analysis.RationalRepresentedUpper

/-!
# The actual named input plus one in the original right half-plane

The normalized addition uses its actual original query clock. Its
observations are exactly represented by the native shift of the decoded
old observation at that clock. The original right-half-plane source is
preserved with the same positive margin certificate A; no equality of
the two raw decoded denominators is asserted or needed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedShiftInput

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNameArithmetic (addF addData add_fast add_at recode_congr)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerHeadShift (shifted)
open GaussianNamedRightHalfPlane (source certificate marginPoint numerator denominator)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianRationalHorner (qadd ofGaussian represents represents_congr positive_product)
open GaussianRationalSyntheticDivision (qone qadd_congr)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def shiftF (f : PR 2) : PR 2 := addF f constantF
def shiftData (x : PTm n) : PTm n := addData x qone
def clock (p : PTm n) : PTm n := GaussianFastValueCut.exponent two p
@[simp] theorem subst_shiftData {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (shiftData x) = shiftData (Syn.subst σ x) := by simp [shiftData]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (clock p) = clock (Syn.subst σ p) := by simp [clock]

theorem clock_later (p : PTm n) : Γ ⊢[PRAAx] le p (clock p) := le_add_right _ _

theorem sample_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (shiftF f) p (shiftData x) ≐ qadd (ap2 f (clock p) x) qone :=
  (add_at f constantF x qone p).eqTrans
    ((recode_congr (qadd_congr (.eqRefl _) (constant_at (clock p) qone))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _)))

theorem regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    pointCN (shiftF f) (shiftData x) := add_fast f constantF x qone h (constant_regular qone)

theorem shifted_fraction_represents (q : PTm n) : Γ ⊢[PRAAx]
    represents (qadd q qone) (shifted (rawGaussian q) (rawDen q)) (rawDen q) := by
  let B := rawDen q
  have hB := raw_den_positive (Γ := Γ) q
  have oneRep : Γ ⊢[PRAAx] represents (qone : PTm n) (ComplexLogarithmRemainder.scale B ComplexLogarithmRemainder.oneCode) B :=
    represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (one_mul B)
      (GaussianRationalHorner.represents_rescale qone ComplexLogarithmRemainder.oneCode one B
        (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one)))
  have old := GaussianRationalHorner.qadd_represents q qone (rawGaussian q)
    (ComplexLogarithmRemainder.scale B ComplexLogarithmRemainder.oneCode) B hB (raw_represents q) oneRep
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) old
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [shifted,GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;>
    ipra_simps <;> ring

theorem shifted_fraction (q : PTm n) : Γ ⊢[PRAAx]
    qadd q qone ≐ ofGaussian (shifted (rawGaussian q) (rawDen q)) (rawDen q) :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (raw_den_positive q)) (raw_den_positive q)
    (shifted_fraction_represents q) (GaussianRationalHorner.ofGaussian_represents _ _ (raw_den_positive q))

theorem sample_fraction (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (shiftF f) p (shiftData x) ≐
      ofGaussian (shifted (numerator f (clock p) x) (denominator f (clock p) x)) (denominator f (clock p) x) :=
  (sample_at f p x).eqTrans (shifted_fraction _)

theorem decoded_shift (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ofGaussian (numerator (shiftF f) p (shiftData x)) (denominator (shiftF f) p (shiftData x)) ≐
      ofGaussian (shifted (numerator f (clock p) x) (denominator f (clock p) x)) (denominator f (clock p) x) :=
  (GaussianExponentialReference.recode_fixed _ (GaussianNameArithmetic.add_canonical f constantF x qone p)).eqTrans
    (sample_fraction f p x)

private theorem add_one_upper (q : PTm n) : Γ ⊢[PRAAx]
    upper (fstT q) (fstT (qadd q qone)) zero one := by
  let B := rawDen q
  let z := rawGaussian q
  have hB := raw_den_positive (Γ := Γ) q
  apply RationalRepresentedUpper.from_signed _ _ (ComplexLogarithmRemainder.re z) (ComplexLogarithmRemainder.re (shifted z B)) B B zero one
    hB hB (raw_represents q).andE₁ (shifted_fraction_represents q).andE₁
  apply zle_of_toZ (B*B)
  simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,shifted,GaussianGammaEulerHeadLower.translated,
    GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,
    ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem certificate_at (f : PR 2) (x A p q : PTm n) (h : Γ ⊢[PRAAx] certificate f x A) : Γ ⊢[PRAAx]
    upper (fstT (ap2 constantF p (marginPoint A))) (fstT (ap2 (shiftF f) q (shiftData x)))
      (unit p+unit q) (unit p*unit q) := by
  have old := GaussianNamedRightHalfPlane.actual_sample_upper f x A (clock q) h
  have extended := upper_triangle _ _ _ one (unit (clock q)) zero one old (add_one_upper (ap2 f (clock q) x))
  have oneS : Γ ⊢[PRAAx] upper (fstT (marginPoint A)) (fstT (qadd (ap2 f (clock q) x) qone)) one (unit (clock q)) :=
    upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) extended
  have grow := GaussianExponentialReference.unit_monotone (clock_later (Γ := Γ) q)
  have widened := upper_mono _ _ one (unit (clock q)) (unit p+unit q) (unit p*unit q) (unit_positive _) oneS
    (by ipra_le 𝔞(unit p)*sl grow + 𝔞(unit q)*𝔞(unit (clock q)))
  exact upper_congr (congrFst (constant_at p (marginPoint A))).eqSymm (congrFst (sample_at f q x)).eqSymm (.eqRefl _) (.eqRefl _) widened

theorem original_certificate (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] certificate f x A) : Γ ⊢[PRAAx]
    certificate (shiftF f) (shiftData x) A := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] certificate f (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A)) :=
    by simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [certificate,realOrder,Syn.shift,subst_shiftData,GaussianNamedRightHalfPlane.subst_marginPoint] using
    certificate_at f (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A)) (var 1) (var 0) hs

theorem original_source (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    source (shiftF f) (shiftData x) A :=
  .andI (regular f x h.andE₁) (.andI h.andE₂.andE₁ (original_certificate f x A h.andE₂.andE₂))

theorem actual_named_right_half_plane_shift_source_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source f (var 0) (var 1) ⟶ source (shiftF f) (shiftData (var 0)) (var 1)) :=
  closeUniv 2 (.impI (original_source f _ _ Prf.hyp0))
theorem actual_named_shift_decoded_native_fraction_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ofGaussian (numerator (shiftF f) (var 0) (shiftData (var 1))) (denominator (shiftF f) (var 0) (shiftData (var 1))) ≐
      ofGaussian (shifted (numerator f (clock (var 0)) (var 1)) (denominator f (clock (var 0)) (var 1)))
        (denominator f (clock (var 0)) (var 1))) :=
  closeUniv 2 (decoded_shift f _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerNamedShiftInput

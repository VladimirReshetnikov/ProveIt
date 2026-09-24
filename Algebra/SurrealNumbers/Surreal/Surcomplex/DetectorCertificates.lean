import Surreal.Algebra.DetectorCertificates
import Surreal.Surcomplex.DetectorWitnessSupport
import Surreal.Foundations.OmnificRealScaling
import Surreal.Foundations.OmnificReciprocalSeries

/-!
# Actual omnific certificate examples

The identities and constant coefficients of `odg:def:ex:certificates`.
The witnesses work for every actual purely infinite input; omega and
the infinite reciprocal-exponent series supply the printed examples.
-/

universe u
namespace Surreal.Foundations.SignSequence

open IntersectivePolynomial

noncomputable section

attribute [local instance] nonnegativeSupportRealAlgebra

private theorem support_constant_zero (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) : constantCoeff x.val = 0 :=
  (CoefficientPullback.mem_ker_iff constantCoeff (Int.castRingHom ℝ) Int.cast_injective x).mp hx

private theorem integer_constant_eq (x : OmnificInteger.{u}) (n : ℤ)
    (hx : constantCoeff x.val = (n : ℝ)) : omnificConstantCoeff x = n := by
  apply Int.cast_injective (α := ℝ)
  exact (CoefficientPullback.embedding_retraction constantCoeff (Int.castRingHom ℝ)
    Int.cast_injective x).trans hx

/-- The t witness of constant term zero, including its allowed irrational coefficient. -/
def omnificOneShiftT (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal) :
    OmnificInteger.{u} := omnificRealScale (-Real.sqrt 13) x hx

@[simp] theorem omnificOneShiftT_val (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal) :
    omnificToSurreal (omnificOneShiftT x hx) = -ofReal (Real.sqrt 13) * omnificToSurreal x := by
  rw [omnificOneShiftT, omnificToSurreal_realScale, map_neg]

/-- The literal printed witnesses for 1+x, with both exact integer constant coefficients. -/
theorem omnific_oneShift_certificate (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) :
    (1 + x) * oneShiftS x = value (omnificOneShiftT x hx) ∧
      omnificConstantCoeff (oneShiftS x) = -48841 ∧
      omnificConstantCoeff (omnificOneShiftT x hx) = 0 := by
  refine ⟨?_, oneShiftS_augmentation omnificConstantCoeff x hx, ?_⟩
  · apply Subtype.ext
    change (1 + x.val) * oneShiftS x.val = value (realConstants (-Real.sqrt 13) * x.val)
    rw [map_neg]
    apply oneShift_identity
    rw [← map_pow, Real.sq_sqrt (by norm_num), map_ofNat]
  · exact omnificRealScale_mem_purelyInfinite (-Real.sqrt 13) x hx

/-- Every such 1+x is accepted by the two-witness detector. -/
theorem omnific_oneShift_detects (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal) :
    Detects (1 + x) := ⟨oneShiftS x, omnificOneShiftT x hx, (omnific_oneShift_certificate x hx).1⟩

/-- For nonzero purely infinite x, the accepted element 1+x is a nonunit. -/
theorem omnific_oneShift_not_isUnit (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) (hx0 : x ≠ 0) : ¬ IsUnit (1 + x) := by
  intro hu
  rcases (omnific_isUnit_iff _).mp hu with h | h
  · exact hx0 (_root_.add_left_cancel (h.trans (_root_.add_zero 1).symm))
  · have hc := congrArg omnificConstantCoeff h
    change omnificConstantCoeff x = 0 at hx
    norm_num [map_add, map_one, map_neg, hx] at hc

/-- The printed affine witness for the constant-term-two input. -/
def omnificTwoShiftT (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal) :
    OmnificInteger.{u} := 1 + omnificRealScale (twoShiftSlope (Real.sqrt 13)) x hx

@[simp] theorem omnificTwoShiftT_val (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal) :
    omnificToSurreal (omnificTwoShiftT x hx) =
      1 + ofReal ((1 - Real.sqrt 13) / 2) * omnificToSurreal x := by
  rw [omnificTwoShiftT, map_add, map_one, omnificToSurreal_realScale]
  rfl

private theorem twoShift_data (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal) :
    constantCoeff (omnificTwoShiftT x hx).val = 1 ∧
      constantCoeff (detectorWitnessS (Real.sqrt 13) (twoShiftSlope (Real.sqrt 13)) (2 + x.val)) =
        -21120 ∧
      (2 + x.val) * detectorWitnessS (Real.sqrt 13) (twoShiftSlope (Real.sqrt 13)) (2 + x.val) =
        value (omnificTwoShiftT x hx).val := by
  let ct : nonnegativeSupportSubring.{u} →ₐ[ℝ] ℝ :=
    { __ := constantCoeff
      commutes' := constantCoeff_realConstants }
  have hd := twoShift_augmentation ct (Real.sqrt 13) (by norm_num [Real.sq_sqrt])
    x.val (support_constant_zero x hx)
  have ht : detectorWitnessT (Real.sqrt 13) (twoShiftSlope (Real.sqrt 13)) (2 + x.val) =
      (omnificTwoShiftT x hx).val := by
    change (witnessTPolynomial _ _).eval₂ (algebraMap ℝ nonnegativeSupportSubring) (2 + x.val) = _
    rw [witnessTPolynomial_eval, twoShiftT_formula]
    rfl
  change constantCoeff (detectorWitnessT _ _ (2 + x.val)) = 1 ∧
    constantCoeff (detectorWitnessS _ _ (2 + x.val)) = -21120 ∧
    (2 + x.val) * detectorWitnessS _ _ (2 + x.val) = value (detectorWitnessT _ _ (2 + x.val)) at hd
  rwa [ht] at hd

/-- The degree-five witness is omnific because its extracted coefficient is -21120. -/
def omnificTwoShiftS (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal) :
    OmnificInteger.{u} :=
  ⟨detectorWitnessS (Real.sqrt 13) (twoShiftSlope (Real.sqrt 13)) (2 + x.val),
    ⟨-21120, by
      simpa only [Int.coe_castRingHom, Int.cast_neg, Int.cast_ofNat] using
        (twoShift_data x hx).2.1.symm⟩⟩

/-- The printed constant-term-two certificate and its exact constant coefficients. -/
theorem omnific_twoShift_certificate (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) :
    (2 + x) * omnificTwoShiftS x hx = value (omnificTwoShiftT x hx) ∧
      omnificConstantCoeff (omnificTwoShiftS x hx) = -21120 ∧
      omnificConstantCoeff (omnificTwoShiftT x hx) = 1 := by
  have hd := twoShift_data x hx
  refine ⟨Subtype.ext hd.2.2, integer_constant_eq _ _ ?_, integer_constant_eq _ _ ?_⟩
  · simp only [Int.cast_neg, Int.cast_ofNat]
    exact hd.2.1
  · simpa only [Int.cast_one] using hd.1

/-- The displayed constant-term-two input is accepted with the constructed witnesses. -/
theorem omnific_twoShift_detects (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal) :
    Detects (2 + x) :=
  ⟨omnificTwoShiftS x hx, omnificTwoShiftT x hx, (omnific_twoShift_certificate x hx).1⟩

/-- Every actual purely infinite omnific input is rejected by the detector. -/
theorem omnific_purelyInfinite_not_detects (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) : ¬ Detects x := by
  rw [omnific_detector_iff]
  exact not_not.mpr hx

/-- The printed nonzero omega example is rejected. -/
theorem omnific_omega_not_detects : ¬ Detects (omnificMonomial (1 : SignSequence.{u}) zero_lt_one) :=
  omnific_purelyInfinite_not_detects _ (omnificMonomial_mem_purelyInfinite _ _)

/-- The accepted element 1+omega is a nonunit. -/
theorem omnific_one_add_omega_detects_nonunit :
    Detects (1 + omnificMonomial (1 : SignSequence.{u}) zero_lt_one) ∧
      ¬ IsUnit (1 + omnificMonomial (1 : SignSequence.{u}) zero_lt_one) :=
  ⟨omnific_oneShift_detects _ (omnificMonomial_mem_purelyInfinite _ _),
    omnific_oneShift_not_isUnit _ (omnificMonomial_mem_purelyInfinite _ _) (omnificMonomial_ne_zero _ _)⟩

/-- The source's second finite expression, 2+omega, has the printed certificate. -/
theorem omnific_two_add_omega_detects : Detects (2 + omnificMonomial (1 : SignSequence.{u}) zero_lt_one) :=
  omnific_twoShift_detects _ (omnificMonomial_mem_purelyInfinite _ _)

/-- The actual infinite reciprocal-exponent series has no certificate. -/
theorem omnific_reciprocal_series_not_detects : ¬ Detects reciprocalOmegaOmnific.{u} :=
  omnific_purelyInfinite_not_detects _ reciprocalOmegaOmnific_purelyInfinite

end
end Surreal.Foundations.SignSequence

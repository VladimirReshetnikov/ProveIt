import Surreal.Surcomplex.PurelyInfiniteSize
import Surreal.Foundations.OmnificRealScaling

/-!
# Real and complex kernels of X + iY

The example in `odg:dec:rem:kernels`. The real kernel is zero, whereas the
complex kernel consists of (t,it). Real omnific solutions at every ordinary
complex level are ordinary. Gaussian omnific variables admit the purely
infinite line (1+t,it), including the actual point (1+omega,i omega).
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- The coefficient row of the Cartesian form X + iY. -/
def cartesianFormMatrix : Matrix Unit (Fin 2) ℂ := fun _ => ![1, Complex.I]

/-- The Cartesian form has zero kernel on real vectors. -/
theorem cartesianForm_real_kernel :
    LinearMap.ker (realKernelMatrix cartesianFormMatrix).mulVecLin = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  have h := (realKernelMatrix_mem_ker_iff cartesianFormMatrix v).mp hv ()
  simp [cartesianFormMatrix, Fin.sum_univ_two] at h
  have h0 := congrArg Complex.re h
  have h1 := congrArg Complex.im h
  simp at h0 h1
  change v = 0
  ext k
  fin_cases k
  · exact h0
  · exact h1

/-- The complex kernel is the line spanned by (1,i). -/
theorem cartesianForm_complex_kernel_iff (v : Fin 2 → ℂ) :
    v ∈ LinearMap.ker cartesianFormMatrix.mulVecLin ↔
      ∃ t : ℂ, v = ![t, Complex.I * t] := by
  constructor
  · intro hv
    have h := congrFun hv ()
    change cartesianFormMatrix.mulVec v () = 0 at h
    simp [Matrix.mulVec, dotProduct, cartesianFormMatrix, Fin.sum_univ_two] at h
    refine ⟨v 0, ?_⟩
    ext k
    fin_cases k
    · rfl
    · change v 1 = Complex.I * v 0
      have hi := congrArg (Complex.I * ·) h
      simp only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul, mul_zero] at hi
      linear_combination -hi
  · rintro ⟨t, rfl⟩
    ext j
    simp [Matrix.mulVec, dotProduct, cartesianFormMatrix, Fin.sum_univ_two, ← mul_assoc]

/-- Every real omnific solution at an ordinary complex level is its ordinary constant pair.
The level may be zero. -/
theorem omnific_cartesian_rigidity (c : ℂ) (x y : SignSequence.OmnificInteger.{u})
    (h : omnificSupportInclusion x + complexConstants Complex.I * omnificSupportInclusion y =
      complexConstants c) :
    x = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff x) ∧
      y = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff y) := by
  have hv : ofReal (SignSequence.omnificToSurreal x) +
      ofComplex Complex.I * ofReal (SignSequence.omnificToSurreal y) = ofComplex c :=
    congrArg Subtype.val h
  have hx : SignSequence.omnificToSurreal x = SignSequence.ofReal c.re := by
    simpa using congrArg QuadraticAlgebra.re hv
  have hy : SignSequence.omnificToSurreal y = SignSequence.ofReal c.im := by
    simpa using congrArg QuadraticAlgebra.im hv
  exact ⟨SignSequence.omnific_eq_intConstant_of_finite x (hx ▸ SignSequence.finite_ofReal c.re),
    SignSequence.omnific_eq_intConstant_of_finite y (hy ▸ SignSequence.finite_ofReal c.im)⟩

/-- Exact ordinary solutions of the real omnific Cartesian equation. -/
theorem omnific_cartesian_solutions_iff (c : ℂ) (x y : SignSequence.OmnificInteger.{u}) :
    omnificSupportInclusion x + complexConstants Complex.I * omnificSupportInclusion y =
      complexConstants c ↔
      ∃ a b : ℤ, (a : ℂ) + Complex.I * (b : ℂ) = c ∧
        x = SignSequence.omnificIntCast a ∧ y = SignSequence.omnificIntCast b := by
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := omnific_cartesian_rigidity c x y h
    refine ⟨SignSequence.omnificConstantCoeff x, SignSequence.omnificConstantCoeff y, ?_, hx, hy⟩
    have hc := congrArg constantCoeff h
    simpa only [map_add, map_mul, constantCoeff_omnificSupportInclusion,
      constantCoeff_complexConstants] using hc
  · rintro ⟨a, b, hc, rfl, rfl⟩
    rw [omnificSupportInclusion_intCast, omnificSupportInclusion_intCast,
      ← map_mul, ← map_add, hc]

/-- The purely infinite complex line through the ordinary Gaussian point (1,0). -/
def gaussianCartesianPoint (t : complexPurelyInfiniteSubmodule.{u}) :
    Fin 2 → GaussianOmnificInteger.{u} :=
  ![1 + complexPurelyInfiniteToGaussian t, complexPurelyInfiniteToGaussian (Complex.I • t)]

/-- Every point of this line solves X + iY = 1. -/
theorem gaussianCartesianPoint_equation (t : complexPurelyInfiniteSubmodule.{u}) :
    (gaussianCartesianPoint t 0).val +
      complexConstants Complex.I * (gaussianCartesianPoint t 1).val = 1 := by
  change 1 + t.val + complexConstants Complex.I * (Complex.I • t.val) = 1
  rw [Algebra.smul_def]
  change 1 + t.val + complexConstants Complex.I * (complexConstants Complex.I * t.val) = 1
  rw [← mul_assoc, ← map_mul, Complex.I_mul_I, map_neg, map_one]
  ring

/-- A nonzero purely infinite parameter makes the first coordinate nonordinary. -/
theorem gaussianCartesianPoint_nonordinary (t : complexPurelyInfiniteSubmodule.{u}) (ht : t ≠ 0) :
    ∀ a : GaussianInt, gaussianCartesianPoint t 0 ≠ gaussianOmnificConstants a := by
  intro a h
  have ha := congrArg gaussianOmnificConstantCoeff h
  change gaussianOmnificConstantCoeff (1 + complexPurelyInfiniteToGaussian t) = _ at ha
  simp only [map_add, map_one, gaussianConstantCoeff_purelyInfinite, add_zero,
    gaussianOmnificConstantCoeff_constants] at ha
  rw [← ha, map_one] at h
  have hv : 1 + t.val = (1 : nonnegativeSupportSubring.{u}) := congrArg Subtype.val h
  apply ht
  exact Subtype.ext (add_eq_left.mp hv)

/-- The manuscript's actual omega point belongs to the Gaussian omnific ring, solves the
equation, and is nonordinary. Its two ambient values are literally (1+omega,i omega). -/
theorem gaussian_cartesian_omega :
    let w : SignSequence.OmnificInteger.{u} := SignSequence.omnificMonomial 1 zero_lt_one
    ∃ x y : GaussianOmnificInteger.{u},
      gaussianOmnificToSurcomplex x = 1 + ofReal (SignSequence.omnificToSurreal w) ∧
      gaussianOmnificToSurcomplex y = I * ofReal (SignSequence.omnificToSurreal w) ∧
      x.val + complexConstants Complex.I * y.val = 1 ∧
      ∀ a : GaussianInt, x ≠ gaussianOmnificConstants a := by
  dsimp only
  let w : SignSequence.omnificPurelyInfiniteIdeal.{u} :=
    ⟨SignSequence.omnificMonomial 1 zero_lt_one,
      SignSequence.omnificMonomial_mem_purelyInfinite 1 zero_lt_one⟩
  let t := realPurelyInfiniteToComplex w
  refine ⟨gaussianCartesianPoint t 0, gaussianCartesianPoint t 1, rfl, ?_,
    gaussianCartesianPoint_equation t, gaussianCartesianPoint_nonordinary t ?_⟩
  · change ofComplex Complex.I * ofReal (SignSequence.omnificToSurreal w.val) = _
    rw [ofComplex_I]
  · intro hz
    have hw : w = 0 := realPurelyInfiniteToComplex_injective hz
    exact SignSequence.omnificMonomial_ne_zero 1 zero_lt_one (congrArg Subtype.val hw)

end
end Surreal.Surcomplex

import Surreal.Surcomplex.DecomposableFibers
import Surreal.Foundations.OmnificPurelyInfiniteModule

/-!
# Omnific fibers of complex products of affine forms

The solution decomposition in `odg:thm:decomposable` (a) and
`odg:eq:decomposablefiber`, retaining arbitrary complex coefficients and
actual real omnific unknowns.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- Include real omnific integers in the actual complex nonnegative-support ring. -/
def omnificSupportInclusion : SignSequence.OmnificInteger.{u} →+* nonnegativeSupportSubring.{u} :=
  (ofReal.comp SignSequence.omnificToSurreal).codRestrict _ (fun x =>
    ⟨x.val.property, Subring.zero_mem _⟩)

@[simp] theorem constantCoeff_omnificSupportInclusion (x : SignSequence.OmnificInteger.{u}) :
    constantCoeff (omnificSupportInclusion x) = (SignSequence.omnificConstantCoeff x : ℂ) := by
  apply Complex.ext
  · change SignSequence.constantCoeff x.val = (SignSequence.omnificConstantCoeff x : ℝ)
    rw [SignSequence.constantCoeff_eq]
    exact (SignSequence.cast_omnificConstantCoeff x).symm
  · exact map_zero SignSequence.constantCoeff

@[simp] theorem omnificSupportInclusion_intCast (a : ℤ) :
    omnificSupportInclusion (SignSequence.omnificIntCast a) = complexConstants.{u} (a : ℂ) := by
  apply Subtype.ext
  apply Surcomplex.ext <;> simp [omnificSupportInclusion, complexConstants]

/-- The constant coordinate in an ordinary-plus-purely-infinite split is forced. -/
theorem omnific_split_constant (a : ℤ) (v : SignSequence.omnificPurelyInfiniteIdeal.{u}) :
    SignSequence.omnificConstantCoeff (SignSequence.omnificIntCast a + v.val) = a := by
  have hv : SignSequence.omnificConstantCoeff v.val = 0 := v.property
  simp [hv]

/-- Exact omnific fibers: ordinary integer points plus purely infinite common-kernel vectors. -/
theorem omnific_decomposable_fiber_iff {m n : Type*} [Fintype m] [Fintype n]
    (β : m → ℂ) (A : Matrix m n ℂ) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (x : n → SignSequence.OmnificInteger.{u}) :
    DecomposableFibers.value β A e (fun k => omnificSupportInclusion (x k)) = complexConstants c ↔
      ∃ (a : n → ℤ) (v : n → SignSequence.omnificPurelyInfiniteIdeal.{u}),
        (∀ k, x k = SignSequence.omnificIntCast (a k) + (v k).val) ∧
        DecomposableFibers.value β A e (fun k => (a k : ℂ)) = c ∧
        ∀ j, ∑ k, A j k • omnificSupportInclusion (v k).val = 0 := by
  rw [nonnegativeSupport_decomposable_iff β A e he c hc]
  constructor
  · rintro ⟨hx, hk⟩
    let a : n → ℤ := fun k => SignSequence.omnificConstantCoeff (x k)
    let v : n → SignSequence.omnificPurelyInfiniteIdeal := fun k =>
      ⟨x k - SignSequence.omnificIntCast (a k), by
        change SignSequence.omnificConstantCoeff (x k - SignSequence.omnificIntCast (a k)) = 0
        simp [a]⟩
    refine ⟨a, v, fun k => by dsimp [v]; abel, ?_, ?_⟩
    · simpa only [constantCoeff_omnificSupportInclusion] using hx
    · intro j
      simpa only [v, map_sub, omnificSupportInclusion_intCast,
        constantCoeff_omnificSupportInclusion] using hk j
  · rintro ⟨a, v, hx, ha, hv⟩
    constructor
    · simpa only [hx, constantCoeff_omnificSupportInclusion, omnific_split_constant] using ha
    · intro j
      have hr (k : n) : omnificSupportInclusion (x k) -
          complexConstants (constantCoeff (omnificSupportInclusion (x k))) =
          omnificSupportInclusion (v k).val := by
        rw [constantCoeff_omnificSupportInclusion, hx k, omnific_split_constant,
          map_add, omnificSupportInclusion_intCast, add_sub_cancel_left]
      simpa only [hr] using hv j

end
end Surreal.Surcomplex

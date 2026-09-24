import Surreal.Algebra.ModuleKernelBasis
import Surreal.Foundations.OmnificPurelyInfiniteModule

/-!
# Omnific linear systems with ordinary right-hand sides

The full `odg:thm:linear`: constant extraction splits every solution into an
ordinary solution and a purely infinite kernel vector. Any rational kernel
basis gives unique purely infinite coefficients. Full column rank forces
all solutions to be ordinary.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

open Matrix Module

variable {m n ι : Type*} [Fintype n]

/-- Constant extraction commutes with an integer matrix acting on omnific tuples. -/
theorem omnificConstantCoeff_mulVec (M : Matrix m n ℤ) (x : n → OmnificInteger.{u}) :
    (fun j => omnificConstantCoeff ((M.map omnificIntCast *ᵥ x) j)) =
      M *ᵥ (fun k => omnificConstantCoeff (x k)) := by
  funext j
  simp [Matrix.mulVec, dotProduct]

/-- Integer inclusion commutes with matrix action. -/
theorem omnificIntCast_mulVec (M : Matrix m n ℤ) (a : n → ℤ) :
    M.map omnificIntCast *ᵥ (fun k => omnificIntCast (a k)) =
      (fun j => omnificIntCast.{u} ((M *ᵥ a) j)) := by
  funext j
  simp [Matrix.mulVec, dotProduct]

/-- All solutions split into an ordinary solution and a purely infinite homogeneous solution. -/
theorem omnific_linear_solutions_iff (M : Matrix m n ℤ) (b : m → ℤ)
    (x : n → OmnificInteger.{u}) :
    M.map omnificIntCast *ᵥ x = (fun j => omnificIntCast (b j)) ↔
      ∃ (a : n → ℤ) (v : n → omnificPurelyInfiniteIdeal.{u}),
        (∀ j, x j = omnificIntCast (a j) + (v j).val) ∧
        M *ᵥ a = b ∧ M.map omnificIntCast *ᵥ (fun j => (v j).val) = 0 := by
  constructor
  · intro hx
    let a : n → ℤ := fun j => omnificConstantCoeff (x j)
    let v : n → omnificPurelyInfiniteIdeal := fun j =>
      ⟨x j - omnificIntCast (a j), by
        change omnificConstantCoeff (x j - omnificIntCast (a j)) = 0
        simp [a]⟩
    have ha : M *ᵥ a = b := by
      rw [← omnificConstantCoeff_mulVec, hx]
      simp
    refine ⟨a, v, fun j => by dsimp [v]; abel, ha, ?_⟩
    change M.map omnificIntCast *ᵥ (x - fun j => omnificIntCast (a j)) = 0
    rw [mulVec_sub, omnificIntCast_mulVec, ha, hx, sub_self]
  · rintro ⟨a, v, he, ha, hv⟩
    have hx : x = (fun j => omnificIntCast (a j)) + (fun j => (v j).val) := funext he
    rw [hx, mulVec_add, omnificIntCast_mulVec, ha, hv, _root_.add_zero]

/-- The rational module equation on the ideal is exactly its omnific matrix equation. -/
theorem omnific_purelyInfinite_kernel_iff (M : Matrix m n ℤ)
    (v : n → omnificPurelyInfiniteIdeal.{u}) :
    M.map omnificIntCast *ᵥ (fun j => (v j).val) = 0 ↔
      ∀ j, ∑ k, (M j k : ℚ) • v k = 0 := by
  constructor
  · intro hv j
    apply Subtype.val_injective
    simp only [Submodule.coe_sum, omnificPurelyInfinite_int_smul, ZeroMemClass.coe_zero]
    exact congrFun hv j
  · intro hv
    funext j
    have h := congrArg Subtype.val (hv j)
    simp only [Submodule.coe_sum, omnificPurelyInfinite_int_smul, ZeroMemClass.coe_zero] at h
    exact h

variable [Fintype m] [DecidableEq m] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- Every rational kernel basis uniquely parametrizes the purely infinite homogeneous solutions. -/
theorem omnific_purelyInfinite_kernel_coordinates_iff (M : Matrix m n ℤ)
    (b : Basis ι ℚ (LinearMap.ker (M.map (Int.castRingHom ℚ)).mulVecLin))
    (v : n → omnificPurelyInfiniteIdeal.{u}) :
    M.map omnificIntCast *ᵥ (fun j => (v j).val) = 0 ↔
      ∃! h : ι → omnificPurelyInfiniteIdeal.{u}, ∀ j, v j = ∑ i, (b i).val j • h i := by
  rw [omnific_purelyInfinite_kernel_iff]
  constructor
  · exact ModuleKernelBasis.existsUnique_kernel_coordinates (M.map (Int.castRingHom ℚ)) b v
  · rintro ⟨h, he, _⟩ j
    simp_rw [he]
    exact ModuleKernelBasis.kernel_coordinates_solve (M.map (Int.castRingHom ℚ)) b h j

/-- Full column rank over the rationals forces every omnific solution to be ordinary. -/
theorem omnific_linear_full_column_rank (M : Matrix m n ℤ)
    (hM : Function.Injective (M.map (Int.castRingHom ℚ)).mulVecLin)
    (b : m → ℤ) (x : n → OmnificInteger.{u})
    (hx : M.map omnificIntCast *ᵥ x = fun j => omnificIntCast (b j)) :
    ∃ a : n → ℤ, M *ᵥ a = b ∧ ∀ j, x j = omnificIntCast (a j) := by
  obtain ⟨a, v, he, ha, hv⟩ := (omnific_linear_solutions_iff M b x).mp hx
  have hz := ModuleKernelBasis.eq_zero_of_injective (M.map (Int.castRingHom ℚ)) hM v
    ((omnific_purelyInfinite_kernel_iff M v).mp hv)
  refine ⟨a, ha, fun j => ?_⟩
  simpa only [hz, Pi.zero_apply, ZeroMemClass.coe_zero, _root_.add_zero] using he j

end
end Surreal.Foundations.SignSequence

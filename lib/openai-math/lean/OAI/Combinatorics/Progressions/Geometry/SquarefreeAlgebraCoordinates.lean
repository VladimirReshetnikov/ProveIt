import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import OAI.Combinatorics.Progressions.Estimates.SquarefreeAdaptedLieAlgebra

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeCoefficientLayer (a : SquarefreeIndex ι) : Submodule ℚ L := by
  classical
  exact if a.val = 0 then ⊥ else F.layer (blockDegree π a.val)

theorem mem_squarefreeCoefficientLayer (a : SquarefreeIndex ι) (v : L) :
    v ∈ F.squarefreeCoefficientLayer π a ↔
      v ∈ F.layer (blockDegree π a.val) ∧ (a.val = 0 → v = 0) := by
  classical
  by_cases ha : a.val = 0 <;> simp [squarefreeCoefficientLayer, ha, F.zero_eq_top]

noncomputable def squarefreeAlgebraEquiv :
    F.SquarefreeAlgebra π ≃ₗ[ℚ] ((a : SquarefreeIndex ι) → F.squarefreeCoefficientLayer π a) where
  toFun x a := ⟨squarefreePolynomialEquiv x.val a,
    (F.mem_squarefreeCoefficientLayer π a _).mpr (x.property a)⟩
  invFun f := ⟨squarefreePolynomialEquiv.symm (fun a => (f a).val), by
    intro a
    simpa only [LinearEquiv.apply_symm_apply] using
      (F.mem_squarefreeCoefficientLayer π a _).mp (f a).property⟩
  left_inv x := by
    apply Subtype.ext
    exact squarefreePolynomialEquiv.symm_apply_apply x.val
  right_inv f := by
    ext a
    exact congrFun (squarefreePolynomialEquiv.apply_symm_apply (fun b => (f b).val)) a
  map_add' x y := by
    ext a
    exact congrFun (map_add squarefreePolynomialEquiv x.val y.val) a
  map_smul' r x := by
    ext a
    exact congrFun (map_smul squarefreePolynomialEquiv r x.val) a

theorem squarefreeAlgebraEquiv_apply (x : F.SquarefreeAlgebra π) (a : SquarefreeIndex ι) :
    (F.squarefreeAlgebraEquiv π x a).val = squarefreePolynomialEquiv x.val a := rfl

instance squarefreeAlgebraFiniteDimensional [FiniteDimensional ℚ L] :
    FiniteDimensional ℚ (F.SquarefreeAlgebra π) :=
  FiniteDimensional.of_injective (F.squarefreeAlgebraEquiv π).toLinearMap
    (F.squarefreeAlgebraEquiv π).injective

theorem squarefreeAlgebra_finrank [FiniteDimensional ℚ L] :
    Module.finrank ℚ (F.SquarefreeAlgebra π) =
      ∑ a : SquarefreeIndex ι, Module.finrank ℚ (F.squarefreeCoefficientLayer π a) := by
  rw [(F.squarefreeAlgebraEquiv π).finrank_eq, Module.finrank_pi_fintype]

theorem squarefreeAlgebra_finrank_le [FiniteDimensional ℚ L] :
    Module.finrank ℚ (F.SquarefreeAlgebra π) ≤
      2 ^ Fintype.card ι * Module.finrank ℚ L := by
  rw [F.squarefreeAlgebra_finrank π]
  calc
    _ ≤ ∑ _a : SquarefreeIndex ι, Module.finrank ℚ L :=
      Finset.sum_le_sum fun a _ => (F.squarefreeCoefficientLayer π a).finrank_le
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_squarefreeIndex, Nat.cast_id]

end Erdos3.MultidegreeLieFiltration

end

end OAI

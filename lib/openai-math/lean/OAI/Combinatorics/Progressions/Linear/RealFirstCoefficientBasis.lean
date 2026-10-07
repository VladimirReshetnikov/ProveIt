import OAI.Combinatorics.Progressions.Estimates.RealFirstCoefficientHorizontal
import OAI.Combinatorics.Progressions.Geometry.SupportedSubquotient

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realShiftedCoefficient_eq_span (w : σ → ℕ) (k : ℕ) :
    F.realShiftedCoefficientSubmodule w k = Submodule.span ℝ
      ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ ''
        {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}) := by
  change (F.shiftedPolynomialIdeal w k).toSubmodule.baseChange ℝ = _
  rw [F.shiftedPolynomialIdeal_eq_span_monomialBasis b ω hF,
    Submodule.baseChange_span, Set.image_image]
  congr 2
  funext z
  exact (Basis.baseChange_apply ℝ (F.adaptedMonomialBasis b ω hF w) z).symm

noncomputable def realShiftedMonomialBasis (w : σ → ℕ) (k : ℕ) :
    Basis (ShiftedMonomialIndex w ω k) ℝ (F.realShiftedCoefficientSubmodule w k) :=
  supportedSubmoduleBasis ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ)
    (F.realShiftedCoefficientSubmodule w k)
    {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}
    (F.realShiftedCoefficient_eq_span b ω hF w k)

@[simp] theorem realShiftedMonomialBasis_coe (w : σ → ℕ) (k : ℕ) (z : ShiftedMonomialIndex w ω k) :
    (F.realShiftedMonomialBasis b ω hF w k z : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) =
      (F.adaptedMonomialBasis b ω hF w).baseChange ℝ z.val :=
  supportedSubmoduleBasis_coe _ _ _ _ z

theorem realShiftedMonomialBasis_repr (w : σ → ℕ) (k : ℕ)
    (x : F.realShiftedCoefficientSubmodule w k) (z : ShiftedMonomialIndex w ω k) :
    (F.realShiftedMonomialBasis b ω hF w k).repr x z =
      ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr x.val z.val :=
  supportedSubmoduleBasis_repr _ _ _ _ x z

theorem realShiftedCoefficient_next_eq_span (w : σ → ℕ) (k : ℕ) :
    (F.realShiftedCoefficientSubmodule w (k + 1)).comap (F.realShiftedCoefficientSubmodule w k).subtype =
      Submodule.span ℝ (F.realShiftedMonomialBasis b ω hF w k ''
        {z | Finsupp.weight w z.val.val.1 + (k + 1) ≤ ω z.val.val.2}) := by
  have hP := F.realShiftedCoefficient_eq_span b ω hF w k
  have hQ := F.realShiftedCoefficient_eq_span b ω hF w (k + 1)
  have hdata := supportedSubmoduleBasis_comap_span
    ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ)
    (F.realShiftedCoefficientSubmodule w k) (F.realShiftedCoefficientSubmodule w (k + 1))
    {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}
    {z | Finsupp.weight w z.val.1 + (k + 1) ≤ ω z.val.2} hP hQ
  exact hdata

noncomputable def realFirstCoefficientBasis (w : σ → ℕ) :
    Basis (FirstCoefficientIndex w ω) ℝ (F.RealFirstCoefficientModule w) :=
  (supportedQuotientBasis (F.realShiftedMonomialBasis b ω hF w 1)
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype)
    {z | Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2}
    (F.realShiftedCoefficient_next_eq_span b ω hF w 1)).reindex (firstCoefficientSurvivorEquiv w ω)

@[simp] theorem realFirstCoefficientBasis_apply (w : σ → ℕ) (z : FirstCoefficientIndex w ω) :
    F.realFirstCoefficientBasis b ω hF w z =
      F.realFirstCoefficientMap w
        (F.realShiftedMonomialBasis b ω hF w 1 ((firstCoefficientSurvivorEquiv w ω).symm z).val) := by
  rw [realFirstCoefficientBasis, Basis.reindex_apply, supportedQuotientBasis_apply]
  rfl

theorem realFirstCoefficientBasis_repr_map (w : σ → ℕ)
    (x : F.realShiftedCoefficientSubmodule w 1) (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientMap w x) z =
      ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr x.val
        ((firstCoefficientSurvivorEquiv w ω).symm z).val.val := by
  rw [realFirstCoefficientBasis, Basis.repr_reindex_apply]
  change (supportedQuotientBasis _ _ _ _).repr
    (((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype).mkQ x) _ = _
  rw [supportedQuotientBasis_repr_mk, F.realShiftedMonomialBasis_repr]

theorem realFirstCoefficientBasis_polynomial_coordinate (w : σ → ℕ)
    (x : F.realShiftedCoefficientSubmodule w 1) (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientMap w x) z =
      (b.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w x.val) z.val.1) z.val.2 := by
  rw [F.realFirstCoefficientBasis_repr_map]
  exact (F.realAdaptedPolynomialTensor_coordinates w b ω hF x.val
    ((firstCoefficientSurvivorEquiv w ω).symm z).val.val).symm

end Erdos3.NilpotentLieFiltration

end

end OAI

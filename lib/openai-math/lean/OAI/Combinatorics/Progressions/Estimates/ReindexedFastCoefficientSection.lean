/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.FastCoefficientDerivativeCoordinates
import OAI.Combinatorics.Progressions.Linear.RationalSpanDerivativeSystem

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realFirstCoefficientHorizontal_grid (l : ℕ) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientGrid e ω hF w l x) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun
      (F.realFirstCoefficientHorizontal w x) ∈ realDenominatorGrid l := by
  obtain ⟨v, hv⟩ := hx
  refine ⟨fun i => v (F.horizontalCoefficientIndex e ω hF w i), ?_⟩
  funext i
  change (v (F.horizontalCoefficientIndex e ω hF w i) : ℝ) =
    (l : ℝ) * ((F.layerOneBasis e ω hF).baseChange ℝ).repr
      (F.realFirstCoefficientHorizontal w x) i
  rw [F.realFirstCoefficientHorizontal_coordinates]
  exact congrFun hv _

theorem realFirstCoefficientHorizontal_bound (T : σ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (x : F.RealFirstCoefficientModule w) (hx : F.FirstCoefficientSlowBound e ω hF w T M x) :
    ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun
      (F.realFirstCoefficientHorizontal w x)‖ ≤ M := by
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro i
  rw [Real.norm_eq_abs, Basis.equivFun_apply, F.realFirstCoefficientHorizontal_coordinates]
  simpa only [horizontalCoefficientIndex, monomialScale_zero, div_one] using
    hx (F.horizontalCoefficientIndex e ω hF w i)

omit [Fintype ι] in
theorem realHorizontalSection_constant_coordinate
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (z : FirstCoefficientIndex w ω) (hz : z.val.1 = 0) :
    (F.realFirstCoefficientBasis e ω hF w).repr (F.realFirstCoefficientHorizontalSection w x) z =
      ((F.layerOneBasis e ω hF).baseChange ℝ).repr x (layerOneIndexOfConstant ω w z hz) := by
  have h := F.realFirstCoefficientHorizontal_coordinates e ω hF w
    (F.realFirstCoefficientHorizontalSection w x) (layerOneIndexOfConstant ω w z hz)
  rw [F.realFirstCoefficientHorizontal_section, F.horizontalCoefficientIndex_of_constant] at h
  exact h.symm

omit [Fintype ι] in
theorem realHorizontalSection_nonconstant_coordinate
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (z : FirstCoefficientIndex w ω) (hz : z.val.1 ≠ 0) :
    (F.realFirstCoefficientBasis e ω hF w).repr (F.realFirstCoefficientHorizontalSection w x) z = 0 := by
  classical
  have h := F.realFirstCoefficientHorizontal_projector_repr e ω hF w
    (F.realFirstCoefficientHorizontalSection w x) z
  simpa only [F.realFirstCoefficientHorizontal_section, hz, ite_false] using h

theorem realHorizontalSection_slow_bound (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) {M : ℝ} (hM : 0 ≤ M)
    (hx : ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x‖ ≤ M) :
    F.FirstCoefficientSlowBound e ω hF w T M (F.realFirstCoefficientHorizontalSection w x) := by
  classical
  intro z
  by_cases hz : z.val.1 = 0
  · rw [F.realHorizontalSection_constant_coordinate e ω hF w x z hz,
      hz, monomialScale_zero, div_one]
    exact (norm_le_pi_norm (((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x)
      (layerOneIndexOfConstant ω w z hz)).trans hx
  · rw [F.realHorizontalSection_nonconstant_coordinate e ω hF w x z hz, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT _).le

theorem realHorizontalSection_grid (l : ℕ) (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (hx : ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    F.FirstCoefficientGrid e ω hF w l (F.realFirstCoefficientHorizontalSection w x) := by
  classical
  obtain ⟨v, hv⟩ := hx
  refine ⟨fun z => if hz : z.val.1 = 0 then v (layerOneIndexOfConstant ω w z hz) else 0, ?_⟩
  funext z
  change ((if hz : z.val.1 = 0 then v (layerOneIndexOfConstant ω w z hz) else 0 : ℤ) : ℝ) =
    (l : ℝ) * (F.realFirstCoefficientBasis e ω hF w).repr
      (F.realFirstCoefficientHorizontalSection w x) z
  by_cases hz : z.val.1 = 0
  · rw [dite_eq_left hz, F.realHorizontalSection_constant_coordinate e ω hF w x z hz]
    exact congrFun hv _
  · rw [dite_eq_right hz, F.realHorizontalSection_nonconstant_coordinate e ω hF w x z hz]
    simp only [Int.cast_zero, mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

section Bounds

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem FirstCoefficientSlowBound.mono (w : σ → ℕ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} (hMN : M ≤ N) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound e ω hF w T M x) :
    F.FirstCoefficientSlowBound e ω hF w T N x := by
  intro z
  exact (hx z).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT z.val.1).le)

end Bounds

variable {σ ι ν L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ν] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

local notation "E" => F.RealFirstCoefficientModule w
local notation "J" => F.realFirstCoefficientFastSubmodule w hw U

noncomputable def realFastCoefficientRepresentative (b : Basis ν ℝ (E ⧸ J))
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E) : (E ⧸ J) →ₗ[ℝ] E :=
  sectionMap.comp b.equivFun.toLinearMap

theorem realFastCoefficientRepresentative_mk (b : Basis ν ℝ (E ⧸ J))
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y) (x : E ⧸ J) :
    (J).mkQ (F.realFastCoefficientRepresentative w hw U b sectionMap x) = x := by
  change (J).mkQ (sectionMap (b.equivFun x)) = x
  rw [hsection, LinearEquiv.symm_apply_apply]

theorem realFastCoefficientRepresentative_horizontal (b : Basis ν ℝ (E ⧸ J))
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y) (x : E ⧸ J) :
    F.realFirstCoefficientHorizontal w (F.realFastCoefficientRepresentative w hw U b sectionMap x) =
      F.realFastCoefficientHorizontal w hw U x := by
  have h := congrArg (F.realFastCoefficientHorizontal w hw U)
    (F.realFastCoefficientRepresentative_mk w hw U b sectionMap hsection x)
  exact h

theorem realFastCoefficientRepresentative_bound
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis ν ℝ (E ⧸ J)) (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (rows : ν → FirstCoefficientIndex w ω) (T : σ → ℝ) {C M : ℝ}
    (hbound : ∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
      F.FirstCoefficientSlowBound e ω hF w T (C * M) (sectionMap y))
    (x : E ⧸ J) (hx : ∀ i, |b.equivFun x i| ≤ M / monomialScale T (rows i).val.1) :
    F.FirstCoefficientSlowBound e ω hF w T (C * M)
      (F.realFastCoefficientRepresentative w hw U b sectionMap x) := hbound (b.equivFun x) hx

theorem realFastCoefficientRepresentative_grid
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis ν ℝ (E ⧸ J)) (sectionMap : (ν → ℝ) →ₗ[ℝ] E) (l m : ℕ)
    (hgrid : ∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w m (sectionMap y))
    (x : E ⧸ J) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    F.FirstCoefficientGrid e ω hF w m
      (F.realFastCoefficientRepresentative w hw U b sectionMap x) := hgrid (b.equivFun x) hx

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι ν L : Type*} [Fintype ι] [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

local notation "E" => F.RealFirstCoefficientModule w
local notation "J" => F.realFirstCoefficientFastSubmodule w hw U
local notation "Hq" => F.realFastCoefficientHorizontal w hw U
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))

theorem realFastCoefficientHorizontal_section_norm_bound
    (b : Basis ν ℝ (E ⧸ J)) (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (rows : ν → FirstCoefficientIndex w ω) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ M, 0 ≤ M → ∀ y : ν → ℝ,
      (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF w T (C * M) (sectionMap y))
    (x : E ⧸ J) :
    ‖cH (Hq x)‖ ≤ C * ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) x‖ := by
  let N := basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
  let x' := F.realFastCoefficientRepresentative w hw U b sectionMap x
  have hcoords : ∀ i, |b.equivFun x i| ≤ ‖N x‖ / monomialScale T (rows i).val.1 :=
    (basisWeightedCoordinates_norm_le_iff b _ (fun i => monomialScale_pos T hT _)
      (norm_nonneg _) x).mp le_rfl
  have hx' : F.FirstCoefficientSlowBound e ω hF w T (C * ‖N x‖) x' :=
    F.realFastCoefficientRepresentative_bound w hw U e ω hF b sectionMap rows T
      (hbound ‖N x‖ (norm_nonneg _)) x hcoords
  have hhorizontal := F.realFastCoefficientRepresentative_horizontal w hw U b sectionMap hsection x
  calc
    ‖cH (Hq x)‖ = ‖cH (F.realFirstCoefficientHorizontal w x')‖ :=
      (congrArg (fun y => ‖cH y‖) hhorizontal).symm
    _ ≤ C * ‖N x‖ := F.realFirstCoefficientHorizontal_bound e ω hF w T
      (mul_nonneg hC (norm_nonneg _)) x' hx'

theorem realFastCoefficientHorizontal_section_grid
    (b : Basis ν ℝ (E ⧸ J)) (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (l m : ℕ)
    (hgrid : ∀ y : ν → ℝ, y ∈ realDenominatorGrid l →
      F.FirstCoefficientGrid e ω hF w m (sectionMap y))
    (x : E ⧸ J) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    cH (Hq x) ∈ realDenominatorGrid m := by
  have hx' := F.realFastCoefficientRepresentative_grid w hw U e ω hF b sectionMap l m hgrid x hx
  have hhorizontal := F.realFastCoefficientRepresentative_horizontal w hw U b sectionMap hsection x
  have hg := F.realFirstCoefficientHorizontal_grid e ω hF w m _ hx'
  exact (congrArg (fun y => cH y ∈ realDenominatorGrid m) hhorizontal).mp hg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

noncomputable def reindexCoordinateSection {ν E : Type*} [AddCommGroup E] [Module ℝ E]
    (R : (ν → ℝ) →ₗ[ℝ] E) (e : Equiv.Perm ν) : (ν → ℝ) →ₗ[ℝ] E where
  toFun y := R (fun i => y (e.symm i))
  map_add' _ _ := R.map_add _ _
  map_smul' r _ := R.map_smul r _

theorem reindexCoordinateSection_right_inverse {ν E Q : Type*} [Fintype ν]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup Q] [Module ℝ Q]
    (P : E →ₗ[ℝ] Q) (b : Basis ν ℝ Q) (R : (ν → ℝ) →ₗ[ℝ] E)
    (hR : ∀ y, P (R y) = b.equivFun.symm y) (e : Equiv.Perm ν) (y : ν → ℝ) :
    P (reindexCoordinateSection R e y) = (b.reindex e.symm).equivFun.symm y := by
  apply (b.reindex e.symm).equivFun.injective
  rw [LinearEquiv.apply_symm_apply, basis_reindex_equivFun]
  change (fun i => b.equivFun (P (R (fun j => y (e.symm j)))) (e i)) = y
  rw [hR, LinearEquiv.apply_symm_apply]
  funext i
  exact congrArg y (e.symm_apply_apply i)

namespace NilpotentLieFiltration

theorem exists_reindexed_fast_coefficient_section
    {σ ι ν L : Type*} [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (b : Basis ν ℝ (F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U))
    (rows : ν → FirstCoefficientIndex w ω) (R : (ν → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
    (δ : ℕ) (C : ℝ)
    (hproj : ∀ l x, F.FirstCoefficientGrid e ω hF w l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) ∈ realDenominatorGrid (δ * l))
    (hgrid : ∀ l y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w (δ * l) (R y))
    (hweighted : ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
      (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
        |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) i| ≤
          C * M / monomialScale T (rows i).val.1) ∧
      (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF w T (C * M) (R y)))
    (perm : Equiv.Perm ν) :
    ∃ R' : (ν → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      (∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R' y) =
        (b.reindex perm.symm).equivFun.symm y) ∧
      (∀ l x, F.FirstCoefficientGrid e ω hF w l x →
        (b.reindex perm.symm).equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) ∈
          realDenominatorGrid (δ * l)) ∧
      (∀ l y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w (δ * l) (R' y)) ∧
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
        (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
          |(b.reindex perm.symm).equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) i| ≤
            C * M / monomialScale T (rows (perm i)).val.1) ∧
        (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows (perm i)).val.1) →
          F.FirstCoefficientSlowBound e ω hF w T (C * M) (R' y)) := by
  refine ⟨reindexCoordinateSection R perm,
    reindexCoordinateSection_right_inverse _ b R hR perm, ?_, ?_, ?_⟩
  · intro l x hx
    exact basis_reindex_grid b perm (δ * l) _ (hproj l x hx)
  · intro l y hy
    exact hgrid l _ (realDenominatorGrid_comp l y hy perm.symm)
  · intro T hT M hM
    obtain ⟨hproj', hlift'⟩ := hweighted T hT M hM
    constructor
    · intro x hx i
      simpa only [basis_reindex_equivFun] using hproj' x hx (perm i)
    · intro y hy
      apply hlift' (fun i => y (perm.symm i))
      intro i
      simpa only [Equiv.apply_symm_apply] using hy (perm.symm i)

end NilpotentLieFiltration
end Erdos3

end

end OAI

/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realifiedSquarePolynomial_fst
    (p : VectorPolynomial σ ℚ F.realification.squareLieSubalgebra) :
    VectorPolynomial.map ((realificationLieHom F.squareFst).toLinearMap.restrictScalars ℚ)
      (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap p) =
        VectorPolynomial.map F.realification.squareFst.toLinearMap p := by
  apply coefficients.injective
  ext α
  simp only [coefficients_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  have h := F.realifiedSquareEquiv_fst (F.realifiedSquareEquiv.symm (coefficients p α))
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem realifiedSquarePolynomial_snd
    (p : VectorPolynomial σ ℚ F.realification.squareLieSubalgebra) :
    VectorPolynomial.map ((realificationLieHom F.squareSnd).toLinearMap.restrictScalars ℚ)
      (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap p) =
        VectorPolynomial.map F.realification.squareSnd.toLinearMap p := by
  apply coefficients.injective
  ext α
  simp only [coefficients_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  have h := F.realifiedSquareEquiv_snd (F.realifiedSquareEquiv.symm (coefficients p α))
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem realifiedSquarePolynomial_adapted (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ F.realification.squareLieSubalgebra)
    (hp : F.realification.squareFiltration.Adapted w p) :
    F.squareFiltration.realification.Adapted w
      (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap p) :=
  F.realification.squareFiltration.adapted_map F.squareFiltration.realification
    F.realifiedSquareEquiv.symm.toLinearMap
    (fun j x hx => (F.realifiedSquareEquiv_symm_mem_layer j x).mpr hx) w hp

end NilpotentLieFiltration

theorem exists_bounded_realified_square_polynomial (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (h : σ → ℚ) (f : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ r : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra),
          D.filtration.squareFiltration.realification.Adapted w r ∧
          VectorPolynomial.map
            ((realificationLieHom D.filtration.squareFst).toLinearMap.restrictScalars ℚ) r =
              normalizedShiftLog s h (-ε.coord) (-γ.coord) f.log ∧
          VectorPolynomial.map
            ((realificationLieHom D.filtration.squareSnd).toLinearMap.restrictScalars ℚ) r = f.log := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_normalized_square s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw h f
  obtain ⟨ε, γ, hγ, hε, r, hr, hf, hs⟩ := hnorm D p hp hD w hw h f
  refine ⟨ε, γ, hγ, hε, VectorPolynomial.map D.filtration.realifiedSquareEquiv.symm.toLinearMap r,
    D.filtration.realifiedSquarePolynomial_adapted w r hr, ?_, ?_⟩
  · rw [D.filtration.realifiedSquarePolynomial_fst]
    exact hf
  · rw [D.filtration.realifiedSquarePolynomial_snd]
    exact hs

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def realSquareFstPolynomialHom :
    F.squareFiltration.RealAdaptedPolynomialGroup w →* F.RealAdaptedPolynomialGroup w :=
  realificationMap (hnil := (F.squareFiltration.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot) (F.squareFstPolynomialMap w)

noncomputable def realSquareSndPolynomialHom :
    F.squareFiltration.RealAdaptedPolynomialGroup w →* F.RealAdaptedPolynomialGroup w :=
  realificationMap (hnil := (F.squareFiltration.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot) (F.squareSndPolynomialMap w)

theorem realSquareFstPolynomialHom_polynomial (r : F.squareFiltration.RealAdaptedPolynomialGroup w) :
    F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord =
      VectorPolynomial.map ((realificationLieHom F.squareFst).toLinearMap.restrictScalars ℚ)
        (F.squareFiltration.realAdaptedPolynomialMap w r.coord) :=
  F.squareFiltration.realFilteredPolynomialMap_polynomial F F.squareFst (fun _ _ hx => hx.1) w r.coord

theorem realSquareSndPolynomialHom_polynomial (r : F.squareFiltration.RealAdaptedPolynomialGroup w) :
    F.realAdaptedPolynomialMap w (F.realSquareSndPolynomialHom w r).coord =
      VectorPolynomial.map ((realificationLieHom F.squareSnd).toLinearMap.restrictScalars ℚ)
        (F.squareFiltration.realAdaptedPolynomialMap w r.coord) :=
  F.squareFiltration.realFilteredPolynomialMap_polynomial F F.squareSnd (fun _ _ hx => hx.2.1) w r.coord

theorem realSquarePolynomial_ext {r q : F.squareFiltration.RealAdaptedPolynomialGroup w}
    (hf : F.realSquareFstPolynomialHom w r = F.realSquareFstPolynomialHom w q)
    (hs : F.realSquareSndPolynomialHom w r = F.realSquareSndPolynomialHom w q) : r = q := by
  let P := (F.squareFstPolynomialMap w).toLinearMap.prod (F.squareSndPolynomialMap w).toLinearMap
  have hP : Function.Injective P := by
    intro x y hxy
    exact F.square_polynomial_ext w (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  have hPR := Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) P hP
  apply NilpotentLieBCHGroup.ext
  apply hPR
  apply (TensorProduct.prodRight ℚ ℝ ℝ (F.adaptedLieSubalgebra w) (F.adaptedLieSubalgebra w)).injective
  change TensorProduct.prodRight ℚ ℝ ℝ _ _ (P.baseChange ℝ r.coord) =
    TensorProduct.prodRight ℚ ℝ ℝ _ _ (P.baseChange ℝ q.coord)
  rw [realification_prod, realification_prod]
  exact Prod.ext (congrArg NilpotentLieBCHGroup.coord hf) (congrArg NilpotentLieBCHGroup.coord hs)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem exists_realSquarePolynomial_lift (p : F.squareFiltration.realification.adaptedLieSubalgebra w) :
    ∃ r : F.squareFiltration.RealAdaptedPolynomialGroup w,
      F.squareFiltration.realAdaptedPolynomialMap w r.coord = p.val ∧
      F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord =
        VectorPolynomial.map ((realificationLieHom F.squareFst).toLinearMap.restrictScalars ℚ) p.val ∧
      F.realAdaptedPolynomialMap w (F.realSquareSndPolynomialHom w r).coord =
        VectorPolynomial.map ((realificationLieHom F.squareSnd).toLinearMap.restrictScalars ℚ) p.val := by
  obtain ⟨x, hx⟩ := F.squareFiltration.realAdaptedPolynomialTensor_surjective w
    (F.adaptedSquareBasis b ω (hF 2)) (squareBasisWeight ω) (F.adaptedSquareBasis_layers b ω hF) p
  have hp := congrArg (fun z : F.squareFiltration.realification.adaptedLieSubalgebra w => z.val) hx
  change F.squareFiltration.realAdaptedPolynomialMap w x = p.val at hp
  refine ⟨⟨x⟩, hp, ?_, ?_⟩
  · rw [F.realSquareFstPolynomialHom_polynomial, hp]
  · rw [F.realSquareSndPolynomialHom_polynomial, hp]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedPolynomialMap_coefficient
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedPolynomialMap w x) α = (F.adaptedCoefficientMap w α).baseChange ℝ x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r p => rw [F.realAdaptedPolynomialMap_coefficient_tmul]; rfl

include b ω hF in
theorem realNormalizedRelative_mem_iff_tensor
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    x ∈ (F.normalizedRelativeSubmodule w).baseChange ℝ ↔
      F.realAdaptedPolynomialTensor w x ∈ F.realification.normalizedRelativeSubmodule w := by
  change x ∈ ((F.shiftedAdaptedIdeal w).toSubmodule ⊓
    (F.layer 2).comap (F.adaptedCoefficientMap w 0)).baseChange ℝ ↔ _
  rw [realification_inf, realification_comap]
  change (x ∈ F.realShiftedCoefficientSubmodule w 1 ∧
    (F.adaptedCoefficientMap w 0).baseChange ℝ x ∈ F.realification.layer 2) ↔
    (F.realAdaptedPolynomialTensor w x ∈ F.realification.shiftedPolynomialIdeal w 1 ∧
      coefficients (F.realAdaptedPolynomialMap w x) 0 ∈ F.realification.layer 2)
  rw [F.realShiftedCoefficient_mem_iff_tensor b ω hF,
    F.realAdaptedPolynomialMap_coefficient]

include b ω hF in
theorem realNormalizedRelative_polynomial_surjective
    (p : F.realification.normalizedRelativeSubmodule w) :
    ∃ x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w,
      F.realAdaptedPolynomialTensor w ((F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x) = p.val := by
  obtain ⟨x, hx⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p.val
  have hmem : x ∈ (F.normalizedRelativeSubmodule w).baseChange ℝ := by
    apply (F.realNormalizedRelative_mem_iff_tensor b ω hF w x).mpr
    rw [hx]
    exact p.property
  let y := (realificationSubmoduleEquiv (F.normalizedRelativeSubmodule w)).symm ⟨x, hmem⟩
  have hy : (F.normalizedRelativeSubmodule w).subtype.baseChange ℝ y = x :=
    congrArg Subtype.val ((realificationSubmoduleEquiv (F.normalizedRelativeSubmodule w)).apply_symm_apply ⟨x, hmem⟩)
  exact ⟨y, by rw [hy]; exact hx⟩

theorem realFirstCoefficientOfPolynomial_normalized
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realFirstCoefficientOfPolynomial b ω hF w
      (F.realAdaptedPolynomialMap w ((F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x)) =
      F.realNormalizedFirstCoefficientMap w x := by
  rw [F.realNormalizedFirstCoefficientMap_eq, ← F.realNormalizedRelativeInFirst_coe]
  exact F.realFirstCoefficientOfPolynomial_map b ω hF w _

theorem realReducedRelativeCoefficient_of_polynomial (hw : ∀ i, 0 < w i)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hx : F.realReducedRelativeSquareSymbolMap w hw x = (F.reducedSquareRealRelativePart w g).coord) :
    F.realReducedRelativeCoefficient w hw g =
      F.realFirstCoefficientOfPolynomial b ω hF w
        (F.realAdaptedPolynomialMap w ((F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x)) := by
  rw [F.realFirstCoefficientOfPolynomial_normalized]
  exact (F.realReducedRelativeCoefficient_of_preimage w hw g x hx).symm

variable [Fintype σ]

include b ω hF in
theorem exists_real_normalizedRelative_preimage (h : σ → ℚ) (e m : ℝ ⊗[ℚ] L)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hzero : coefficients (normalizedShiftLog (s + 1) h (-e) (-m)
      (F.realAdaptedPolynomialMap (fun _ => 1) g.coord) -
        F.realAdaptedPolynomialMap (fun _ => 1) g.coord) 0 ∈ F.realification.layer 2) :
    ∃ x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule (fun _ : σ => 1),
      F.realAdaptedPolynomialTensor (fun _ => 1)
        ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
          F.realification.normalizedRelativeLog h e m
            (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord) ∧
      F.realNormalizedFirstCoefficientMap (fun _ => 1) x =
        F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          F.realFirstCoefficientConstant (fun _ => 1) e -
          F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) := by
  have hmem := F.realification.normalizedRelativeLog_mem h e m
    (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord) hzero
  obtain ⟨x, hx⟩ := F.realNormalizedRelative_polynomial_surjective b ω hF (fun _ => 1) ⟨_, hmem⟩
  refine ⟨x, hx, ?_⟩
  have hc := congrArg (fun p : F.realification.adaptedLieSubalgebra (fun _ : σ => 1) => p.val) hx
  have he := F.realFirstCoefficientOfPolynomial_normalized b ω hF (fun _ => 1) x
  change F.realAdaptedPolynomialMap (fun _ => 1)
      ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
    (F.realification.normalizedRelativeLog h e m
      (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val at hc
  rw [hc] at he
  exact he.symm.trans (F.realFirstCoefficientOfPolynomial_normalizedRelativeLog b ω hF h e m g)

include b ω hF in
theorem real_normalized_square_coefficient_identity (h : σ → ℚ) (e m : ℝ ⊗[ℚ] L)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (Q : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule (fun _ : σ => 1))
    (hQ : F.realReducedRelativeSquareSymbolMap (fun _ => 1) (fun _ => Nat.zero_lt_one) x =
      (F.reducedSquareRealRelativePart (fun _ => 1) Q).coord)
    (hx : F.realAdaptedPolynomialTensor (fun _ => 1)
        ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
      F.realification.normalizedRelativeLog h e m (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)) :
    F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
        F.realFirstCoefficientConstant (fun _ => 1) e -
        F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) =
      F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) Q := by
  rw [F.realReducedRelativeCoefficient_of_polynomial b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) Q x hQ]
  have hc := congrArg (fun p : F.realification.adaptedLieSubalgebra (fun _ : σ => 1) => p.val) hx
  change F.realAdaptedPolynomialMap (fun _ => 1)
      ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
    (F.realification.normalizedRelativeLog h e m
      (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val at hc
  rw [hc]
  exact (F.realFirstCoefficientOfPolynomial_normalizedRelativeLog b ω hF h e m g).symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def realSquareDiagonalPolynomialHom :
    F.RealAdaptedPolynomialGroup w →* F.squareFiltration.RealAdaptedPolynomialGroup w :=
  realificationMap (hnil := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := (F.squareFiltration.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (F.squareDiagonalPolynomialMap w)

noncomputable def realRelativeSquarePolynomial (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.squareFiltration.RealAdaptedPolynomialGroup w :=
  ⟨(F.relativeSquareLift w hw).baseChange ℝ x⟩

theorem realSquareFstPolynomialHom_diagonal (g : F.RealAdaptedPolynomialGroup w) :
    F.realSquareFstPolynomialHom w (F.realSquareDiagonalPolynomialHom w g) = g := by
  have hcomp : (F.squareFstPolynomialMap w).toLinearMap.comp
      (F.squareDiagonalPolynomialMap w).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro p
    exact F.squareFstPolynomialMap_diagonal w p
  apply NilpotentLieBCHGroup.ext
  change (F.squareFstPolynomialMap w).toLinearMap.baseChange ℝ
    ((F.squareDiagonalPolynomialMap w).toLinearMap.baseChange ℝ g.coord) = g.coord
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_id,
    LinearMap.id_apply]

theorem realSquareSndPolynomialHom_diagonal (g : F.RealAdaptedPolynomialGroup w) :
    F.realSquareSndPolynomialHom w (F.realSquareDiagonalPolynomialHom w g) = g := by
  have hcomp : (F.squareSndPolynomialMap w).toLinearMap.comp
      (F.squareDiagonalPolynomialMap w).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro p
    exact F.squareSndPolynomialMap_diagonal w p
  apply NilpotentLieBCHGroup.ext
  change (F.squareSndPolynomialMap w).toLinearMap.baseChange ℝ
    ((F.squareDiagonalPolynomialMap w).toLinearMap.baseChange ℝ g.coord) = g.coord
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_id,
    LinearMap.id_apply]

theorem realSquareFstPolynomialHom_relative (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realSquareFstPolynomialHom w (F.realRelativeSquarePolynomial w hw x) =
      (⟨(F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x⟩ : F.RealAdaptedPolynomialGroup w) := by
  have hcomp : (F.squareFstPolynomialMap w).toLinearMap.comp (F.relativeSquareLift w hw) =
      (F.normalizedRelativeSubmodule w).subtype := by
    apply LinearMap.ext
    intro p
    exact F.squareFstPolynomialMap_relative w hw p
  apply NilpotentLieBCHGroup.ext
  change (F.squareFstPolynomialMap w).toLinearMap.baseChange ℝ
    ((F.relativeSquareLift w hw).baseChange ℝ x) = _
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp]

theorem realSquareSndPolynomialHom_relative (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realSquareSndPolynomialHom w (F.realRelativeSquarePolynomial w hw x) = 1 := by
  have hcomp : (F.squareSndPolynomialMap w).toLinearMap.comp (F.relativeSquareLift w hw) = 0 := by
    apply LinearMap.ext
    intro p
    exact F.squareSndPolynomialMap_relative w hw p
  apply NilpotentLieBCHGroup.ext
  change (F.squareSndPolynomialMap w).toLinearMap.baseChange ℝ
    ((F.relativeSquareLift w hw).baseChange ℝ x) = 0
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_zero,
    LinearMap.zero_apply]

theorem realSquarePolynomial_factorization (hw : ∀ i, 0 < w i)
    (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (g : F.RealAdaptedPolynomialGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hf : F.realSquareFstPolynomialHom w r =
      (⟨(F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x⟩ : F.RealAdaptedPolynomialGroup w) * g)
    (hs : F.realSquareSndPolynomialHom w r = g) :
    r = F.realRelativeSquarePolynomial w hw x * F.realSquareDiagonalPolynomialHom w g := by
  apply F.realSquarePolynomial_ext w
  · rw [map_mul, F.realSquareFstPolynomialHom_relative, F.realSquareFstPolynomialHom_diagonal, hf]
  · rw [map_mul, F.realSquareSndPolynomialHom_relative, F.realSquareSndPolynomialHom_diagonal, one_mul, hs]

theorem realSquareDifference_mem_two (x : ℝ ⊗[ℚ] F.squareLieSubalgebra) :
    realificationLieHom F.squareFst x - realificationLieHom F.squareSnd x ∈ F.realification.layer 2 := by
  rw [← F.realifiedSquareEquiv_fst, ← F.realifiedSquareEquiv_snd]
  exact (F.realification.mem_squareLieSubalgebra (F.realifiedSquareEquiv x).val).mp
    (F.realifiedSquareEquiv x).property

theorem realSquarePolynomial_horizontal (r : F.squareFiltration.RealAdaptedPolynomialGroup w) :
    coefficients (F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord -
      F.realAdaptedPolynomialMap w (F.realSquareSndPolynomialHom w r).coord) 0 ∈ F.realification.layer 2 := by
  rw [map_sub, Finsupp.sub_apply, F.realSquareFstPolynomialHom_polynomial,
    F.realSquareSndPolynomialHom_polynomial, coefficients_map, coefficients_map]
  exact F.realSquareDifference_mem_two _

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem realAdaptedPolynomialGroupHom_injective :
    Function.Injective (F.realAdaptedPolynomialGroupHom w) := by
  intro g h hgh
  apply NilpotentLieBCHGroup.ext
  apply F.realAdaptedPolynomialTensor_injective b ω hF w
  exact congrArg NilpotentLieBCHGroup.coord hgh

end Erdos3.NilpotentLieFiltration

end

end OAI

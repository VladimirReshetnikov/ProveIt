import OAI.Combinatorics.Progressions.Linear.NativeMarkedKernelFreezing
import OAI.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module NilpotentLieBCHGroup
open scoped TensorProduct
variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)

theorem real_linear_section_rightInverse (φ : L →ₗ⁅ℚ⁆ M) (S : M →ₗ[ℚ] L)
    (hS : Function.RightInverse S φ) :
    Function.RightInverse (fun y : G.realification.Group =>
      (⟨S.baseChange ℝ y.coord⟩ : F.realification.Group))
      (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ) := by
  have hcomp : φ.toLinearMap.comp S = LinearMap.id := LinearMap.ext hS
  have hcompR := congrArg (fun f : M →ₗ[ℚ] M => f.baseChange ℝ) hcomp
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hcompR
  intro y
  apply NilpotentLieBCHGroup.ext
  exact DFunLike.congr_fun hcompR y.coord

variable (w : σ → ℕ)

noncomputable def frozenMarkedLeft (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (EF : (G.realification.adaptedPolynomialFiltration w).Group)
    (kE : F.realification.Group) :
    (F.realification.adaptedPolynomialFiltration w).Group :=
  F.realification.adaptedConstantGroupHom w kE *
    F.filteredRealPolynomialSection G w S hS EF

noncomputable def frozenMarkedRight (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (kR : F.realification.Group) :
    (F.realification.adaptedPolynomialFiltration w).Group :=
  F.filteredRealPolynomialSection G w S hS RF *
    F.realification.adaptedConstantGroupHom w kR

theorem frozenMarked_factors_mark
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (hsection : Function.RightInverse S φ)
    (EF RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (kE kR : F.realification.Group)
    (hkE : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kR = 1) :
    F.realPolynomialGroupMap G φ hφ w (F.frozenMarkedLeft G w S hS EF kE) = EF ∧
    F.realPolynomialGroupMap G φ hφ w (F.frozenMarkedRight G w S hS RF kR) = RF := by
  simp only [frozenMarkedLeft, frozenMarkedRight, map_mul,
    realPolynomialGroupMap_constant, hkE, hkR, map_one, one_mul, mul_one,
    realPolynomialGroupMap_filteredSection, hsection, and_self]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.Niltest
open NilpotentLieBCHGroup
open scoped TensorProduct NNReal
variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem observable_frozenMarked_polynomial_factors
    (T : D.Niltest w) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse S φ)
    (g E P R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (hfac : E * P * R = g)
    (EF RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (kE kR : D.RealGroup)
    (hkE : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kR = 1)
    (z : σ → ℝ)
    (hcoset : (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w z
      ((D.filtration.filteredRealPolynomialSection G w S hS RF)⁻¹ * R)) : D.Space) =
        QuotientGroup.mk kR) :
    letI := rightMetricSpace
      (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    ‖T.observable (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w z g)) -
      T.observable (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w z
        (D.filtration.frozenMarkedLeft G w S hS EF kE * P *
          D.filtration.frozenMarkedRight G w S hS RF kR)))‖ ≤
      (T.lipBound : ℝ) * dist
        (D.filtration.adaptedPolynomialRealValueHom w z
          (E * (D.filtration.filteredRealPolynomialSection G w S hS EF)⁻¹)) kE := by
  let ρ := fun y : G.realification.Group =>
    (⟨S.baseChange ℝ y.coord⟩ : D.RealGroup)
  have he := D.filtration.filteredRealPolynomialSection_value G w S hS EF z
  have hr := D.filtration.filteredRealPolynomialSection_value G w S hS RF z
  have hc : (QuotientGroup.mk
      ((ρ (G.adaptedPolynomialRealValueHom w z RF))⁻¹ *
        D.filtration.adaptedPolynomialRealValueHom w z R) : D.Space) =
      QuotientGroup.mk kR := by
    simpa only [map_mul, map_inv, hr] using hcoset
  have hout := T.observable_freeze_marked_kernel_factors
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ) ρ
    (D.filtration.real_linear_section_rightInverse G φ S hsection)
    (D.filtration.adaptedPolynomialRealValueHom w z E)
    (D.filtration.adaptedPolynomialRealValueHom w z P)
    (D.filtration.adaptedPolynomialRealValueHom w z R)
    (G.adaptedPolynomialRealValueHom w z EF) (G.adaptedPolynomialRealValueHom w z RF)
    kE kR hkE hkR hc
  rw [← hfac]
  simpa only [NilpotentLieFiltration.frozenMarkedLeft,
    NilpotentLieFiltration.frozenMarkedRight, map_mul, map_inv,
    NilpotentLieFiltration.adaptedPolynomialRealValueHom_constant, he, hr] using hout.2.2

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

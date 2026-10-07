/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.ProductOrbitCongruence
import OAI.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)

theorem mem_native_refiltration_layer (j : ℕ)
    (x : ℝ ⊗[ℚ] F.gradedRefiltrationSubalgebra W) :
    x ∈ (F.gradedRefiltration W).realification.layer j ↔
      realificationLieHom (F.gradedRefiltrationSubalgebra W).incl x ∈
        F.realGradedRefiltrationLayer W j := by
  change x ∈ ((F.gradedRefiltrationLayer W j).comap
    (F.gradedRefiltrationSubalgebra W).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  rfl

theorem exists_native_refiltered_orbit (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) :
    ∃ q : (F.gradedRefiltration W).realification.PolynomialOrbit w,
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p ∧ coefficients q.log 0 = 0 := by
  obtain ⟨q₀, _, hq₀, hz₀⟩ := F.exists_refiltered_polynomial_of_coefficients w W hw p hp hzero
  let H := F.gradedRefiltrationSubalgebra W
  let inc := (realLieHomToRat (realificationLieHom H.incl)).toLinearMap
  let lift : F.realGradedRefiltrationSubalgebra W →ₗ[ℚ] (ℝ ⊗[ℚ] H) :=
    (realificationSubmoduleEquiv H.toSubmodule).symm.toLinearMap.restrictScalars ℚ
  have hcomp : inc.comp lift = (F.realGradedRefiltrationSubalgebra W).incl.toLinearMap := by
    ext x
    exact congrArg Subtype.val ((realificationSubmoduleEquiv H.toSubmodule).apply_symm_apply x)
  let q := VectorPolynomial.map lift q₀
  have hmap : VectorPolynomial.map inc q = p := by
    apply coefficients.injective
    ext α
    dsimp only [q]
    rw [coefficients_map, coefficients_map]
    change (inc.comp lift) (coefficients q₀ α) = coefficients p α
    rw [hcomp]
    simpa only [coefficients_map] using congrArg (fun r => coefficients r α) hq₀
  have hadapted : (F.gradedRefiltration W).realification.Adapted w q := by
    apply ((F.gradedRefiltration W).realification.adapted_iff_coefficients w q).mpr
    intro α
    rw [F.mem_native_refiltration_layer]
    have h := congrArg (fun r => coefficients r α) hmap
    rw [coefficients_map] at h
    change inc (coefficients q α) ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α)
    rw [h]
    exact hp α
  refine ⟨polynomialOrbitOfLog q hadapted, hmap, ?_⟩
  change coefficients (VectorPolynomial.map lift q₀) 0 = 0
  rw [coefficients_map, hz₀, map_zero]

theorem native_refiltered_orbit_real_value (w : σ → ℕ)
    (q : (F.gradedRefiltration W).realification.PolynomialOrbit w)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hmap : VectorPolynomial.map
      (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      q.log = p) (t : σ → ℝ) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
      ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t q) =
        (⟨eval₂ t p⟩ : F.realification.Group) := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (F.gradedRefiltrationSubalgebra W).incl (eval₂ t q.log) = eval₂ t p
  rw [← hmap]
  exact (eval₂_map (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl).toLinearMap t q.log).symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

include hφ in
theorem realificationLieHom_mem_layer (j : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : x ∈ F.realification.layer j) :
    realificationLieHom φ x ∈ G.realification.layer j :=
  baseChange_mem_of_mapsTo (F.layer j) (G.layer j) φ.toLinearMap (hφ j) hx

noncomputable def realPolynomialGroupMap :
    (F.realification.adaptedPolynomialFiltration w).Group →*
      (G.realification.adaptedPolynomialFiltration w).Group :=
  mapOfSteps (hL := (F.realification.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := (G.realification.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (F.realification.filteredPolynomialMap G.realification
      (realLieHomToRat (realificationLieHom φ)) (F.realificationLieHom_mem_layer G φ hφ) w)

theorem realPolynomialGroupMap_log
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    ((F.realPolynomialGroupMap G φ hφ w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) =
      VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
        (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

theorem realPolynomialGroupMap_value
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (x : σ → ℝ) :
    G.adaptedPolynomialRealValueHom w x (F.realPolynomialGroupMap G φ hφ w g) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
        (F.adaptedPolynomialRealValueHom w x g) := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_map (realificationLieHom φ).toLinearMap x
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))

theorem realPolynomialGroupMap_constant (c : F.realification.Group) :
    F.realPolynomialGroupMap G φ hφ w (F.realification.adaptedConstantGroupHom w c) =
      G.realification.adaptedConstantGroupHom w
        (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
          (hM := G.lowerCentralSeries_eq_bot) φ c) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
    (monomial 0 c.coord) = monomial 0 (realificationLieHom φ c.coord)
  exact map_monomial _ _ _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)

theorem refiltration_coefficients_mem_first_of_constant
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hconstant : coefficients p 0 ∈ F.realGradedRefiltrationLayer W 1) :
    ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W 1 := by
  intro α
  by_cases hα : α = 0
  · simpa only [hα] using hconstant
  · exact F.realGradedRefiltrationLayer_antitone W
      (positive_weight_of_ne_zero w hw hα) (hp α)

theorem exists_native_refiltered_orbit_of_constant
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hconstant : coefficients p 0 ∈ F.realGradedRefiltrationLayer W 1) :
    ∃ q : (F.gradedRefiltration W).realification.PolynomialOrbit w,
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p := by
  have hfirst := F.refiltration_coefficients_mem_first_of_constant W w hw p hp hconstant
  have hcoeff : ∀ α, coefficients p α ∈ (F.realGradedRefiltrationSubalgebra W).toSubmodule := by
    intro α
    exact (F.mem_realGradedRefiltrationSubalgebra W _).mpr (hfirst α)
  let q₀ := restrictCoefficients (F.realGradedRefiltrationSubalgebra W).toSubmodule p hcoeff
  have hq₀ : VectorPolynomial.map
      (F.realGradedRefiltrationSubalgebra W).incl.toLinearMap q₀ = p :=
    map_restrictCoefficients (F.realGradedRefiltrationSubalgebra W).toSubmodule p hcoeff
  let H := F.gradedRefiltrationSubalgebra W
  let inc := (realLieHomToRat (realificationLieHom H.incl)).toLinearMap
  let lift : F.realGradedRefiltrationSubalgebra W →ₗ[ℚ] (ℝ ⊗[ℚ] H) :=
    (realificationSubmoduleEquiv H.toSubmodule).symm.toLinearMap.restrictScalars ℚ
  have hcomp : inc.comp lift = (F.realGradedRefiltrationSubalgebra W).incl.toLinearMap := by
    ext x
    exact congrArg Subtype.val ((realificationSubmoduleEquiv H.toSubmodule).apply_symm_apply x)
  let q := VectorPolynomial.map lift q₀
  have hmap : VectorPolynomial.map inc q = p := by
    apply coefficients.injective
    ext α
    dsimp only [q]
    rw [coefficients_map, coefficients_map]
    change (inc.comp lift) (coefficients q₀ α) = coefficients p α
    rw [hcomp]
    simpa only [coefficients_map] using congrArg (fun r => coefficients r α) hq₀
  have hadapted : (F.gradedRefiltration W).realification.Adapted w q := by
    apply ((F.gradedRefiltration W).realification.adapted_iff_coefficients w q).mpr
    intro α
    rw [F.mem_native_refiltration_layer]
    have h := congrArg (fun r => coefficients r α) hmap
    rw [coefficients_map] at h
    change inc (coefficients q α) ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α)
    rw [h]
    exact hp α
  exact ⟨polynomialOrbitOfLog q hadapted, hmap⟩

theorem exists_native_refiltered_orbit_real_values_of_constant
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hconstant : coefficients p 0 ∈ F.realGradedRefiltrationLayer W 1) :
    ∃ q : (F.gradedRefiltration W).realification.PolynomialOrbit w,
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t q) =
          (⟨eval₂ t p⟩ : F.realification.Group) := by
  obtain ⟨q, hq⟩ := F.exists_native_refiltered_orbit_of_constant W w hw p hp hconstant
  exact ⟨q, hq, fun t => F.native_refiltered_orbit_real_value W w q p hq t⟩

theorem exists_native_pointwise_refiltered_orbit_of_constant
    {ι : Type*} (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : F.realification.adaptedLieSubalgebra w)
    (hconstant : coefficients (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
      F.realGradedRefiltrationLayer W 1)
    (hW : ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realPolynomialSymbolMap b ω hlayers w p)) ∈ realificationLieSubalgebra W) :
    ∃ q : (F.gradedRefiltration W).realification.PolynomialOrbit w,
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t q) =
          (⟨eval₂ t (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))⟩ : F.realification.Group) :=
  F.exists_native_refiltered_orbit_real_values_of_constant W w hw p
    ((F.real_symbol_values_iff_refiltration_coefficients b ω hlayers w W p).mp hW) hconstant

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  (b : Basis ι ℚ L) (e : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (ν : κ → ι)
  (hν : ∀ x k, e.repr (φ x) k = b.repr x (ν k))

include hν in
theorem realificationLieHom_repr_of_coordinate (x : ℝ ⊗[ℚ] L) (k : κ) :
    (e.baseChange ℝ).repr (realificationLieHom φ x) k = (b.baseChange ℝ).repr x (ν k) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp only [realificationLieHom_tmul, Basis.baseChange_repr_tmul, hν]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

namespace NilpotentLieFiltration

variable {σ : Type*} {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

include hν in
theorem realPolynomialGroupMap_slow (T : σ → ℝ) (R : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T R g) :
    G.PolynomialSlowBound e w T R (F.realPolynomialGroupMap G φ hφ w g) := by
  intro α k
  change |(e.baseChange ℝ).repr (coefficients
    ((F.realPolynomialGroupMap G φ hφ w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) α) k| ≤ _
  rw [realPolynomialGroupMap_log, coefficients_map]
  change |(e.baseChange ℝ).repr (realificationLieHom φ
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α)) k| ≤ _
  rw [realificationLieHom_repr_of_coordinate b e φ ν hν]
  exact hg α (ν k)

include hν in
theorem realPolynomialGroupMap_rational (q : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w q g) :
    G.PolynomialRationalGrid e w q (F.realPolynomialGroupMap G φ hφ w g) := by
  obtain ⟨z, hz⟩ := hg
  refine ⟨fun x => z (x.1, ν x.2), ?_⟩
  funext x
  change (z (x.1, ν x.2) : ℝ) = (q : ℝ) * (e.baseChange ℝ).repr
    (coefficients ((F.realPolynomialGroupMap G φ hφ w g).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) x.1) x.2
  rw [realPolynomialGroupMap_log, coefficients_map]
  change (z (x.1, ν x.2) : ℝ) = (q : ℝ) * (e.baseChange ℝ).repr
    (realificationLieHom φ (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) x.1)) x.2
  rw [realificationLieHom_repr_of_coordinate b e φ ν hν]
  exact congrFun hz (x.1, ν x.2)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (w : σ → ℕ)

noncomputable def filteredRealPolynomialSection (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (g : (G.realification.adaptedPolynomialFiltration w).Group) :
    (F.realification.adaptedPolynomialFiltration w).Group :=
  ⟨⟨map ((S.baseChange ℝ).restrictScalars ℚ)
      (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)), by
    intro α
    rw [coefficients_map]
    exact baseChange_mem_of_mapsTo (G.layer (Finsupp.weight w α))
      (F.layer (Finsupp.weight w α)) S (hS _) (g.coord.property α)⟩⟩

theorem filteredRealPolynomialSection_value (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (g : (G.realification.adaptedPolynomialFiltration w).Group) (z : σ → ℝ) :
    F.adaptedPolynomialRealValueHom w z (F.filteredRealPolynomialSection G w S hS g) =
      ⟨S.baseChange ℝ (G.adaptedPolynomialRealValueHom w z g).coord⟩ := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_map (S.baseChange ℝ) z (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))

variable (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem realPolynomialGroupMap_filteredSection (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (hsection : Function.RightInverse S φ)
    (g : (G.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialGroupMap G φ hφ w (F.filteredRealPolynomialSection G w S hS g) = g := by
  have hcomp : φ.toLinearMap.comp S = LinearMap.id := LinearMap.ext hsection
  have hcompR := congrArg
    (fun f : M →ₗ[ℚ] M => f.baseChange ℝ) hcomp
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hcompR
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  apply coefficients.injective
  ext α
  change coefficients (map ((φ.toLinearMap.baseChange ℝ).restrictScalars ℚ)
    (map ((S.baseChange ℝ).restrictScalars ℚ)
      (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)))) α = _
  rw [coefficients_map, coefficients_map]
  exact DFunLike.congr_fun hcompR _

theorem coefficient_mem_kernel_of_realPolynomialGroupMap_eq_one
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.realPolynomialGroupMap G φ hφ w g = 1) (α : σ →₀ ℕ) :
    coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      (LinearMap.ker φ.toLinearMap).baseChange ℝ := by
  rw [real_baseChange_ker]
  change φ.toLinearMap.baseChange ℝ (coefficients
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) = 0
  have hc := congrArg (fun q : (G.realification.adaptedPolynomialFiltration w).Group =>
    coefficients (q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) α) hg
  change coefficients (map ((φ.toLinearMap.baseChange ℝ).restrictScalars ℚ)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) α = coefficients 0 α at hc
  simpa only [coefficients_map, LinearMap.restrictScalars_apply, map_zero,
    Finsupp.zero_apply] using hc

theorem marked_kernel_polynomial_factors
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (hsection : Function.RightInverse S φ)
    (E R : (F.realification.adaptedPolynomialFiltration w).Group)
    (EF RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (hE : F.realPolynomialGroupMap G φ hφ w E = EF)
    (hR : F.realPolynomialGroupMap G φ hφ w R = RF) :
    let ρ := F.filteredRealPolynomialSection G w S hS
    let KE := E * (ρ EF)⁻¹
    let KR := (ρ RF)⁻¹ * R
    E = KE * ρ EF ∧ R = ρ RF * KR ∧
      F.realPolynomialGroupMap G φ hφ w KE = 1 ∧
      F.realPolynomialGroupMap G φ hφ w KR = 1 ∧
      (∀ α, coefficients (KE.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
        (LinearMap.ker φ.toLinearMap).baseChange ℝ) ∧
      ∀ α, coefficients (KR.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
        (LinearMap.ker φ.toLinearMap).baseChange ℝ := by
  intro ρ KE KR
  have hKE : F.realPolynomialGroupMap G φ hφ w KE = 1 := by
    dsimp only [KE, ρ]
    rw [map_mul, map_inv, hE,
      F.realPolynomialGroupMap_filteredSection G w φ hφ S hS hsection EF, mul_inv_cancel]
  have hKR : F.realPolynomialGroupMap G φ hφ w KR = 1 := by
    dsimp only [KR, ρ]
    rw [map_mul, map_inv, hR,
      F.realPolynomialGroupMap_filteredSection G w φ hφ S hS hsection RF, inv_mul_cancel]
  refine ⟨by dsimp only [KE]; group, by dsimp only [KR]; group, hKE, hKR, ?_, ?_⟩
  · exact F.coefficient_mem_kernel_of_realPolynomialGroupMap_eq_one G w φ hφ KE hKE
  · exact F.coefficient_mem_kernel_of_realPolynomialGroupMap_eq_one G w φ hφ KR hKR

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t e : ℕ} (F : NilpotentLieFiltration L s)
  (W : LieSubalgebra ℚ F.AssociatedGraded)
  (E : RationalFilteredNilmanifold (F.gradedRefiltrationSubalgebra W) s e)
  (hEF : E.filtration = F.gradedRefiltration W) (w : σ → ℕ)

include hEF in
theorem exists_model_refiltered_polynomial (hw : ∀ i, 0 < w i)
    (b : (F.realification.adaptedPolynomialFiltration w).Group)
    (hb : ∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hb0 : coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0) :
    ∃ g : E.filtration.realification.PolynomialOrbit w,
      ∀ x : σ → ℤ,
        realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
          (E.filtration.realification.polynomialOrbitEval w x g) =
            F.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b := by
  rw [hEF]
  obtain ⟨g, hg, _⟩ := F.exists_native_refiltered_orbit W w hw
    (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) hb hb0
  refine ⟨g, ?_⟩
  intro x
  rw [← polynomialOrbitRealEval_integer]
  exact F.native_refiltered_orbit_real_value W w g _ hg _

theorem refiltered_polynomial_projection (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : (F.realification.adaptedPolynomialFiltration w).Group)
    (g : E.filtration.realification.PolynomialOrbit w)
    (hg : ∀ x : σ → ℤ,
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        (E.filtration.realification.polynomialOrbitEval w x g) =
          F.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b)
    (x : σ → ℤ) :
    G.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (F.realPolynomialGroupMap G φ hφ w b) =
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) (φ.comp (F.gradedRefiltrationSubalgebra W).incl)
        (E.filtration.realification.polynomialOrbitEval w x g) := by
  rw [realPolynomialGroupMap_value, ← hg x]
  apply NilpotentLieBCHGroup.ext
  change φ.toLinearMap.baseChange ℝ
    ((F.gradedRefiltrationSubalgebra W).incl.toLinearMap.baseChange ℝ _) =
      (φ.toLinearMap.comp (F.gradedRefiltrationSubalgebra W).incl.toLinearMap).baseChange ℝ _
  rw [LinearMap.baseChange_comp]
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI

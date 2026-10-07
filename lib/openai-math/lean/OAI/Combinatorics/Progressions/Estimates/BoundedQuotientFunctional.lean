import Mathlib.LinearAlgebra.Matrix.ToLin
import OAI.Combinatorics.Progressions.Estimates.QuotientSubspaceFunctional
import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix BigOperators

variable {ι κ V U : Type*} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℚ V] [AddCommGroup U] [Module ℚ U]

theorem exists_bounded_linear_retraction (a : Basis κ ℚ U) (b : Basis ι ℚ V)
    (φ : U →ₗ[ℚ] V) (hφ : Function.Injective φ) {H : ℕ} (hH : 1 ≤ H)
    (ha : ∀ i j, RationalHeightLE (b.repr (φ (a j)) i) H) :
    ∃ ρ : V →ₗ[ℚ] U, (∀ x, ρ (φ x) = x) ∧
      ∀ i j, RationalHeightLE (a.repr (ρ (b j)) i)
        (rationalSolveHeight (Fintype.card κ) H) := by
  classical
  let A := LinearMap.toMatrix a b φ
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have heq (z : κ → ℚ) : A *ᵥ z = b.equivFun (φ (a.equivFun.symm z)) := by
      have hz := LinearMap.toMatrix_mulVec_repr a b φ (a.equivFun.symm z)
      simpa only [A, ← a.equivFun_apply, ← b.equivFun_apply,
        LinearEquiv.apply_symm_apply] using hz
    rw [heq, heq] at hxy
    exact a.equivFun.symm.injective (hφ (b.equivFun.injective hxy))
  obtain ⟨P, hPA, hP⟩ := exists_bounded_rational_left_inverse A
    (Matrix.mulVec_injective_iff.mp hinj) hH
    (by simpa only [A, LinearMap.toMatrix_apply] using ha)
  refine ⟨Matrix.toLin b a P, ?_, ?_⟩
  · intro x
    have hcomp : (Matrix.toLin b a P).comp φ = LinearMap.id := by
      calc
        _ = (Matrix.toLin b a P).comp (Matrix.toLin a b A) := by
          rw [Matrix.toLin_toMatrix]
        _ = Matrix.toLin a a (P * A) := (Matrix.toLin_mul a b a P A).symm
        _ = LinearMap.id := by rw [hPA, Matrix.toLin_one]
    exact LinearMap.congr_fun hcomp x
  · intro i j
    have hij := LinearMap.toMatrix_toLin b a P
    have hv := congrArg (fun M => M i j) hij
    rw [LinearMap.toMatrix_apply] at hv
    rw [hv]
    exact hP i j

theorem exists_bounded_functional_extension (a : Basis κ ℚ U) (b : Basis ι ℚ V)
    (φ : U →ₗ[ℚ] V) (hφ : Function.Injective φ) (η : U →ₗ[ℚ] ℚ)
    {H K : ℕ} (hH : 1 ≤ H)
    (ha : ∀ i j, RationalHeightLE (b.repr (φ (a j)) i) H)
    (hη : ∀ j, RationalHeightLE (η (a j)) K) :
    ∃ ξ : V →ₗ[ℚ] ℚ, (∀ x, ξ (φ x) = η x) ∧
      ∀ i, RationalHeightLE (ξ (b i))
        ((Fintype.card κ + 1) *
          (rationalSolveHeight (Fintype.card κ) H * K) ^ Fintype.card κ) := by
  classical
  obtain ⟨ρ, hρ, hheight⟩ := exists_bounded_linear_retraction a b φ hφ hH ha
  refine ⟨η.comp ρ, fun x => by simp only [LinearMap.comp_apply, hρ], ?_⟩
  intro i
  have he : η (ρ (b i)) = ∑ j, a.repr (ρ (b i)) j * η (a j) := by
    conv_lhs => rw [← a.sum_repr (ρ (b i))]
    simp only [map_sum, map_smul, smul_eq_mul]
  change RationalHeightLE (η (ρ (b i))) _
  rw [he]
  exact rationalHeightLE_sum _ (fun j => (hheight j i).mul (hη j))

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_bounded_functional_preserving_subspace
    {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (W : Submodule ℚ V) (v : κ → V)
    (hspan : Submodule.span ℚ (Set.range v) = W) (η : V →ₗ[ℚ] ℚ)
    {H K : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v i) j) H)
    (hη : ∀ i, RationalHeightLE (η (v i)) K) :
    ∃ ξ : V →ₗ[ℚ] ℚ, (∀ x ∈ W, ξ x = η x) ∧
      ∀ i, RationalHeightLE (ξ (b i))
        ((finrank ℚ W + 1) * (rationalSolveHeight (finrank ℚ W) H * K) ^ finrank ℚ W) := by
  classical
  let : FiniteDimensional ℚ V := b.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  let a : Basis (Fin (finrank ℚ W)) ℚ W :=
    (Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan)
  have ha (i) : (a i : V) = z i := by
    simp only [a, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  have hcoords (i j) : RationalHeightLE (b.repr (W.subtype (a j)) i) H := by
    change RationalHeightLE (b.repr (a j : V) i) H
    rw [ha]
    obtain ⟨k, hk⟩ := hz j
    rw [← hk]
    exact hv k i
  have hvalues (j) : RationalHeightLE ((η.comp W.subtype) (a j)) K := by
    change RationalHeightLE (η (a j : V)) K
    rw [ha]
    obtain ⟨k, hk⟩ := hz j
    rw [← hk]
    exact hη k
  obtain ⟨ξ, hξ, hbound⟩ := exists_bounded_functional_extension a b W.subtype
    Subtype.val_injective (η.comp W.subtype) hH hcoords hvalues
  refine ⟨ξ, fun x hx => hξ ⟨x, hx⟩, ?_⟩
  simpa only [Fintype.card_fin] using hbound

theorem exists_bounded_quotient_functional
    {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
    (U I : Submodule ℚ V) (b : Basis ι ℚ (V ⧸ I))
    (v : κ → V) (hspan : Submodule.span ℚ (Set.range v) = U)
    (η : V →ₗ[ℚ] ℚ) (hann : U ⊓ I ≤ η.ker)
    {H K : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (I.mkQ (v i)) j) H)
    (hη : ∀ i, RationalHeightLE (η (v i)) K) :
    ∃ ξ : (V ⧸ I) →ₗ[ℚ] ℚ, (∀ x ∈ U, ξ (I.mkQ x) = η x) ∧
      ∀ i, RationalHeightLE (ξ (b i))
        ((finrank ℚ (U.map I.mkQ) + 1) *
          (rationalSolveHeight (finrank ℚ (U.map I.mkQ)) H * K) ^
            finrank ℚ (U.map I.mkQ)) := by
  obtain ⟨η₀, hη₀⟩ := exists_quotient_functional_preserving_subspace U I η hann
  have hmem (i) : v i ∈ U := hspan ▸ Submodule.subset_span (Set.mem_range_self i)
  have hproject : Submodule.span ℚ (Set.range (I.mkQ ∘ v)) = U.map I.mkQ := by
    rw [Set.range_comp, ← Submodule.map_span, hspan]
  obtain ⟨ξ, hξ, hbound⟩ := exists_bounded_functional_preserving_subspace b
    (U.map I.mkQ) (I.mkQ ∘ v) hproject η₀ hH hv
    (fun i => by simpa only [Function.comp_apply, hη₀ (v i) (hmem i)] using hη i)
  refine ⟨ξ, ?_, hbound⟩
  intro x hx
  rw [hξ (I.mkQ x) (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)]
  exact hη₀ x hx

end Erdos3

end

end OAI

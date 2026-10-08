import GowersSzemeredi.Proofs16VarietyBoxes

/-! Common boxes for families of bilinear Bohr varieties (stacking).

For `n` bilinear Bohr varieties with a common radius `ρ`, the variety built
from the union of their frequency sets and the concatenation of their
`L`-families lies inside each of them. The box theorem applied to it gives
one product progression through the origin common to all `n` varieties.
Its step bounds are `M₁^(|⋃Γ| + 2 Σ r)` and `M₂^|⋃Ψ|`, linear in the total
codimension and rank.

This is the union side of research notes J.2's remaining gap (item 2).
Stacking costs only the sum of the ranks in the exponent, not a product
or a power. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- Bohr sets shrink as the frequency set grows. -/
theorem bohr_anti {N : Nat} [NeZero N] {K K' : Finset (ZMod N)} (h : K ⊆ K') (ρ : Real) :
    bohr K' ρ ⊆ bohr K ρ := by
  intro x hx
  unfold bohr at hx ⊢
  obtain ⟨_, hx⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => hx r (h hr)⟩

/-- Freiman-linearity passes to subsets. -/
theorem IsFreimanLinearOn.mono {N : Nat} {B B' : Finset (ZMod N)} {L : ZMod N → ZMod N}
    (h : IsFreimanLinearOn B L) (hsub : B' ⊆ B) : IsFreimanLinearOn B' L :=
  fun y₁ y₂ y₃ y₄ h1 h2 h3 h4 hsum => h y₁ y₂ y₃ y₄ (hsub h1) (hsub h2) (hsub h3) (hsub h4) hsum

/-- The concatenated `L`-family of `n` varieties. -/
def concatFamily {N n : Nat} (r : Fin n → Nat) (L : ∀ t, Fin (r t) → ZMod N → ZMod N) :
    Fin (∑ t, r t) → ZMod N → ZMod N :=
  fun k => let p := finSigmaFinEquiv.symm k; L p.1 p.2

/-- The union variety lies inside each member variety. -/
theorem unionVariety_subset {N n : Nat} [NeZero N] (Γ Ψ : Fin n → Finset (ZMod N))
    (r : Fin n → Nat) (L : ∀ t, Fin (r t) → ZMod N → ZMod N) (ρ : Real) (t : Fin n) :
    bilinearBohrVariety (Finset.univ.biUnion Γ) (Finset.univ.biUnion Ψ) (concatFamily r L) ρ ⊆
      bilinearBohrVariety (Γ t) (Ψ t) (L t) ρ := by
  intro p hp
  unfold bilinearBohrVariety at hp ⊢
  obtain ⟨hprod, hvar⟩ := Finset.mem_filter.mp hp
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hprod
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨bohr_anti (Finset.subset_biUnion_of_mem Γ (Finset.mem_univ t)) ρ hx,
     bohr_anti (Finset.subset_biUnion_of_mem Ψ (Finset.mem_univ t)) ρ hy⟩, ?_⟩
  apply bohr_anti _ ρ hvar
  intro z hz
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
  refine Finset.mem_image.mpr ⟨finSigmaFinEquiv ⟨t, i⟩, Finset.mem_univ _, ?_⟩
  show concatFamily r L (finSigmaFinEquiv ⟨t, i⟩) p.2 = L t i p.2
  unfold concatFamily
  rw [Equiv.symm_apply_apply]

/-- **A common box for `n` varieties.** -/
theorem varieties_common_product {N n : Nat} [NeZero N] (Γ Ψ : Fin n → Finset (ZMod N))
    (r : Fin n → Nat) (L : ∀ t, Fin (r t) → ZMod N → ZMod N) {ρ : Real}
    (hL : ∀ t k, IsFreimanLinearOn (bohr (Ψ t) ρ) (L t k))
    (M₁ M₂ : Nat) [NeZero M₁] [NeZero M₂] (L₁ L₂ : Nat)
    (h₂ : (L₂ : Real) ≤ ρ * M₂) (h₁ : (L₁ : Real) * (1 + L₂) ≤ ρ * M₁) :
    ∃ u v : Nat, 0 < u ∧ u ≤ M₁ ^ ((Finset.univ.biUnion Γ).card + ((∑ t, r t) + (∑ t, r t))) ∧
      0 < v ∧ v ≤ M₂ ^ (Finset.univ.biUnion Ψ).card ∧
      ∀ t i j, i < L₁ → j < L₂ →
        ((i : ZMod N) * (u : ZMod N), (j : ZMod N) * (v : ZMod N)) ∈
          bilinearBohrVariety (Γ t) (Ψ t) (L t) ρ := by
  have hLc : ∀ k, IsFreimanLinearOn (bohr (Finset.univ.biUnion Ψ) ρ) (concatFamily r L k) := by
    intro k
    let p := finSigmaFinEquiv.symm k
    exact (hL p.1 p.2).mono
      (bohr_anti (Finset.subset_biUnion_of_mem Ψ (Finset.mem_univ p.1)) ρ)
  obtain ⟨u, v, hu, huM, hv, hvM, hmem⟩ :=
    bilinearBohrVariety_contains_product hLc M₁ M₂ L₁ L₂ h₂ h₁
  exact ⟨u, v, hu, huM, hv, hvM, fun t i j hi hj =>
    unionVariety_subset Γ Ψ r L ρ t (hmem i j hi hj)⟩

end LeanProofs.GowersSzemeredi

import IPRADerivations.Topology.RationalHomology
import IPRADerivations.Topology.PrismIdentity

/-!
# The mod-2 prism identity, choice-independent homology maps and tower homology

Packet: `topology/ipra_topology_framework_2026-11-15`, `paper/sections/05_carrier_theorems.tex`:

* `prism_mod2` (`thm:prism`, "Finite prism identity"): for evaluations in a group of exponent `2` (chains over
  `𝔽₂`, with any normalization of tuples built into the evaluation `φ`: "paired words have the same multiset of
  vertices, so either both normalize to the same simplex or both vanish"),
  `∂P + P∂ = f_# + g_#`. It is the signed identity `prism_identity` of `Topology/PrismIdentity` with the signs
  erased;
* `induced_eq` (`cor:choice-independent`, "Choice-independent homology map"): chain maps with a supplied
  homotopy `f − g = ∂h + h∂` induce the same map on homology ("`f_# z` and `g_# z` differ by a boundary"), over
  any field (`−1 = 1` over `𝔽₂`);
* `induced_id`, `induced_comp_map`: the induced map is functorial ("Composition of carriers induces composition
  of homology maps");
* `tower_square` (`thm:tower-homology`, "Tower homology"): if the two composites around a naturality square of
  chain maps are homotopic ("carried by a common carrier. They are therefore contiguous"), the square commutes
  on homology, so a coherent tower map is a morphism of the inverse systems of homology spaces;
* `tower_map_comp`: composition of tower maps is functorial on homology.
-/

namespace LeanProofs.IPRA.Topology.TowerHomology

open Finset LeanProofs.IPRA.Topology.RationalHomology LeanProofs.IPRA.Topology.PrismIdentity

/-! ## The prism identity modulo 2 -/

/-- `thm:prism`: `∂P + P∂ = f_# + g_#` for evaluations in a group of exponent 2. -/
theorem prism_mod2 {V W M : Type*} [AddCommGroup M] (hM : ∀ y : M, y + y = 0) (f g : V → W) (k : ℕ)
    (φ : (ℕ → W) → M) (hφ : ∀ σ τ : ℕ → W, (∀ m < k + 1, σ m = τ m) → φ σ = φ τ) (σ : ℕ → V) :
    (∑ i ∈ range (k + 1), ∑ j ∈ range (k + 2), φ (face j (prism f g i σ))) +
      ∑ l ∈ range (k + 1), ∑ i ∈ range k, φ (prism f g i (face l σ)) = φ (f ∘ σ) + φ (g ∘ σ) := by
  have hneg : ∀ y : M, -y = y := fun y => neg_eq_of_add_eq_zero_left (hM y)
  have hs : ∀ (m : ℕ) (y : M), ((-1 : ℤ) ^ m) • y = y := fun m y => by
    rcases neg_one_pow_eq_or ℤ m with h | h
    · rw [h, one_zsmul]
    · rw [h, neg_zsmul, one_zsmul, hneg]
  have h := prism_identity f g k φ hφ σ
  simp only [hs] at h
  rw [h, sub_eq_add_neg, hneg, add_comm]

/-! ## Homology maps -/

variable {K : Type*} [Field K]
variable {X₂ X₁ X₀ : Type*} [AddCommGroup X₂] [Module K X₂] [AddCommGroup X₁] [Module K X₁]
  [AddCommGroup X₀] [Module K X₀]
variable {Y₂ Y₁ Y₀ : Type*} [AddCommGroup Y₂] [Module K Y₂] [AddCommGroup Y₁] [Module K Y₁]
  [AddCommGroup Y₀] [Module K Y₀]
variable {Z₂ Z₁ Z₀ : Type*} [AddCommGroup Z₂] [Module K Z₂] [AddCommGroup Z₁] [Module K Z₁]
  [AddCommGroup Z₀] [Module K Z₀]
variable {d₁ : X₁ →ₗ[K] X₀} {d₂ : X₂ →ₗ[K] X₁} {e₁ : Y₁ →ₗ[K] Y₀} {e₂ : Y₂ →ₗ[K] Y₁}
  {z₁ : Z₁ →ₗ[K] Z₀} {z₂ : Z₂ →ₗ[K] Z₁}

/-- `cor:choice-independent`: homotopic chain maps induce the same map on homology. -/
theorem induced_eq (f₂ : X₂ →ₗ[K] Y₂) (f₁ : X₁ →ₗ[K] Y₁) (f₀ : X₀ →ₗ[K] Y₀) (c₁ : e₁ ∘ₗ f₁ = f₀ ∘ₗ d₁)
    (c₂ : e₂ ∘ₗ f₂ = f₁ ∘ₗ d₂) (g₂ : X₂ →ₗ[K] Y₂) (g₁ : X₁ →ₗ[K] Y₁) (g₀ : X₀ →ₗ[K] Y₀)
    (c₁' : e₁ ∘ₗ g₁ = g₀ ∘ₗ d₁) (c₂' : e₂ ∘ₗ g₂ = g₁ ∘ₗ d₂) (h₁ : X₁ →ₗ[K] Y₂) (h₀ : X₀ →ₗ[K] Y₁)
    (hh : f₁ - g₁ = e₂ ∘ₗ h₁ + h₀ ∘ₗ d₁) :
    induced f₂ f₁ f₀ c₁ c₂ = induced g₂ g₁ g₀ c₁' c₂' := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, induced, Submodule.mapQ_apply]
  rw [Submodule.Quotient.eq]
  refine ⟨h₁ x.1, ?_⟩
  have hx := LinearMap.mem_ker.mp x.2
  have := LinearMap.congr_fun hh x.1
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, hx, map_zero, add_zero] at this
  simp only [Submodule.coe_subtype, Submodule.coe_sub, cyc, LinearMap.codRestrict_apply, LinearMap.comp_apply]
  exact this.symm

/-- The identity chain map induces the identity. -/
theorem induced_id (c₁ : d₁ ∘ₗ LinearMap.id = LinearMap.id ∘ₗ d₁) (c₂ : d₂ ∘ₗ LinearMap.id = LinearMap.id ∘ₗ d₂) :
    induced (LinearMap.id : X₂ →ₗ[K] X₂) LinearMap.id LinearMap.id c₁ c₂ = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, induced, Submodule.mapQ_apply, LinearMap.id_apply]
  exact congrArg _ (Subtype.ext rfl)

/-- Composition of chain maps induces composition of homology maps. -/
theorem induced_comp_map (f₂ : X₂ →ₗ[K] Y₂) (f₁ : X₁ →ₗ[K] Y₁) (f₀ : X₀ →ₗ[K] Y₀) (c₁ : e₁ ∘ₗ f₁ = f₀ ∘ₗ d₁)
    (c₂ : e₂ ∘ₗ f₂ = f₁ ∘ₗ d₂) (g₂ : Y₂ →ₗ[K] Z₂) (g₁ : Y₁ →ₗ[K] Z₁) (g₀ : Y₀ →ₗ[K] Z₀)
    (c₁' : z₁ ∘ₗ g₁ = g₀ ∘ₗ e₁) (c₂' : z₂ ∘ₗ g₂ = g₁ ∘ₗ e₂)
    (k₁ : z₁ ∘ₗ (g₁ ∘ₗ f₁) = (g₀ ∘ₗ f₀) ∘ₗ d₁) (k₂ : z₂ ∘ₗ (g₂ ∘ₗ f₂) = (g₁ ∘ₗ f₁) ∘ₗ d₂) :
    induced (g₂ ∘ₗ f₂) (g₁ ∘ₗ f₁) (g₀ ∘ₗ f₀) k₁ k₂ = induced g₂ g₁ g₀ c₁' c₂' ∘ₗ induced f₂ f₁ f₀ c₁ c₂ := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, induced, Submodule.mapQ_apply]
  exact congrArg _ (Subtype.ext rfl)

/-- The chain-map conditions of a composite. -/
theorem comp_chain {f₁ : X₁ →ₗ[K] Y₁} {f₀ : X₀ →ₗ[K] Y₀} (c₁ : e₁ ∘ₗ f₁ = f₀ ∘ₗ d₁) {g₁ : Y₁ →ₗ[K] Z₁}
    {g₀ : Y₀ →ₗ[K] Z₀} (c₁' : z₁ ∘ₗ g₁ = g₀ ∘ₗ e₁) : z₁ ∘ₗ (g₁ ∘ₗ f₁) = (g₀ ∘ₗ f₀) ∘ₗ d₁ := by
  rw [← LinearMap.comp_assoc, c₁', LinearMap.comp_assoc, c₁, LinearMap.comp_assoc]

/-! ## Tower homology -/

variable {W₂ W₁ W₀ : Type*} [AddCommGroup W₂] [Module K W₂] [AddCommGroup W₁] [Module K W₁]
  [AddCommGroup W₀] [Module K W₀] {w₁ : W₁ →ₗ[K] W₀} {w₂ : W₂ →ₗ[K] W₁}

/-- `thm:tower-homology`: a naturality square of chain maps `X --r--> Y`, `X --φ--> Z`, `Y --ψ--> W`,
`Z --s--> W` whose two composites are homotopic commutes on homology. -/
theorem tower_square (r₂ : X₂ →ₗ[K] Y₂) (r₁ : X₁ →ₗ[K] Y₁) (r₀ : X₀ →ₗ[K] Y₀) (cr₁ : e₁ ∘ₗ r₁ = r₀ ∘ₗ d₁)
    (cr₂ : e₂ ∘ₗ r₂ = r₁ ∘ₗ d₂) (ψ₂ : Y₂ →ₗ[K] W₂) (ψ₁ : Y₁ →ₗ[K] W₁) (ψ₀ : Y₀ →ₗ[K] W₀)
    (cψ₁ : w₁ ∘ₗ ψ₁ = ψ₀ ∘ₗ e₁) (cψ₂ : w₂ ∘ₗ ψ₂ = ψ₁ ∘ₗ e₂) (φ₂ : X₂ →ₗ[K] Z₂) (φ₁ : X₁ →ₗ[K] Z₁)
    (φ₀ : X₀ →ₗ[K] Z₀) (cφ₁ : z₁ ∘ₗ φ₁ = φ₀ ∘ₗ d₁) (cφ₂ : z₂ ∘ₗ φ₂ = φ₁ ∘ₗ d₂) (s₂ : Z₂ →ₗ[K] W₂)
    (s₁ : Z₁ →ₗ[K] W₁) (s₀ : Z₀ →ₗ[K] W₀) (cs₁ : w₁ ∘ₗ s₁ = s₀ ∘ₗ z₁) (cs₂ : w₂ ∘ₗ s₂ = s₁ ∘ₗ z₂)
    (h₁ : X₁ →ₗ[K] W₂) (h₀ : X₀ →ₗ[K] W₁) (hh : ψ₁ ∘ₗ r₁ - s₁ ∘ₗ φ₁ = w₂ ∘ₗ h₁ + h₀ ∘ₗ d₁) :
    induced ψ₂ ψ₁ ψ₀ cψ₁ cψ₂ ∘ₗ induced r₂ r₁ r₀ cr₁ cr₂ =
      induced s₂ s₁ s₀ cs₁ cs₂ ∘ₗ induced φ₂ φ₁ φ₀ cφ₁ cφ₂ := by
  rw [← induced_comp_map r₂ r₁ r₀ cr₁ cr₂ ψ₂ ψ₁ ψ₀ cψ₁ cψ₂ (comp_chain cr₁ cψ₁) (comp_chain cr₂ cψ₂),
    ← induced_comp_map φ₂ φ₁ φ₀ cφ₁ cφ₂ s₂ s₁ s₀ cs₁ cs₂ (comp_chain cφ₁ cs₁) (comp_chain cφ₂ cs₂)]
  exact induced_eq _ _ _ _ _ _ _ _ _ _ h₁ h₀ hh

/-- Composition of tower maps is functorial on homology (one level). -/
theorem tower_map_comp (f₂ : X₂ →ₗ[K] Y₂) (f₁ : X₁ →ₗ[K] Y₁) (f₀ : X₀ →ₗ[K] Y₀) (c₁ : e₁ ∘ₗ f₁ = f₀ ∘ₗ d₁)
    (c₂ : e₂ ∘ₗ f₂ = f₁ ∘ₗ d₂) (g₂ : Y₂ →ₗ[K] Z₂) (g₁ : Y₁ →ₗ[K] Z₁) (g₀ : Y₀ →ₗ[K] Z₀)
    (c₁' : z₁ ∘ₗ g₁ = g₀ ∘ₗ e₁) (c₂' : z₂ ∘ₗ g₂ = g₁ ∘ₗ e₂) :
    induced (g₂ ∘ₗ f₂) (g₁ ∘ₗ f₁) (g₀ ∘ₗ f₀) (comp_chain c₁ c₁') (comp_chain c₂ c₂') =
      induced g₂ g₁ g₀ c₁' c₂' ∘ₗ induced f₂ f₁ f₀ c₁ c₂ :=
  induced_comp_map f₂ f₁ f₀ c₁ c₂ g₂ g₁ g₀ c₁' c₂' _ _

end LeanProofs.IPRA.Topology.TowerHomology

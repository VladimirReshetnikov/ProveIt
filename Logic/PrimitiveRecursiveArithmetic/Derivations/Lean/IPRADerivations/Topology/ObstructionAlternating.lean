import IPRADerivations.Topology.AntipodalObstruction
import IPRADerivations.Topology.DegenerateBoundary

/-!
# The finite obstruction for alternating coefficient functionals

Packet: `topology/hairy_ball_ipra`, `sections/degree.tex`, Theorem `thm:obstruction` ("Finite obstruction"),
the chain argument in one statement: "Each tuple in `P(S^r(Z))` has `d + 1` entries belonging to a single face
with at most `d` vertices, so this chain vanishes … Thus consecutive layers have exactly the same top image
chain … For odd `d`, the coefficient at the all-positive face would give `1 = −1`." (Here `d = n + 1`.)

`finite_obstruction_alt` combines `Topology/AntipodalObstruction.finite_obstruction` with
`Topology/DegenerateBoundary.degenerate_boundary`: the coefficient functional `φ` is alternating and vanishes
on repeats, and every prism tuple between consecutive layers has a repeated vertex (the no-opposite-labels
condition: the `n + 2` labels lie in a face with at most `n + 1` vertices). Then, for even `n`, the layers
cannot run from a labelling of carrier degree one to its antipode: on a failed scan the hypotheses are
contradictory, so the bounded scan for opposite labels succeeds.
-/

namespace LeanProofs.IPRA.Topology.ObstructionAlternating

open Finset
open LeanProofs.IPRA.Topology.PrismIdentity (face prism)
open LeanProofs.IPRA.Topology.SphereCycle (Vtx facet coef anti)
open LeanProofs.IPRA.Topology.AntipodalObstruction (ext finite_obstruction)
open LeanProofs.IPRA.Topology.DegenerateBoundary (swapAt degenerate_boundary)

variable {V ι : Type*}

/-- `thm:obstruction` in chain form, for an alternating coefficient functional. -/
theorem finite_obstruction_alt {n : ℕ} (hn : Even n) (s : Finset ι) (c : ι → ℤ) (σ : ι → ℕ → V)
    (ℓ : ℕ → V → Vtx (n + 1)) (T : ℕ) (hT : ℓ T = anti ∘ ℓ 0) (φ : (ℕ → Vtx (n + 1)) → ℤ)
    (hφ : ∀ ρ τ : ℕ → Vtx (n + 1), (∀ m < n + 1, ρ m = τ m) → φ ρ = φ τ)
    (hfacet : ∀ ε : Fin (n + 1) → Bool,
      φ (ext (facet ε)) = if facet ε = facet (fun _ => true) then 1 else 0)
    (hcyc : ∀ ψ : (ℕ → V) → ℤ, ∑ i ∈ s, c i • ∑ l ∈ range (n + 1), ((-1 : ℤ) ^ l) • ψ (face l (σ i)) = 0)
    (hdeg1 : ∀ χ : (ℕ → Vtx (n + 1)) → ℤ,
      (∀ ρ τ : ℕ → Vtx (n + 1), (∀ m < n + 1, ρ m = τ m) → χ ρ = χ τ) →
      ∑ i ∈ s, c i • χ (ℓ 0 ∘ σ i) = ∑ ε : Fin (n + 1) → Bool, coef ε • χ (ext (facet ε)))
    (halt : ∀ (τ : ℕ → Vtx (n + 1)) (j : ℕ), j + 1 < n + 1 → φ (swapAt j τ) = -φ τ)
    (hrep : ∀ (τ : ℕ → Vtx (n + 1)) (j k : ℕ), j < k → k < n + 1 → τ j = τ k → φ τ = 0)
    (hrepeat : ∀ t < T, ∀ i ∈ s, ∀ m ∈ range (n + 1), ∃ p q, p < q ∧ q < n + 2 ∧
      prism (ℓ t) (ℓ (t + 1)) m (σ i) p = prism (ℓ t) (ℓ (t + 1)) m (σ i) q) : False :=
  finite_obstruction hn s c σ ℓ T hT φ hφ hfacet hcyc hdeg1 fun t ht i hi m hm => by
    obtain ⟨p, q, hpq, hq, h⟩ := hrepeat t ht i hi m hm
    exact degenerate_boundary φ (n + 1) halt hrep _ hpq hq h

end LeanProofs.IPRA.Topology.ObstructionAlternating

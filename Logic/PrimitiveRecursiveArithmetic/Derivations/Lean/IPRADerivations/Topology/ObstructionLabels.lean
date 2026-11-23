import IPRADerivations.Topology.ObstructionAlternating
import Mathlib.Combinatorics.Pigeonhole

/-!
# The finite obstruction in terms of labels

Packet: `topology/hairy_ball_ipra`, `sections/degree.tex`, Theorem `thm:obstruction` ("Finite obstruction"):
"There is a simplex `s` of `K_r` and a `j < T` such that among the labels
`{ℓ_j(x), ℓ_{j+1}(x) : x a vertex of s}` one finds opposite signed indices." Also the last step of S04–S06 of
`topology/general_topology_ipra_2026-11-19`: "A collection of signed basis vertices containing no opposite
pair spans a face of the cross-polytope."

* `repeat_of_no_opposite`: `n + 2` signed indices among `±e_0, …, ±e_n` with no opposite pair contain two
  equal ones (pigeonhole on the unsigned indices);
* `finite_obstruction_labels`: for even `n`, an alternating coefficient functional and labellings
  `ℓ_0, …, ℓ_T` with `ℓ_0` of carrier degree one and `ℓ_T = A ∘ ℓ_0`, it is contradictory that no prism tuple
  between consecutive layers contains an opposite pair. So on every such table of labels the bounded scan
  for an opposite pair succeeds.

Metatheory-level chain algebra, as in `Topology/PrismIdentity`; the cycle and its carrier degree are
hypotheses.
-/

namespace LeanProofs.IPRA.Topology.ObstructionLabels

open Finset
open LeanProofs.IPRA.Topology.PrismIdentity (face prism)
open LeanProofs.IPRA.Topology.SphereCycle (Vtx facet coef anti)
open LeanProofs.IPRA.Topology.AntipodalObstruction (ext)
open LeanProofs.IPRA.Topology.DegenerateBoundary (swapAt)
open LeanProofs.IPRA.Topology.ObstructionAlternating (finite_obstruction_alt)

variable {V ι : Type*}

/-- Signed indices with no opposite pair: `n + 2` of them among `±e_0, …, ±e_n` contain a repetition. -/
theorem repeat_of_no_opposite {n : ℕ} (τ : ℕ → Vtx (n + 1))
    (h : ∀ p q, p < n + 2 → q < n + 2 → τ p ≠ anti (τ q)) : ∃ p q, p < q ∧ q < n + 2 ∧ τ p = τ q := by
  obtain ⟨i, j, hij, he⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 2) => (τ i.val).2) (by simp)
  have key : ∀ a b : Fin (n + 2), a.val < b.val → (τ a.val).2 = (τ b.val).2 →
      ∃ p q, p < q ∧ q < n + 2 ∧ τ p = τ q := by
    intro a b hab hs
    refine ⟨a.val, b.val, hab, b.isLt, ?_⟩
    by_contra hne
    apply h a.val b.val a.isLt b.isLt
    have h1 : (τ a.val).1 ≠ (τ b.val).1 := fun h1 => hne (Prod.ext h1 hs)
    refine Prod.ext ?_ hs
    show (τ a.val).1 = !(τ b.val).1
    cases ha : (τ a.val).1 <;> cases hb : (τ b.val).1 <;> simp_all
  rcases Nat.lt_or_gt_of_ne (fun hv => hij (Fin.ext hv)) with hlt | hgt
  · exact key i j hlt he
  · exact key j i hgt he.symm

/-- `thm:obstruction`: labels without opposite pairs on consecutive layers are contradictory. -/
theorem finite_obstruction_labels {n : ℕ} (hn : Even n) (s : Finset ι) (c : ι → ℤ) (σ : ι → ℕ → V)
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
    (hno : ∀ t < T, ∀ i ∈ s, ∀ m ∈ range (n + 1), ∀ p q, p < n + 2 → q < n + 2 →
      prism (ℓ t) (ℓ (t + 1)) m (σ i) p ≠ anti (prism (ℓ t) (ℓ (t + 1)) m (σ i) q)) : False :=
  finite_obstruction_alt hn s c σ ℓ T hT φ hφ hfacet hcyc hdeg1 halt hrep fun t ht i hi m hm =>
    repeat_of_no_opposite _ (hno t ht i hi m hm)

end LeanProofs.IPRA.Topology.ObstructionLabels

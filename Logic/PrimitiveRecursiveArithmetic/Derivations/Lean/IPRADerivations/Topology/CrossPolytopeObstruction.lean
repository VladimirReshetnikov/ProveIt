import IPRADerivations.Topology.FacetCoefficient

/-!
# The finite obstruction on the cross-polytope itself

Packet: `topology/hairy_ball_ipra`, `sections/degree.tex`, Theorem `thm:obstruction` for `r = 0` (no
subdivision), and S04 of `topology/general_topology_ipra_2026-11-19` for `K = C_n`: with the cross-polytope
cycle `z_n` of `Topology/SphereCycle` as the cycle and the identity labelling as `ℓ_0`, the hypotheses of
`Topology/FacetCoefficient.obstruction_of_cycle` are theorems, so the statement is unconditional:

* `pad`, `face_ext`: the faces of a facet, as sequences;
* `cycle_ext`: `∂ z_n = 0` for evaluations of sequences;
* `cross_polytope_obstruction`: for even `n`, labellings `ℓ_0 = id, ℓ_1, …, ℓ_T = A` of the vertices
  `±e_0, …, ±e_n` cannot avoid opposite pairs on every prism tuple of every facet between consecutive layers:
  the identity and the antipodal map of the `n`-sphere's cross-polytope are not joined by a chain of
  contiguous simplicial maps.

Metatheory-level chain algebra, as in `Topology/PrismIdentity`. The subdivided complexes `K_r`, `r > 0`,
need the subdivision operator, which is not derived.
-/

namespace LeanProofs.IPRA.Topology.CrossPolytopeObstruction

open Finset
open LeanProofs.IPRA.Topology.PrismIdentity (face prism)
open LeanProofs.IPRA.Topology.SphereCycle (Vtx facet coef anti boundary_zero)
open LeanProofs.IPRA.Topology.AntipodalObstruction (ext)
open LeanProofs.IPRA.Topology.FacetCoefficient (obstruction_of_cycle)

variable {n : ℕ}

/-- A face tuple `Fin n → Vtx (n + 1)` as a sequence (constant beyond its entries). -/
def pad (ρ : Fin n → Vtx (n + 1)) : ℕ → Vtx (n + 1) :=
  fun m => if h : m < n then ρ ⟨m, h⟩ else (true, 0)

theorem face_ext (τ : Fin (n + 1) → Vtx (n + 1)) (j : Fin (n + 1)) :
    face j.val (ext τ) = pad (τ ∘ j.succAbove) := by
  funext m
  by_cases hm : m < n
  · by_cases hj : m < j.val
    · have h1 : j.succAbove ⟨m, hm⟩ = ⟨m, by omega⟩ := by
        rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def, hj])]
        rfl
      simp only [face, pad, AntipodalObstruction.ext, Function.comp_apply, if_pos hj, dif_pos hm,
        dif_pos (show m < n + 1 by omega), h1]
    · have h1 : j.succAbove ⟨m, hm⟩ = ⟨m + 1, by omega⟩ := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by simp only [Fin.le_def, Fin.coe_castSucc]; omega)]
        rfl
      simp only [face, pad, AntipodalObstruction.ext, Function.comp_apply, if_neg hj, dif_pos hm,
        dif_pos (show m + 1 < n + 1 by omega), h1]
  · have hj : ¬ m < j.val := by have := j.isLt; omega
    simp only [face, pad, AntipodalObstruction.ext, if_neg hj, dif_neg hm, dif_neg (show ¬ m + 1 < n + 1 by omega)]

/-- `∂ z_n = 0`, for evaluations of sequences. -/
theorem cycle_ext (ψ : (ℕ → Vtx (n + 1)) → ℤ) :
    ∑ ε : Fin (n + 1) → Bool, coef ε • ∑ l ∈ range (n + 1), ((-1 : ℤ) ^ l) • ψ (face l (ext (facet ε))) = 0 := by
  have h := boundary_zero (M := ℤ) (n := n) fun ρ => ψ (pad ρ)
  refine Eq.trans (sum_congr rfl fun ε _ => ?_) h
  rw [Finset.sum_range fun l => ((-1 : ℤ) ^ l) • ψ (face l (ext (facet ε)))]
  congr 1
  exact sum_congr rfl fun j _ => by rw [face_ext]

/-- The identity and the antipodal map of the cross-polytope are not joined by labellings without opposite
pairs (`n` even). -/
theorem cross_polytope_obstruction (hn : Even n) (ℓ : ℕ → Vtx (n + 1) → Vtx (n + 1)) (T : ℕ)
    (h0 : ℓ 0 = id) (hT : ℓ T = anti)
    (hno : ∀ t < T, ∀ ε : Fin (n + 1) → Bool, ∀ m ∈ range (n + 1), ∀ p q, p < n + 2 → q < n + 2 →
      prism (ℓ t) (ℓ (t + 1)) m (ext (facet ε)) p ≠ anti (prism (ℓ t) (ℓ (t + 1)) m (ext (facet ε)) q)) :
    False := by
  refine obstruction_of_cycle hn (Finset.univ : Finset (Fin (n + 1) → Bool)) coef (fun ε => ext (facet ε)) ℓ T
    (by rw [hT, h0]; rfl) cycle_ext (fun χ _ => by rw [h0]; rfl) fun t ht ε _ m hm => hno t ht ε m hm

end LeanProofs.IPRA.Topology.CrossPolytopeObstruction

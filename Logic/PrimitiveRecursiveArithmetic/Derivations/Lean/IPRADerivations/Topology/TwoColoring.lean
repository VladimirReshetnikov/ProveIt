import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Two colours or an odd-cycle certificate

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/05_algebraic.tex`, Theorem A10 ("A finite
loopless graph admits a two-coloring if and only if it has no odd cycle"):

* `colour`: colour each vertex by the parity of a chosen walk from the representative of its component
  ("color each vertex by the parity of its tree distance from the root");
* `colour_valid`: if every closed walk has even length, adjacent vertices get different colours (the walk to
  `u`, the edge `u v` and the reversed walk to `v` form a closed walk);
* `twoColorable_iff`: `G` is two-colourable exactly when every closed walk has even length; the forward
  direction is "colors alternate around every cycle in a proper two-coloring" (Mathlib's
  `Coloring.even_length_iff_congr`);
* `odd_certificate`: a graph that is not two-colourable has a closed walk of odd length;
* A09 ("a bounded coloring theorem"): `greedy`, the greedy invariant (the first `k` vertices are properly
  coloured with `Δ + 1` colours, the next one receiving a colour unused by its at most `Δ` earlier neighbours),
  and `colorable_succ_maxDegree`, a proper colouring with `Δ + 1` colours.
-/

namespace LeanProofs.IPRA.Topology.TwoColoring

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The representative of the component of `v`. -/
noncomputable def root (v : V) : V := (G.connectedComponentMk v).out

theorem reach (v : V) : G.Reachable (root G v) v := ConnectedComponent.eq.mp (Quot.out_eq _)

theorem root_eq_of_adj {u v : V} (h : G.Adj u v) : root G u = root G v := by
  unfold root
  rw [ConnectedComponent.connectedComponentMk_eq_of_adj h]

/-- A chosen walk from the root to `v`. -/
noncomputable def walkTo (v : V) : G.Walk (root G v) v := (reach G v).some

/-- The parity colour. -/
noncomputable def colour (v : V) : Bool := decide (Even (walkTo G v).length)

theorem colour_valid (hev : ∀ u (p : G.Walk u u), Even p.length) {u v : V} (h : G.Adj u v) :
    colour G u ≠ colour G v := by
  have hr := root_eq_of_adj G h
  have he := hev _ ((((walkTo G u).copy hr rfl).concat h).append (walkTo G v).reverse)
  rw [Walk.length_append, Walk.length_concat, Walk.length_copy, Walk.length_reverse, Nat.even_add,
    Nat.even_add_one] at he
  unfold colour
  intro hc
  have hc' : Even (walkTo G u).length ↔ Even (walkTo G v).length := by simpa using hc
  tauto

/-- A10: two-colourable exactly when every closed walk has even length. -/
theorem twoColorable_iff : G.Colorable 2 ↔ ∀ u (p : G.Walk u u), Even p.length := by
  constructor
  · rintro ⟨c⟩ u p
    have c' := G.recolorOfEquiv finTwoEquiv c
    exact (c'.even_length_iff_congr p).mpr Iff.rfl
  · intro hev
    have C : G.Coloring Bool := Coloring.mk (colour G) (fun h => colour_valid G hev h)
    simpa using C.colorable

/-- The odd-cycle certificate: a graph that is not two-colourable has a closed walk of odd length. -/
theorem odd_certificate (h : ¬ G.Colorable 2) : ∃ u, ∃ p : G.Walk u u, Odd p.length := by
  by_contra hno
  push_neg at hno
  exact h ((twoColorable_iff G).mpr fun u p => Nat.not_odd_iff_even.mp (hno u p))

/-! ## A09: greedy colouring with `Δ + 1` colours -/

/-- The greedy invariant: the first `k` vertices are properly coloured with `Δ + 1` colours. -/
theorem greedy {n Δ : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ v, (G.neighborFinset v).card ≤ Δ) :
    ∀ k ≤ n, ∃ c : Fin n → Fin (Δ + 1), ∀ u v : Fin n, u.val < k → v.val < k → G.Adj u v → c u ≠ c v := by
  intro k
  induction k with
  | zero => intro _; exact ⟨fun _ => 0, fun u _ hu => absurd hu (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨c, hc⟩ := ih (by omega)
    set w : Fin n := ⟨k, by omega⟩
    set forbidden : Finset (Fin (Δ + 1)) := ((G.neighborFinset w).filter fun v => v.val < k).image c
    have hcard : forbidden.card ≤ Δ :=
      (Finset.card_image_le).trans ((Finset.card_filter_le _ _).trans (hdeg w))
    obtain ⟨col, hcol⟩ : ∃ col : Fin (Δ + 1), col ∉ forbidden := by
      by_contra hall
      push_neg at hall
      have : (Finset.univ : Finset (Fin (Δ + 1))).card ≤ forbidden.card :=
        Finset.card_le_card fun x _ => hall x
      simp at this
      omega
    refine ⟨Function.update c w col, fun u v hu hv huv => ?_⟩
    have hne : u ≠ v := G.ne_of_adj huv
    by_cases hu' : u = w
    · have hv' : v ≠ w := fun h => hne (hu'.trans h.symm)
      have hvk : v.val < k := by
        have : v.val ≠ k := fun h => hv' (Fin.ext h)
        omega
      rw [hu', Function.update_self, Function.update_of_ne hv']
      intro h
      apply hcol
      rw [h]
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset w v).mpr (hu' ▸ huv), hvk⟩, rfl⟩
    · by_cases hv' : v = w
      · have huk : u.val < k := by
          have : u.val ≠ k := fun h => hu' (Fin.ext h)
          omega
        rw [hv', Function.update_self, Function.update_of_ne hu']
        intro h
        apply hcol
        rw [← h]
        exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr
          ⟨(G.mem_neighborFinset w u).mpr (hv' ▸ huv.symm), huk⟩, rfl⟩
      · rw [Function.update_of_ne hu', Function.update_of_ne hv']
        have huk : u.val < k := by
          have : u.val ≠ k := fun h => hu' (Fin.ext h)
          omega
        have hvk : v.val < k := by
          have : v.val ≠ k := fun h => hv' (Fin.ext h)
          omega
        exact hc u v huk hvk huv

/-- A09: a graph of maximum degree `Δ` has a proper colouring with `Δ + 1` colours. -/
theorem colorable_succ_maxDegree {n Δ : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ v, (G.neighborFinset v).card ≤ Δ) : G.Colorable (Δ + 1) := by
  obtain ⟨c, hc⟩ := greedy G hdeg n le_rfl
  exact ⟨Coloring.mk c fun {u v} h => hc u v u.2 v.2 h⟩

end LeanProofs.IPRA.Topology.TwoColoring

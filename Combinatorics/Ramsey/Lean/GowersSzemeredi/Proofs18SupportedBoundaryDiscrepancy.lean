import GowersSzemeredi.Proofs18BoundaryRefinement
import GowersSzemeredi.Proofs18IntervalBoundarySelection

/-! Discrepancy of arbitrary bounded complex functions survives removal of
cells crossing the boundary of their supporting interval. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- Removing exceptional cells costs at most their total cardinality when
all remaining cells either lie in, or avoid, the support. -/
theorem supported_discrepancy_away_from_exceptional_cells {N M : Nat} [NeZero N]
    (f : ZMod N → Complex) (S : Finset (ZMod N)) (Q : Fin M → ModAP N)
    (B : Finset (Fin M)) (hf : DiscValued f) (hsupp : ∀ x, x ∉ S → f x = 0)
    (hgood : ∀ i, i ∉ B → (Q i).carrier ⊆ S ∨ Disjoint (Q i).carrier S) :
    ∃ G : Finset (Fin M),
      (∀ i ∈ G, (Q i).carrier ⊆ S) ∧
      (∑ i, ‖∑ x ∈ (Q i).carrier, f x‖) ≤
        (∑ i ∈ G, ‖∑ x ∈ (Q i).carrier, f x‖) + ∑ i ∈ B, ((Q i).carrier.card : Real) := by
  classical
  let G := Finset.univ.filter (fun i => (Q i).carrier ⊆ S)
  have hnorm (i : Fin M) : ‖∑ x ∈ (Q i).carrier, f x‖ ≤ ((Q i).carrier.card : Real) := by
    calc
      _ ≤ ∑ x ∈ (Q i).carrier, ‖f x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ (Q i).carrier, (1 : Real) := Finset.sum_le_sum fun x _ => hf x
      _ = _ := by simp
  have hzero (i : Fin M) (hiG : i ∉ G) (hiB : i ∉ B) :
      ‖∑ x ∈ (Q i).carrier, f x‖ = 0 := by
    have hdis : Disjoint (Q i).carrier S := (hgood i hiB).resolve_left
      (fun h => hiG (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hs : (∑ x ∈ (Q i).carrier, f x) = 0 := Finset.sum_eq_zero fun x hx =>
      hsupp x (fun hxS => Finset.disjoint_left.mp hdis hx hxS)
    rw [hs, norm_zero]
  refine ⟨G, fun i hi => (Finset.mem_filter.mp hi).2, ?_⟩
  calc
    _ ≤ ∑ i : Fin M, ((if i ∈ G then ‖∑ x ∈ (Q i).carrier, f x‖ else 0) +
        if i ∈ B then ((Q i).carrier.card : Real) else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hiG : i ∈ G
      · rw [if_pos hiG]
        exact le_add_of_nonneg_right (by split_ifs <;> positivity)
      · rw [if_neg hiG, zero_add]
        by_cases hiB : i ∈ B
        · rw [if_pos hiB]
          exact hnorm i
        · rw [if_neg hiB, hzero i hiG hiB]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
      have hG : Finset.univ.filter (fun i => i ∈ G) = G := by ext i; simp
      have hB : Finset.univ.filter (fun i => i ∈ B) = B := by ext i; simp
      rw [hG, hB]

/-- Small modular diameter loses at most one eighth of the discrepancy
when restricting to cells wholly contained in a supporting interval. -/
theorem interval_small_diameter_supported_discrepancy {N M L : Nat} [NeZero N]
    (f : ZMod N → Complex) (Q : Fin M → ModAP N) (beta : Real)
    (hL : L ≤ N) (hf : DiscValued f)
    (hsupp : ∀ x, x ∉ finiteIntervalImage N (Finset.univ : Finset (Fin L)) → f x = 0)
    (hβ : 0 < beta) (hscale : 32 ≤ beta * N)
    (hpart : IsPartition (fun i => (Q i).carrier) Finset.univ)
    (hdiam : ∀ i, diameterAtMostReal (Q i).carrier (beta / 64 * N))
    (hdis : beta * N ≤ ∑ i, ‖∑ x ∈ (Q i).carrier, f x‖) :
    ∃ G : Finset (Fin M),
      (∀ i ∈ G, (Q i).carrier ⊆ finiteIntervalImage N (Finset.univ : Finset (Fin L))) ∧
      (7 * beta / 8) * N ≤ ∑ i ∈ G, ‖∑ x ∈ (Q i).carrier, f x‖ := by
  obtain ⟨B, hgood, hbadNat⟩ := interval_crossing_cells_mass Q hL (beta / 64) hpart hdiam
  have hbad : ∑ i ∈ B, ((Q i).carrier.card : Real) ≤ beta * N / 8 := by
    have hc : (∑ i ∈ B, ((Q i).carrier.card : Real)) ≤
        4 * (Nat.floor (beta / 64 * N) : Real) + 2 := by exact_mod_cast hbadNat
    have hb := Nat.floor_le (show (0 : Real) ≤ beta / 64 * N by positivity)
    linarith only [hc, hb, hscale]
  obtain ⟨G, hG, hbound⟩ := supported_discrepancy_away_from_exceptional_cells
    f _ Q B hf hsupp hgood
  exact ⟨G, hG, by linarith only [hdis, hbound, hbad]⟩

/-- Every discrepancy partition of an interval-supported function has a
small-diameter refinement whose interior cells retain seven eighths of its
normalized discrepancy. The full refinement and its cell-count budget are
retained, so the interior family can later be transported or completed. -/
theorem interval_supported_discrepancy_refinement {N M L : Nat} [NeZero N]
    (f : ZMod N → Complex) (Q : Fin M → ModAP N) (beta : Real)
    (hL : L ≤ N) (hf : DiscValued f)
    (hsupp : ∀ x, x ∉ finiteIntervalImage N (Finset.univ : Finset (Fin L)) → f x = 0)
    (hβ : 0 < beta) (hscale : 32 ≤ beta * N)
    (hQ : IsPartition (fun i => (Q i).carrier) Finset.univ)
    (hproper : ∀ i, (Q i).IsProper)
    (hdis : beta * N ≤ ∑ i, ‖∑ x ∈ (Q i).carrier, f x‖) :
    ∃ K : Nat, ∃ R : Fin K → ModAP N,
      IsPartition (fun j => (R j).carrier) Finset.univ ∧
      IsRefinement (fun j => (R j).carrier) (fun i => (Q i).carrier) ∧
      (∀ j, (R j).IsProper) ∧
      (K : Real) ≤ boundaryRefinementConstant (beta / 64) * (M : Real) ^ (1 / 16 : Real) *
        (N : Real) ^ (15 / 16 : Real) ∧
      ∃ G : Finset (Fin K),
        (∀ j ∈ G, (R j).carrier ⊆ finiteIntervalImage N (Finset.univ : Finset (Fin L))) ∧
        (7 * beta / 8) * N ≤ ∑ j ∈ G, ‖∑ x ∈ (R j).carrier, f x‖ := by
  obtain ⟨K, R, hR, href, hRproper, hcount, hdiam, hnorm⟩ :=
    small_diameter_partition_refinement Q (beta / 64) (by positivity) hQ hproper
  obtain ⟨G, hG, hdisG⟩ := interval_small_diameter_supported_discrepancy
    f R beta hL hf hsupp hβ hscale hR hdiam (hdis.trans (hnorm f))
  exact ⟨K, R, hR, href, hRproper, hcount, G, hG, hdisG⟩

end LeanProofs.GowersSzemeredi

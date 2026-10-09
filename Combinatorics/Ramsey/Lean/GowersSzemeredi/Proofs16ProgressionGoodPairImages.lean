import GowersSzemeredi.Proofs16ColumnImageBridges
import GowersSzemeredi.Proofs16ProgressionBridgeGeometry

/-! Quantitative good-pair purification on a proper progression. A
quarter-progression quadruple with two good pairs has controlled image on
its endpoint domain, without keeping any bridge frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnPairImageFailures {N : Nat} [NeZero N]
    (C : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho : Real) (K : Nat) (a b : ZMod N) : Finset (ZMod N) :=
  (progressionBridgeSet C (a-b)).filter fun u =>
    ¬ColumnQuadImageRelation T L rho K a b (u+(a-b)) u

/-- The two good pairs of an additive quadruple admit a common bridge. -/
theorem exists_common_image_bridge {N : Nat} [NeZero N]
    (C : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho : Real) (K : Nat) (a b c e : ZMod N)
    (hadd : a-b = c-e)
    (hsmall : (columnPairImageFailures C T L rho K a b).card+
      (columnPairImageFailures C T L rho K c e).card < (progressionBridgeSet C (a-b)).card) :
    ∃ u ∈ C, u+(a-b) ∈ C ∧
      ColumnQuadImageRelation T L rho K a b (u+(a-b)) u ∧
      ColumnQuadImageRelation T L rho K c e (u+(a-b)) u := by
  have hce : columnPairImageFailures C T L rho K c e =
      (progressionBridgeSet C (a-b)).filter fun u =>
        ¬ColumnQuadImageRelation T L rho K c e (u+(a-b)) u := by
    simp only [columnPairImageFailures, hadd]
  rw [hce] at hsmall
  obtain ⟨u, hu, hab, hce⟩ := exists_bridge_avoiding_two_failures
    (progressionBridgeSet C (a-b))
    (fun u => ColumnQuadImageRelation T L rho K a b (u+(a-b)) u)
    (fun u => ColumnQuadImageRelation T L rho K c e (u+(a-b)) u) hsmall
  exact ⟨u, (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2, hab, hce⟩

/-- Explicit cyclic version of the good-pair bridge step (Claim 7.3).
The only abundance requirement is the sum of the two failure counts times
`4^rank` being less than the parent progression cardinality. -/
theorem progression_good_pairs_image_relation {N d K : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    {rho : Real} (hrho : 0 < rho) (hK : 0 < K)
    (hT : ∀ x ∈ Q.carrier, (T x).card ≤ d)
    (hL : ∀ x ∈ Q.carrier, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (a b c e : ZMod N)
    (ha : a ∈ (centeredProgressionShrink Q 4).carrier)
    (hb : b ∈ (centeredProgressionShrink Q 4).carrier)
    (hc : c ∈ (centeredProgressionShrink Q 4).carrier)
    (he : e ∈ (centeredProgressionShrink Q 4).carrier)
    (hadd : a-b = c-e)
    (hsmall : 4^Q.rank*((columnPairImageFailures Q.carrier T L rho K a b).card+
      (columnPairImageFailures Q.carrier T L rho K c e).card) < Q.carrier.card) :
    ColumnQuadImageRelation T L (rho/2) (K*K*refinementKernelCap (4*d) (2*d) rho rho) a b c e := by
  have hmass := centered_progression_bridge_card Q hQ ha hb
  have hsum : (columnPairImageFailures Q.carrier T L rho K a b).card+
      (columnPairImageFailures Q.carrier T L rho K c e).card <
        (progressionBridgeSet Q.carrier (a-b)).card := by
    have hscaled := hsmall.trans_le hmass
    exact (Nat.mul_lt_mul_left (by positivity : 0 < 4^Q.rank)).mp hscaled
  obtain ⟨u, hu, hv, hab, hce⟩ := exists_common_image_bridge Q.carrier T L rho K a b c e hadd hsum
  have haQ := centered_progression_shrink_subset Q 4 ha
  have hbQ := centered_progression_shrink_subset Q 4 hb
  have hcQ := centered_progression_shrink_subset Q 4 hc
  have heQ := centered_progression_shrink_subset Q 4 he
  apply column_quad_image_bridge T L hrho hK hK a b c e (u+(a-b)) u ?_ ?_ hab hce
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hT _ haQ
    · exact hT _ hbQ
    · exact hT _ hcQ
    · exact hT _ heQ
    · exact hT _ hv
    · exact hT _ hu
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hL _ haQ
    · exact hL _ hbQ
    · exact hL _ hcQ
    · exact hL _ heQ

end LeanProofs.GowersSzemeredi

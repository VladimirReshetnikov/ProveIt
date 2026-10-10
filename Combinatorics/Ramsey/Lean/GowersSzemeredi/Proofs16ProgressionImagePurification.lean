import GowersSzemeredi.Proofs16PairImageFailureCounts

/-! The first purification profile from the selected progression maps.
Few failed quadruples give an explicit exceptional pair set. Every
quarter-progression additive quadruple avoiding those pairs is controlled
on its endpoint domain at half radius. No additional structural hypothesis
is introduced. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A threshold leaving a factor-two reserve for a shared bridge. -/
def progressionGoodPairThreshold {N : Nat} (Q : CenteredProgression N) : Nat :=
  Q.carrier.card/(4^(Q.rank+1))

theorem progression_good_pair_threshold_reserve {N : Nat} (Q : CenteredProgression N) :
    4^Q.rank*(2*progressionGoodPairThreshold Q) < Q.carrier.card := by
  have hzero : (0 : ZMod N) ∈ Q.carrier :=
    (centered_progression_mem_iff Q 0).mpr ⟨fun _ => 0, by simp, by simp⟩
  have hpos : 0 < Q.carrier.card := Finset.card_pos.mpr ⟨0,hzero⟩
  have hdiv := Nat.mul_div_le Q.carrier.card (4^(Q.rank+1))
  have hpow : 4^(Q.rank+1) = 4*4^Q.rank := by rw [pow_succ, Nat.mul_comm]
  rw [←show progressionGoodPairThreshold Q = Q.carrier.card/(4^(Q.rank+1)) from rfl] at hdiv
  rw [hpow] at hdiv
  by_cases hb : progressionGoodPairThreshold Q = 0
  · simpa [hb] using hpos
  · have hbpos := Nat.pos_of_ne_zero hb
    have hp : 0 < 4^Q.rank := by positivity
    nlinarith only [hdiv, Nat.mul_pos hp hbpos]

/-- From the selected maps' total exception bound, obtain a small pair
exception set and a relation for every remaining quarter-box quadruple. -/
theorem progression_image_purification_profile {N d K : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    {rho eta : Real} (hrho : 0 < rho) (hK : 0 < K)
    (hT : ∀ x ∈ Q.carrier, (T x).card ≤ d)
    (hL : ∀ x ∈ Q.carrier, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hfail : ((progressionMapImageFailures Q.carrier T L rho K).card : Real) ≤ eta*(N : Real)^3) :
    ∃ E : Finset (ZMod N × ZMod N), E ⊆ Q.carrier ×ˢ Q.carrier ∧
      (E.card : Real) ≤ eta*(N : Real)^3/(progressionGoodPairThreshold Q+1) ∧
      ∀ a b c e : ZMod N,
        a ∈ (centeredProgressionShrink Q 4).carrier →
        b ∈ (centeredProgressionShrink Q 4).carrier →
        c ∈ (centeredProgressionShrink Q 4).carrier →
        e ∈ (centeredProgressionShrink Q 4).carrier → a-b = c-e →
        (a,b) ∉ E → (c,e) ∉ E →
        ColumnQuadImageRelation T L (rho/2)
          (K*K*refinementKernelCap (4*d) (2*d) rho rho) a b c e := by
  let b0 := progressionGoodPairThreshold Q
  let E := (Q.carrier ×ˢ Q.carrier).filter fun p =>
    b0 < (columnPairImageFailures Q.carrier T L rho K p.1 p.2).card
  have hbound : (b0+1)*E.card ≤ (progressionMapImageFailures Q.carrier T L rho K).card :=
    column_bad_pairs_count_le Q.carrier T L rho K b0
  have hboundR : ((b0 : Real)+1)*E.card ≤ eta*(N : Real)^3 := by
    have h : ((b0 : Real)+1)*E.card ≤ (progressionMapImageFailures Q.carrier T L rho K).card := by
      exact_mod_cast hbound
    exact h.trans hfail
  refine ⟨E, Finset.filter_subset _ _, ?_, ?_⟩
  · exact (le_div_iff₀ (by positivity : 0 < (b0 : Real)+1)).mpr (by
      simpa only [mul_comm] using hboundR)
  · intro a b c e ha hb hc he hadd hab hce
    have haQ := centered_progression_shrink_subset Q 4 ha
    have hbQ := centered_progression_shrink_subset Q 4 hb
    have hcQ := centered_progression_shrink_subset Q 4 hc
    have heQ := centered_progression_shrink_subset Q 4 he
    have habound : (columnPairImageFailures Q.carrier T L rho K a b).card ≤ b0 := by
      have hn : ¬b0 < (columnPairImageFailures Q.carrier T L rho K a b).card := by
        intro h
        exact hab (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haQ,hbQ⟩,h⟩)
      omega
    have hcebound : (columnPairImageFailures Q.carrier T L rho K c e).card ≤ b0 := by
      have hn : ¬b0 < (columnPairImageFailures Q.carrier T L rho K c e).card := by
        intro h
        exact hce (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hcQ,heQ⟩,h⟩)
      omega
    apply progression_good_pairs_image_relation Q hQ T L hrho hK hT hL a b c e ha hb hc he hadd
    apply lt_of_le_of_lt (Nat.mul_le_mul_left _ (show
      (columnPairImageFailures Q.carrier T L rho K a b).card+
      (columnPairImageFailures Q.carrier T L rho K c e).card ≤ 2*b0 by omega))
    exact progression_good_pair_threshold_reserve Q

end LeanProofs.GowersSzemeredi

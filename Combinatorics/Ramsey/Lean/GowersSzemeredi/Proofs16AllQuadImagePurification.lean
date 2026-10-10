import GowersSzemeredi.Proofs16DirectedBridgeSelection
import GowersSzemeredi.Proofs16ShrunkBridgeCandidates
import GowersSzemeredi.Proofs16QuadImagePermutations

/-! All additive quadruples on a dense vertex core have bounded images.
The second bridge selection removes the exceptional pair condition, while
its two auxiliary spectra are removed only by the proved image theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A near-complete good-pair relation on the quarter progression becomes
an unconditional quadruple relation on the sixteenth vertex core. -/
theorem progression_all_quad_images_of_good_pairs {N d M : Nat} [NeZero N]
    (Q : CenteredProgression N) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (E : Finset (ZMod N × ZMod N))
    {rho : Real} (hrho : 0 < rho) (hM : 0 < M)
    (hT : ∀ x ∈ Q.carrier, (T x).card ≤ d)
    (hL : ∀ x ∈ Q.carrier, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hgood : ∀ a b c e : ZMod N,
      a ∈ (centeredProgressionShrink Q 4).carrier → b ∈ (centeredProgressionShrink Q 4).carrier →
      c ∈ (centeredProgressionShrink Q 4).carrier → e ∈ (centeredProgressionShrink Q 4).carrier →
      a-b = c-e → (a,b) ∉ E → (c,e) ∉ E → ColumnQuadImageRelation T L rho M a b c e) :
    let S := directedExceptionCore (centeredProgressionShrink Q 16).carrier E
      (progressionPurificationVertexThreshold Q)
    ∀ a b c e : ZMod N, a ∈ S → b ∈ S → c ∈ S → e ∈ S → a-b = c-e →
      ColumnQuadImageRelation T L (rho/2) (M*M*refinementKernelCap (4*d) (2*d) rho rho) a b c e := by
  intro S a b c e ha hb hc he hadd
  have haD := (Finset.mem_filter.mp ha).1
  have hbD := (Finset.mem_filter.mp hb).1
  have hcD := (Finset.mem_filter.mp hc).1
  have heD := (Finset.mem_filter.mp he).1
  have ha4 := centered_progression_sixteenth_subset_quarter Q haD
  have hb4 := centered_progression_sixteenth_subset_quarter Q hbD
  have hc4 := centered_progression_sixteenth_subset_quarter Q hcD
  have he4 := centered_progression_sixteenth_subset_quarter Q heD
  obtain ⟨y, hy, hay, hby, hcz, hez⟩ := exists_directed_bridge_four_good_pairs E
    (centeredProgressionShrink Q 8).carrier a b c e (c-a)
    (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp hb).2.1
    (Finset.mem_filter.mp hc).2.1 (Finset.mem_filter.mp he).2.1
    (progression_vertex_threshold_reserve Q)
  let z := y+(c-a)
  obtain ⟨hy4,hz4⟩ := centered_progression_second_bridge_mem Q haD hcD hy
  have heq1 : a-y = c-z := by dsimp only [z]; ring
  have heq2 : b-y = e-z := by dsimp only [z]; linear_combination -hadd
  have h1 := column_quad_image_swap_middle T L rho a y c z
    (hgood a y c z ha4 hy4 hc4 hz4 heq1 hay hcz)
  have h2 := column_quad_image_swap_middle T L rho b y e z
    (hgood b y e z hb4 hy4 he4 hz4 heq2 hby hez)
  have haQ := centered_progression_shrink_subset Q 4 ha4
  have hbQ := centered_progression_shrink_subset Q 4 hb4
  have hcQ := centered_progression_shrink_subset Q 4 hc4
  have heQ := centered_progression_shrink_subset Q 4 he4
  have hyQ := centered_progression_shrink_subset Q 4 hy4
  have hzQ := centered_progression_shrink_subset Q 4 hz4
  apply column_quad_image_swap_middle T L (rho/2) a c b e
  apply column_quad_image_bridge T L hrho hM hM a c b e y z ?_ ?_ h1 h2
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hT _ haQ
    · exact hT _ hcQ
    · exact hT _ hbQ
    · exact hT _ heQ
    · exact hT _ hyQ
    · exact hT _ hzQ
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hL _ haQ
    · exact hL _ hcQ
    · exact hL _ hbQ
    · exact hL _ heQ

/-- Full quadruple purification from the selected maps' original error
bound, with explicit retained mass and a quarter-radius endpoint domain. -/
theorem exists_progression_all_quad_image_core {N d K : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    {rho eta : Real} (hrho : 0 < rho) (hK : 0 < K)
    (hT : ∀ x ∈ Q.carrier, (T x).card ≤ d)
    (hL : ∀ x ∈ Q.carrier, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hfail : ((progressionMapImageFailures Q.carrier T L rho K).card : Real) ≤ eta*(N : Real)^3) :
    let M := K*K*refinementKernelCap (4*d) (2*d) rho rho
    ∃ S ⊆ (centeredProgressionShrink Q 16).carrier,
      (((centeredProgressionShrink Q 16).carrier.card : Real) -
        2*(eta*(N : Real)^3/(progressionGoodPairThreshold Q+1))/
          (progressionPurificationVertexThreshold Q+1) ≤ S.card) ∧
      ∀ a b c e : ZMod N, a ∈ S → b ∈ S → c ∈ S → e ∈ S → a-b = c-e →
        ColumnQuadImageRelation T L (rho/4)
          (M*M*refinementKernelCap (4*d) (2*d) (rho/2) (rho/2)) a b c e := by
  intro M
  obtain ⟨E,hE,hEcard,hgood⟩ := progression_image_purification_profile Q hQ T L hrho hK hT hL hfail
  let S := directedExceptionCore (centeredProgressionShrink Q 16).carrier E
    (progressionPurificationVertexThreshold Q)
  have hmass := directed_exception_core_mass (centeredProgressionShrink Q 16).carrier E
    (progressionPurificationVertexThreshold Q)
  have hloss : 2*(E.card : Real)/(progressionPurificationVertexThreshold Q+1) ≤
      2*(eta*(N : Real)^3/(progressionGoodPairThreshold Q+1))/(progressionPurificationVertexThreshold Q+1) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hEcard (by norm_num)) (by positivity)
  have hM : 0 < M := Nat.mul_pos (Nat.mul_pos hK hK) (refinementKernelCap_pos _ _ hrho hrho)
  refine ⟨S,Finset.filter_subset _ _, by linarith, ?_⟩
  have hhalf : ∀ x ∈ Q.carrier, IsFreimanLinearOn (bohr (T x) (rho/2)) (L x) :=
    fun x hx => column_freiman_smaller_radius (T x) (L x) (by linarith) (hL x hx)
  have hall := progression_all_quad_images_of_good_pairs Q T L E (by positivity : 0 < rho/2)
    hM hT hhalf hgood
  simpa only [show (rho/2)/2 = rho/4 by ring] using hall

end LeanProofs.GowersSzemeredi

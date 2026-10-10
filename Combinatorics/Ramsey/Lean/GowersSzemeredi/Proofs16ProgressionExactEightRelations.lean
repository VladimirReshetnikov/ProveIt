import GowersSzemeredi.Proofs16ExactOriginalEightAgreement
import GowersSzemeredi.Proofs16EightImageExtension

/-! Every additive eight-tuple on a smaller progression is respected exactly.
Quadruple compatibility telescopes through shared anchors. The endpoint
frequency-removal bound followed by prime-cyclic rigidity keeps only the
natural eight endpoint domains; it requires no model-packing iteration. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Exact pair compatibility bounds the quadruple defect image by one. -/
theorem column_quad_image_one_of_compatible {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (rho : Real) (a b c e : ZMod N)
    (hcomp : ColumnPairCompatible T L rho (a,b) (c,e)) :
    ColumnQuadImageRelation T L rho 1 a b c e := by
  have hsub : (columnQuadCommonDomain T rho a b c e).image (columnQuadDefect L a b c e) ⊆ {0} := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨-,ha,hb,hc,he⟩ := Finset.mem_filter.mp hy
    have hab : y ∈ bohr (columnDifferenceSpectrum T (a,b)) rho := by
      simpa only [columnDifferenceSpectrum, bohr_union, Finset.mem_inter] using And.intro ha hb
    have hce : y ∈ bohr (columnDifferenceSpectrum T (c,e)) rho := by
      simpa only [columnDifferenceSpectrum, bohr_union, Finset.mem_inter] using And.intro hc he
    have h := hcomp y hab hce
    refine Finset.mem_singleton.mpr ?_
    dsimp only [columnDifferenceMap] at h
    dsimp only [columnQuadDefect]
    linear_combination h
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_singleton 0)

/-- A normalized paired bounded-image defect vanishes on its divided
natural endpoint domain. -/
theorem paired_column_image_relation_exact {N K : Nat} [NeZero N] [Fact N.Prime]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (q : PairedColumnTuple N) {rho : Real} (hr : 0 ≤ rho)
    (hL : ∀ i, IsFreimanLinearOn (bohr (T (q i).1) rho) (L (q i).1) ∧
      IsFreimanLinearOn (bohr (T (q i).2) rho) (L (q i).2))
    (hzero : ∀ i, L (q i).1 0 = 0 ∧ L (q i).2 0 = 0)
    (himage : PairedColumnImageRelation T L rho K q) (hKN : K < N) :
    ∀ y ∈ bohr (pairedColumnSpectrum T q) (rho / K), pairedColumnDefect L q y = 0 := by
  have h0 : pairedColumnDefect L q 0 = 0 := by
    simp [pairedColumnDefect, fun i => (hzero i).1, fun i => (hzero i).2]
  exact freiman_small_image_zero _ hr _ (paired_column_defect_freiman T L q rho hL) h0 himage hKN

/-- Exact quadruples on a full progression imply every additive eight-tuple
on its 1/256 shrinking, on the natural endpoint domain at one uniform radius. -/
theorem progression_all_eight_exact_of_quad_compatible {N d : Nat} [NeZero N] [Fact N.Prime]
    (Q : CenteredProgression N) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho : Real} (hr : 0 < rho)
    (hdata : ∀ x ∈ Q.carrier, (T x).card ≤ d ∧
      IsFreimanLinearOn (bohr (T x) rho) (L x) ∧ L x 0 = 0)
    (hquad : ∀ a b c e, a ∈ Q.carrier → b ∈ Q.carrier → c ∈ Q.carrier → e ∈ Q.carrier →
      a-b = c-e → ColumnPairCompatible T L rho (a,b) (c,e))
    (hKN : refinementKernelCap (8*d) (4*d) rho rho < N)
    (q : PairedColumnTuple N)
    (hq : ∀ i, (q i).1 ∈ (centeredProgressionShrink Q 256).carrier ∧
      (q i).2 ∈ (centeredProgressionShrink Q 256).carrier)
    (hadd : pairedColumnIndex q = 0) :
    ∀ y ∈ bohr (pairedColumnSpectrum T q)
      (rho / (2 * refinementKernelCap (8*d) (4*d) rho rho)), pairedColumnDefect L q y = 0 := by
  have hsmall : 4 * ((centeredProgressionShrink Q 16).carrier \ Q.carrier).card <
      (centeredProgressionShrink Q 32).carrier.card := by
    rw [Finset.sdiff_eq_empty_iff_subset.mpr (centered_progression_shrink_subset Q 16)]
    simp only [Finset.card_empty, mul_zero]
    apply Finset.card_pos.mpr
    refine ⟨0, ?_⟩
    exact (centered_progression_mem_iff _ 0).mpr ⟨fun _ => 0, by simp, by simp⟩
  have hqQ : ∀ i, (q i).1 ∈ Q.carrier ∧ (q i).2 ∈ Q.carrier :=
    fun i => ⟨centered_progression_shrink_subset Q 256 (hq i).1,
      centered_progression_shrink_subset Q 256 (hq i).2⟩
  have hbounded := paired_eight_image_extension Q Q.carrier T L hr (by norm_num : 0 < (1 : Nat)) hsmall
    (fun x hx => (hdata x hx).1) (fun x hx => (hdata x hx).2.1)
    (fun a b c e ha hb hc he heq => column_quad_image_one_of_compatible T L rho a b c e
      (hquad a b c e ha hb hc he heq)) q
    (fun i => ⟨Finset.mem_inter.mpr ⟨(hqQ i).1,(hq i).1⟩,
      Finset.mem_inter.mpr ⟨(hqQ i).2,(hq i).2⟩⟩) hadd
  have hcap : PairedColumnImageRelation T L (rho/2)
      (refinementKernelCap (8*d) (4*d) rho rho) q := by
    simpa only [one_pow, one_mul] using hbounded
  have hLhalf : ∀ x ∈ Q.carrier, IsFreimanLinearOn (bohr (T x) (rho/2)) (L x) := by
    intro x hx
    exact (hdata x hx).2.1.mono (bohr_mono_radius _ (by linarith))
  have hexact := paired_column_image_relation_exact T L q (by positivity : 0 ≤ rho/2)
    (fun i => ⟨hLhalf _ (hqQ i).1,hLhalf _ (hqQ i).2⟩)
    (fun i => ⟨(hdata _ (hqQ i).1).2.2,(hdata _ (hqQ i).2).2.2⟩) hcap hKN
  simpa only [div_div] using hexact

/-- Exact compatibility persists after a radius restriction. -/
theorem ColumnPairCompatible.radius_mono {N : Nat} [NeZero N]
    {T : ZMod N → Finset (ZMod N)} {L : ZMod N → ZMod N → ZMod N}
    {rho sigma : Real} {p q : ZMod N × ZMod N}
    (h : ColumnPairCompatible T L rho p q) (hs : sigma ≤ rho) :
    ColumnPairCompatible T L sigma p q := by
  intro y hy hy'
  exact h y (bohr_mono_radius _ hs hy) (bohr_mono_radius _ hs hy')

/-- Exact source agreement persists after restricting its natural radius. -/
theorem original_eight_exact_agreement_radius_mono {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (Tpsi : Finset (ZMod N))
    (psi : ZMod N → ZMod N) (a : ZMod N) {rho sigma : Real} (hs : sigma ≤ rho) :
    originalEightExactAgreementSet U T L Tpsi psi a rho ⊆
      originalEightExactAgreementSet U T L Tpsi psi a sigma := by
  intro t ht
  obtain ⟨hf, he⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hf, fun y hy => he y (bohr_mono_radius _ hs hy)⟩

end LeanProofs.GowersSzemeredi

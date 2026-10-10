import GowersSzemeredi.Proofs16CommonCoreTranslation
import GowersSzemeredi.Proofs16AllEightImageCore

/-! Quantitatively many anchors remain for every difference in the final
proper progression. This mass will also be needed for eight-tuple source
agreement, where one fixed anchor would give too few representations. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem common_translation_good_count {G I : Type*} [AddCommGroup G] [DecidableEq G] [Fintype I]
    (B D S : Finset G) (shifts : I → G) (hD : ∀ u ∈ B, ∀ i, u+shifts i ∈ D) :
    B.card ≤ (B.filter fun u => ∀ i, u+shifts i ∈ S).card+Fintype.card I*(D \ S).card := by
  let Bad := fun i : I => B.filter fun u => u+shifts i ∉ S
  let BadAll := B.filter fun u => ¬∀ i, u+shifts i ∈ S
  have hbad : ∀ i, (Bad i).card ≤ (D \ S).card := by
    intro i
    apply Finset.card_le_card_of_injOn (fun u => u+shifts i)
    · intro u hu
      exact Finset.mem_sdiff.mpr ⟨hD u (Finset.mem_filter.mp hu).1 i,(Finset.mem_filter.mp hu).2⟩
    · intro u _ v _ he
      exact add_right_cancel he
  have hsub : BadAll ⊆ Finset.univ.biUnion Bad := by
    intro u hu
    obtain ⟨huB,hn⟩ := Finset.mem_filter.mp hu
    obtain ⟨i,hi⟩ := not_forall.mp hn
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨huB,hi⟩⟩
  have hbadAll : BadAll.card ≤ Fintype.card I*(D \ S).card := by
    calc BadAll.card ≤ (Finset.univ.biUnion Bad).card := Finset.card_le_card hsub
      _ ≤ ∑ i, (Bad i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : I, (D \ S).card := Finset.sum_le_sum fun i _ => hbad i
      _ = _ := by simp
  have hp := Finset.card_filter_add_card_filter_not (s := B) (fun u => ∀ i, u+shifts i ∈ S)
  change (B.filter fun u => ∀ i, u+shifts i ∈ S).card+BadAll.card = B.card at hp
  omega

/-- A candidate in `Q/512` and a final difference in `Q/1024` both remain
inside the tiny endpoint progression. -/
theorem progression_difference_anchor_geometry {N : Nat} (Q : CenteredProgression N)
    {a u : ZMod N} (ha : a ∈ (centeredProgressionShrink Q 1024).carrier)
    (hu : u ∈ (centeredProgressionShrink Q 512).carrier) :
    u ∈ (centeredProgressionShrink Q 256).carrier ∧ u+a ∈ (centeredProgressionShrink Q 256).carrier := by
  constructor
  · apply centered_progression_shrink_subset (centeredProgressionShrink Q 256) 2
    simpa only [centered_progression_shrink_comp, Nat.reduceMul] using hu
  · exact centered_progression_add_mem Q (fun i => Q.radius i/512) (fun i => Q.radius i/1024)
      (fun i => Q.radius i/256) (fun i => by omega) hu ha

/-- Every final progression index has a linear-size family of valid
anchors in the tiny core, with all rounding and rank losses explicit. -/
theorem progression_difference_anchor_mass {N : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper) (C : Finset (ZMod N))
    {delta : Real} (hdelta : 0 < delta) (hmass : delta*N ≤ (Q.carrier.card : Real))
    (hloss : (((centeredProgressionShrink Q 256).carrier \ C).card : Real) ≤
      delta*N/(16*(1024 : Real)^Q.rank))
    {a : ZMod N} (ha : a ∈ (centeredProgressionShrink Q 1024).carrier) :
    delta*N/(2*(1024 : Real)^Q.rank) ≤ ((progressionBridgeSet C a).card : Real) := by
  let B := (centeredProgressionShrink Q 512).carrier
  let shifts : Fin 2 → ZMod N := ![0,a]
  have hD : ∀ u ∈ B, ∀ i, u+shifts i ∈ (centeredProgressionShrink Q 256).carrier := by
    intro u hu i
    obtain ⟨h0,h1⟩ := progression_difference_anchor_geometry Q ha hu
    fin_cases i
    · simpa [shifts] using h0
    · simpa [shifts] using h1
  have hc := common_translation_good_count B (centeredProgressionShrink Q 256).carrier C shifts hD
  simp only [Fintype.card_fin] at hc
  let Good := B.filter fun u => ∀ i, u+shifts i ∈ C
  have hGood : Good ⊆ progressionBridgeSet C a := by
    intro u hu
    have hp := (Finset.mem_filter.mp hu).2
    refine Finset.mem_filter.mpr ⟨?_,?_⟩
    · simpa [shifts] using hp 0
    · simpa [shifts] using hp 1
  have hcard : B.card ≤ (progressionBridgeSet C a).card+
      2*((centeredProgressionShrink Q 256).carrier \ C).card := by
    have hle : Good.card ≤ (progressionBridgeSet C a).card := Finset.card_le_card hGood
    have hcount : B.card ≤ Good.card+2*((centeredProgressionShrink Q 256).carrier \ C).card := by
      convert hc using 1 <;> first | rfl | (congr 2; ext u; simp only [Good, Finset.mem_filter])
    omega
  have hR : (B.card : Real) ≤ (progressionBridgeSet C a).card+
      2*(((centeredProgressionShrink Q 256).carrier \ C).card : Real) := by exact_mod_cast hcard
  have hB := centered_progression_shrink_real_mass Q hQ (by decide : 0 < (512 : Nat))
  norm_num only [Nat.cast_ofNat] at hB
  have hBmass : delta*N/(1024 : Real)^Q.rank ≤ (B.card : Real) :=
    (div_le_div_of_nonneg_right hmass (by positivity)).trans hB
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hp : 0 < delta*N/(1024 : Real)^Q.rank := by positivity
  have heq : delta*N/(16*(1024 : Real)^Q.rank) = (delta*N/(1024 : Real)^Q.rank)/16 := by ring
  have heq2 : delta*N/(2*(1024 : Real)^Q.rank) = (delta*N/(1024 : Real)^Q.rank)/2 := by ring
  rw [heq] at hloss
  rw [heq2]
  linarith

end LeanProofs.GowersSzemeredi

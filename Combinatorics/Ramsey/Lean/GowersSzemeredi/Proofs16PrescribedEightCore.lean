import GowersSzemeredi.Proofs16AllEightImageCore

/-! Extend a given near-full compatible core, preserving its identity.
This allows source-agreement properties of the same selected core to
survive the eight-term and final-anchor stages. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A prescribed compatible core supplies a dense tiny endpoint set and
all eight-term image relations, without choosing another representative system. -/
theorem near_full_quad_core_eight_profile {N d H : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper) (S : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    {sigma delta : Real} (hsigma : 0 < sigma) (hH : 0 < H) (hdelta : 0 < delta)
    (hmass : delta*N ≤ (Q.carrier.card : Real))
    (hS : S ⊆ (centeredProgressionShrink Q 16).carrier)
    (hloss : (((centeredProgressionShrink Q 16).carrier \ S).card : Real) ≤ delta*N/(16*(1024 : Real)^Q.rank))
    (hT : ∀ x ∈ S, (T x).card ≤ d)
    (hL : ∀ x ∈ S, IsFreimanLinearOn (bohr (T x) sigma) (L x))
    (hquad : ∀ a b c e : ZMod N, a ∈ S → b ∈ S → c ∈ S → e ∈ S → a-b=c-e →
      ColumnQuadImageRelation T L sigma H a b c e) :
    let C := S ∩ (centeredProgressionShrink Q 256).carrier
    (((centeredProgressionShrink Q 256).carrier \ C).card : Real) ≤ delta*N/(16*(1024 : Real)^Q.rank) ∧
      delta*N/(2*(512 : Real)^Q.rank) ≤ (C.card : Real) ∧ C.Nonempty ∧
      ∀ q : PairedColumnTuple N, (∀ i, (q i).1 ∈ C ∧ (q i).2 ∈ C) → pairedColumnIndex q=0 →
        PairedColumnImageRelation T L (sigma/2) (H^4*refinementKernelCap (8*d) (4*d) sigma sigma) q := by
  intro C
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hsub : (centeredProgressionShrink Q 256).carrier ⊆ (centeredProgressionShrink Q 16).carrier := by
    simpa only [centered_progression_shrink_comp, Nat.reduceMul] using
      centered_progression_shrink_subset (centeredProgressionShrink Q 16) 16
  have hlostiny : ((centeredProgressionShrink Q 256).carrier \ S).card ≤
      ((centeredProgressionShrink Q 16).carrier \ S).card := by
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_sdiff.mp hx).1,(Finset.mem_sdiff.mp hx).2⟩
  have hlostinyR : (((centeredProgressionShrink Q 256).carrier \ S).card : Real) ≤
      ((centeredProgressionShrink Q 16).carrier \ S).card := by exact_mod_cast hlostiny
  have hpow : (512 : Real)^Q.rank ≤ (1024 : Real)^Q.rank :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hloss512 : (((centeredProgressionShrink Q 16).carrier \ S).card : Real) ≤ delta*N/(16*(512 : Real)^Q.rank) :=
    hloss.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hpow (by norm_num)))
  have hmass256 : delta*N/(512 : Real)^Q.rank ≤ ((centeredProgressionShrink Q 256).carrier.card : Real) := by
    have h := centered_progression_shrink_real_mass Q hQ (by decide : 0 < (256 : Nat))
    norm_num only [Nat.cast_ofNat] at h
    exact (div_le_div_of_nonneg_right hmass (by positivity)).trans h
  have hpartition : (((centeredProgressionShrink Q 256).carrier \ S).card : Real)+(C.card : Real) =
      (centeredProgressionShrink Q 256).carrier.card := by
    have h := Finset.card_sdiff_add_card_inter (centeredProgressionShrink Q 256).carrier S
    rw [Finset.inter_comm] at h
    exact_mod_cast h
  have hpositive256 : 0 < delta*N/(512 : Real)^Q.rank := by positivity
  have hCmass : delta*N/(2*(512 : Real)^Q.rank) ≤ (C.card : Real) := by
    have hle : (((centeredProgressionShrink Q 256).carrier \ S).card : Real) ≤
        delta*N/(16*(512 : Real)^Q.rank) := hlostinyR.trans hloss512
    have heq : delta*N/(16*(512 : Real)^Q.rank) = (delta*N/(512 : Real)^Q.rank)/16 := by ring
    have heq2 : delta*N/(2*(512 : Real)^Q.rank) = (delta*N/(512 : Real)^Q.rank)/2 := by ring
    rw [heq] at hle
    rw [heq2]
    linarith
  have hCpos : (0 : Real) < C.card := (by positivity : 0 < delta*N/(2*(512 : Real)^Q.rank)).trans_le hCmass
  have hsmall : 4*((centeredProgressionShrink Q 16).carrier \ S).card < (centeredProgressionShrink Q 32).carrier.card := by
    have h64 : (64 : Real)^Q.rank ≤ (1024 : Real)^Q.rank := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have hloss64 : (((centeredProgressionShrink Q 16).carrier \ S).card : Real) ≤ delta*N/(16*(64 : Real)^Q.rank) :=
      hloss.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left h64 (by norm_num)))
    have hB := centered_progression_shrink_real_mass Q hQ (by decide : 0 < (32 : Nat))
    norm_num only [Nat.cast_ofNat] at hB
    have hBmass : delta*N/(64 : Real)^Q.rank ≤ ((centeredProgressionShrink Q 32).carrier.card : Real) :=
      (div_le_div_of_nonneg_right hmass (by positivity)).trans hB
    have hpos : 0 < delta*N/(64 : Real)^Q.rank := by positivity
    have heq : delta*N/(16*(64 : Real)^Q.rank) = (delta*N/(64 : Real)^Q.rank)/16 := by ring
    rw [heq] at hloss64
    have hR : 4*(((centeredProgressionShrink Q 16).carrier \ S).card : Real) <
        (centeredProgressionShrink Q 32).carrier.card := by linarith
    exact_mod_cast hR
  have hmissing : (centeredProgressionShrink Q 256).carrier \ C =
      (centeredProgressionShrink Q 256).carrier \ S := by
    ext x
    simp only [Finset.mem_sdiff,Finset.mem_inter,C]
    tauto
  refine ⟨?_,hCmass,Finset.card_pos.mp (by exact_mod_cast hCpos),?_⟩
  · rw [hmissing]
    exact hlostinyR.trans hloss
  · intro q hq hadd
    exact paired_eight_image_extension Q S T L hsigma hH hsmall hT hL hquad q hq hadd

end LeanProofs.GowersSzemeredi

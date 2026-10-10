import GowersSzemeredi.Proofs16EightImageExtension
import GowersSzemeredi.Proofs16EightExtensionMassBudget

/-! A near-full core from the actual selected map system supplies a dense
tiny endpoint set on which every additive eight-tuple is compatible. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Preserve both the near-full larger core and the dense tiny endpoint
set, so the subsequent difference-map construction has enough anchors. -/
theorem exists_progression_all_eight_image_core {N d K : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    {rho delta eta : Real} (hrho : 0 < rho) (hK : 0 < K) (hdelta : 0 < delta)
    (hmass : delta*N ≤ (Q.carrier.card : Real))
    (heta : eta ≤ delta^3/(1024*(65536 : Real)^Q.rank))
    (hT : ∀ x ∈ Q.carrier, (T x).card ≤ d)
    (hL : ∀ x ∈ Q.carrier, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hfail : ((progressionMapImageFailures Q.carrier T L rho K).card : Real) ≤ eta*(N : Real)^3) :
    let M := K*K*refinementKernelCap (4*d) (2*d) rho rho
    let H := M*M*refinementKernelCap (4*d) (2*d) (rho/2) (rho/2)
    ∃ (S C : Finset (ZMod N)), S ⊆ (centeredProgressionShrink Q 16).carrier ∧
      C = S ∩ (centeredProgressionShrink Q 256).carrier ∧
      (((centeredProgressionShrink Q 16).carrier \ S).card : Real) ≤ delta*N/(16*(1024 : Real)^Q.rank) ∧
      delta*N/(2*(512 : Real)^Q.rank) ≤ (C.card : Real) ∧ C.Nonempty ∧
      ∀ q : PairedColumnTuple N, (∀ i, (q i).1 ∈ C ∧ (q i).2 ∈ C) → pairedColumnIndex q = 0 →
        PairedColumnImageRelation T L (rho/8) (H^4*refinementKernelCap (8*d) (4*d) (rho/4) (rho/4)) q := by
  intro M H
  obtain ⟨S,hS,hloss,hquad⟩ := exists_progression_near_full_quad_core Q hQ T L hrho hK hdelta hmass heta hT hL hfail
  let C := S ∩ (centeredProgressionShrink Q 256).carrier
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
  have hM : 0 < M := Nat.mul_pos (Nat.mul_pos hK hK) (refinementKernelCap_pos _ _ hrho hrho)
  have hhalf : 0 < rho/2 := by positivity
  have hH : 0 < H := Nat.mul_pos (Nat.mul_pos hM hM) (refinementKernelCap_pos _ _ hhalf hhalf)
  refine ⟨S,C,hS,rfl,hloss,hCmass,Finset.card_pos.mp (by exact_mod_cast hCpos), ?_⟩
  intro q hq hadd
  have hresult := paired_eight_image_extension Q S T L (by positivity : 0 < rho/4) hH hsmall
    (fun x hx => hT x (centered_progression_shrink_subset Q 16 (hS hx)))
    (fun x hx => column_freiman_smaller_radius _ _ (by linarith)
      (hL x (centered_progression_shrink_subset Q 16 (hS hx)))) hquad q hq hadd
  simpa only [show (rho/4)/2 = rho/8 by ring] using hresult

end LeanProofs.GowersSzemeredi

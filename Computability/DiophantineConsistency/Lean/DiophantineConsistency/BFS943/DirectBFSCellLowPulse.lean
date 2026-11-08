import DiophantineConsistency.BFS943.DirectBFSCellLowMask
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSCellLowPulse
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticPackingBlocks
open DirectBFSCellDigit DirectBFSCellDigitUniform DirectBFSPackedCell DirectBFSUniformPackedCell
open DirectBFSCellDigitSupported DirectBFSBaseLowNoCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem local_noCarry (a d k : V) (ha : a≠1) (hd : d≤1) (hk : k<8807) :
    NoCarry (cellDigit a d k) (dig 67 (CompactConcreteIncrement.mask:V) k) := by
  have hb := cellDigit_le_one a d k hd
  rcases le_one_iff_eq_zero_or_one.mp hb with hz | ho
  · rw [hz,noCarry_iff]; intro i; simp
  · obtain ⟨n,he,hs⟩ := cellDigit_supported a d k ha hk (by rw [ho]; simp)
    have hn : n<8807 := by rw [he] at hk; exact_mod_cast hk
    rw [ho,he]
    exact one_noCarry_even _ (supported_mask_even n hn hs)

theorem packed_noCarry (a d : V) (ha : a≠1) (hd : d≤1) :
    NoCarry (packedCell a d) (CompactConcreteIncrement.mask:V) := by
  letI : 𝚺₁-Function₃ (cellDigit : V → V → V → V) := cellDigit_uniform
  haveI : 𝚺₁-Function₁ (cellDigit a d) := by definability
  let g : V → V := fun j => dig 67 (CompactConcreteIncrement.mask:V) j
  letI : 𝚺₁-Function₁ g := by unfold g; definability
  have hmask : bsum 67 g 8807=(CompactConcreteIncrement.mask:V) := by
    apply bsum_unique (f:=g) (fun j _ => dig_lt 67 (CompactConcreteIncrement.mask:V) j)
    exact ⟨CompactConcreteMask.model_lt,fun j _ => rfl⟩
  have hc := bsum_noCarry (w:=(67:V)) (f:=cellDigit a d) (g:=g) (n:=8807)
    (fun j _ => digit_bound a d hd j) (fun j _ => dig_lt 67 _ j)
    (fun j hj => local_noCarry a d j ha hd hj)
  unfold packedCell
  rwa [hmask] at hc

theorem normalized_noCarry (a d : V) (ha : a≠1) :
    NoCarry (normalizedCell a d) (CompactConcreteIncrement.mask:V) := by
  exact packed_noCarry a (d%2) ha (lt_two_iff_le_one.mp (mod_lt d (by norm_num)))
#print axioms DirectBFSCellLowPulse.local_noCarry
#print axioms DirectBFSCellLowPulse.packed_noCarry
#print axioms DirectBFSCellLowPulse.normalized_noCarry
end DirectBFSCellLowPulse

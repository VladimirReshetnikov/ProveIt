import DiophantineConsistency.BFS943.DirectBFS80CleanCarry
import DiophantineConsistency.BFS943.DirectBFSSelectedOrigin
import DiophantineConsistency.BFS943.DirectBFSForeignBands
import DiophantineConsistency.Compact44.SelectedBandWord
import DiophantineConsistency.Compact44.HighMaskLocal

/-! Occupied compact origin slots from the direct-BFS 80-graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFS80Occupied
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry
open CompactPartialBandRotation CompactPartialBand CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactGenericAlignedMass CompactTwoBandFlatten CompactHeterogeneousCarry CleanGeometry FixedGraphSelectedInputs
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80NaturalTransport
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
attribute [local irreducible] DirectBFSModelMass.selectors DirectBFSModelMass.copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_occupied (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    ∀ j : Fin 41,34≤j.val → dig 67 (Cnat p v) (position j:V)=1 := by
  obtain ⟨N,t,hN,hJ,hq,_hle,_hw,htcase,_hcarry,hTzero,_hTpred,_hc,hraw⟩ :=
    DirectBFS80CleanCarry.graph_clean_carry p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N',_hN',_hJ',hq',_hle',_hw',_hcarry',h0,hzero,hbool⟩ :=
    DirectBFS80Support.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N'',_hN'',_hJ'',hq'',_hC,_h0'',_hslots,hhigh⟩ :=
    Direct80FixedSlots.graph_fixed_slots p v hp0 hp2 hp3 hv hz
  have eq1 : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  have eq2 : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N'
  subst N''
  let n : V := 8807*N
  let T := temporalWord n (rankNat p v-67*n) (Cnat p v)
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8807:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8807)
    simpa only [n,mul_one] using h
  have ht1 : (4393:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht2 : (5495:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht : t<n := by
    rcases htcase with h|h
    · rw [h]; exact ht1
    · rw [h]; exact ht2
  have hqexp : q p v=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : Cnat p v<Exp.exp (67*n) := by
    dsimp [Cnat]
    exact BandCarryInputs.source_word_bound (q p v) n (v 1) (v 2) hqexp (hv 1)
  have hbands := DirectBFSRawColumn.flatten position n (Cnat p v) T t
  rw [hTzero,add_zero] at hbands
  have hresult : dig 67 (v 1) t=DirectBFSRawColumn.columnBand position 4393 n (Cnat p v) t+
      DirectBFSRawColumn.columnBand position 5495 n (Cnat p v) t+RawColumnBands.bareColumn n (Cnat p v) t := by
    rw [hraw]
    exact hbands
  obtain ⟨hf1,hf2,hb1,hb2⟩ := DirectBFSForeignBands.foreign_and_bare N (Cnat p v) hN hC hzero
  have hin1 : Inputs n (Cnat p v) 4393 := SelectedBandWord.bounded n _ 4393 ht1 (by norm_num) hbool
  have hin2 : Inputs n (Cnat p v) 5495 := SelectedBandWord.bounded n _ 5495 ht2 (by norm_num) hbool
  have hhigh' : NoCarry (v 1) ((highNat:V)*rep (67*8807) N-1) := by rw [←hJ]; exact hhigh
  have hlocal := HighMaskLocal.local_nocarry N (v 1) hN hhigh'
  rcases htcase with ht1eq | ht2eq
  · rw [ht1eq,hf1,hb1,add_zero,add_zero] at hresult
    have hcol := DirectBFSRawColumn.band_column position 4393 n (Cnat p v) 4393 hn ht1 hC
    have hband : dig 67 (v 1) 4393=DirectBFSSelectedOrigin.decoderBand n (Cnat p v) 4393 := by
      rw [hresult,hcol]
      rfl
    have hnc := hlocal.1
    rw [hband] at hnc
    have hdecode := DirectBFSSelectedOrigin.decode n (Cnat p v) 4393 hin1 hnc
    exact DirectBFSSelectedOrigin.selected_origin_occupied n _ 4393 ht1 (by norm_num) h0 hin1 hdecode
  · rw [ht2eq,hf2,hb2,zero_add,add_zero] at hresult
    have hcol := DirectBFSRawColumn.band_column position 5495 n (Cnat p v) 5495 hn ht2 hC
    have hband : dig 67 (v 1) 5495=DirectBFSSelectedOrigin.decoderBand n (Cnat p v) 5495 := by
      rw [hresult,hcol]
      rfl
    have hnc := hlocal.2
    rw [hband] at hnc
    have hdecode := DirectBFSSelectedOrigin.decode n (Cnat p v) 5495 hin2 hnc
    exact DirectBFSSelectedOrigin.selected_origin_occupied n _ 5495 ht2 (by norm_num) h0 hin2 hdecode

#print axioms DirectBFS80Occupied.graph_occupied
end DirectBFS80Occupied

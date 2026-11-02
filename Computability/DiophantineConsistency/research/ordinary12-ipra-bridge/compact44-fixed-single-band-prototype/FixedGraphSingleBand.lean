import DiophantineConsistency.ForeignBandsZero
import DiophantineConsistency.FixedGraphRawBands
import DiophantineConsistency.FixedGraphSupportCarry
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphSingleBand
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten CompactPartialBandRotation
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_single_band (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    ∃ N w t : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      let T := temporalWord (8807*N) (R-67*(8807*N)) C
      let X := GenericBandCarryFamily.word (8807*N) C (bandOffsets position) T
      CarryInput 67 (8807*N) (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧
      dig 67 T t=0 ∧ dig 67 T (cyc (8807*N) t 1)≤Exp.exp 66 ∧
      carry 67 (8807*N) a X (cyc (8807*N) t 1)=0 ∧
      ((t=4393 ∧ dig 67 (v 1) t=FixedGraphRawBands.decoderBand position 4393 (8807*N) C t) ∨
       (t=5495 ∧ dig 67 (v 1) t=FixedGraphRawBands.decoderBand position 5495 (8807*N) C t)) := by
  obtain ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,htcase,hcarry,hTzero,hTpred,hc,hbands⟩ :=
    FixedGraphRawBands.graph_bands v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h0,hzero,hbool⟩ :=
    FixedGraphSupportCarry.graph_support_carry v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-v 1-v 2
  let n : V := 8807*N
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8807:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8807)
    simpa only [n,mul_one] using h
  have ht₁ : (4393:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht₂ : (5495:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hqexp : q=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (67*n) := by
    dsimp [C]
    exact BandCarryInputs.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  obtain ⟨hf₁,hf₂,hb₁,hb₂⟩ := ForeignBandsZero.foreign_and_bare N C hN hC hzero
  have hd₁ : FixedGraphRawBands.decoderBand position 5495 n C 4393=0 := by
    have h := band_column position 5495 n C 4393 hn ht₁ hC
    change columnBand position 5495 n C 4393 = FixedGraphRawBands.decoderBand position 5495 n C 4393 at h
    rw [hf₁] at h
    exact h.symm
  have hd₂ : FixedGraphRawBands.decoderBand position 4393 n C 5495=0 := by
    have h := band_column position 4393 n C 5495 hn ht₂ hC
    change columnBand position 4393 n C 5495 = FixedGraphRawBands.decoderBand position 4393 n C 5495 at h
    rw [hf₂] at h
    exact h.symm
  refine ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,hcarry,hTzero,hTpred,hc,?_⟩
  rcases htcase with ht | ht
  · left
    refine ⟨ht,?_⟩
    rw [ht] at hbands ⊢
    rw [hd₁,hb₁,add_zero,add_zero] at hbands
    exact hbands
  · right
    refine ⟨ht,?_⟩
    rw [ht] at hbands ⊢
    rw [hd₂,hb₂,zero_add,add_zero] at hbands
    exact hbands
#print axioms FixedGraphSingleBand.graph_single_band
end FixedGraphSingleBand

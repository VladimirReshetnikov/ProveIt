import DiophantineConsistency.Compact44.RawColumnBands
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphRawBands
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def decoderBand (pos : Fin 41→ℕ) (T : ℕ) (n C k : V) : V :=
  (∑ j, CompactPartialBand.selectorDigit n C k T j) + Exp.exp 10 *
    ((∑ j, (Exp.exp 41-Compact943Decoder.tileValue (V:=V) j)*CompactPartialBand.selectorDigit n C k T j) +
     ∑ j, (2:V)^j.val*CompactPartialBand.copyDigit pos n C k T j)

theorem graph_bands (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    ∃ N w t : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧ (t=4393 ∨ t=5495) ∧
      let T := temporalWord (8807*N) (R-67*(8807*N)) C
      let X := GenericBandCarryFamily.word (8807*N) C (bandOffsets position) T
      CarryInput 67 (8807*N) (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧
      dig 67 T t=0 ∧ dig 67 T (cyc (8807*N) t 1)≤Exp.exp 66 ∧
      carry 67 (8807*N) a X (cyc (8807*N) t 1)=0 ∧
      dig 67 (v 1) t=decoderBand position 4393 (8807*N) C t +
        decoderBand position 5495 (8807*N) C t + RawColumnBands.bareColumn (8807*N) C t := by
  obtain ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,htcase,hcarry,hTzero,hTpred,hc,hraw⟩ :=
    FixedGraphCleanCarry.graph_clean_carry v hv hz
  dsimp only at *
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8807*N
  let T : V := temporalWord n (R-67*n) C
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8807:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8807)
    simpa only [n,mul_one] using h
  have ht : t<n := by
    rcases htcase with ht | ht <;> rw [ht] <;> exact lt_of_lt_of_le (by norm_num) hnge
  have hqexp : q=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (67*n) := by
    dsimp [C]
    exact BandCarryInputs.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  have hband := RawColumnBands.decoder_bands position n C T t hn ht hC
  rw [hTzero,add_zero] at hband
  have hresult : dig 67 (v 1) t=decoderBand position 4393 n C t+
      decoderBand position 5495 n C t+RawColumnBands.bareColumn n C t := by
    rw [hraw]
    simpa only [decoderBand] using hband
  exact ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,htcase,hcarry,hTzero,hTpred,hc,hresult⟩
#print axioms FixedGraphRawBands.graph_bands
end FixedGraphRawBands

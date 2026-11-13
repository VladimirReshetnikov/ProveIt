import Direct80FixedCongruence
import DiophantineConsistency.ModelBandCut
import DiophantineConsistency.ActualTemporalBand

/-! Carry the 80 graph congruence through kernel bands and temporal rotation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Direct80BandTemporal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits
open CompactPartialBandRotation CompactBitRotation
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80NaturalTransport
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_band_temporal (p : Fin 4 → ℕ) (v : Fin 10 → V) (pos : Fin 41 → ℕ)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hK : (p 1:V)=kernelBand pos 4393+kernelBand pos 5495+TwoBand.bareKernel) :
    ∃ N : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      (67*8807)*N≤rankNat p v ∧ v 5=Exp.exp (rankNat p v-(67*8807)*N) ∧
      0<b p v ∧ v 1<b p v ∧
      ((rotatedBand pos 4393 (8807*N) (Cnat p v)+rotatedBand pos 5495 (8807*N) (Cnat p v)+
        TwoBand.bareRotated (8807*N) (Cnat p v))+
        temporalWord (8807*N) (rankNat p v-67*(8807*N)) (Cnat p v))%
          (Exp.exp (67*(8807*N))-1)=v 1 ∧
      temporalWord (8807*N) (rankNat p v-67*(8807*N)) (Cnat p v)<Exp.exp (67*(8807*N)) ∧
      (∀ j : V, dig 67 (temporalWord (8807*N) (rankNat p v-67*(8807*N)) (Cnat p v)) j≤Exp.exp 67-1) ∧
      dig 67 (Cnat p v) 0=1 ∧ ∀ j<8807*N, dig 67 (Cnat p v) j≤3 := by
  obtain ⟨N,hN,hJ,hq,hle,hw,hpos,hF,hcongr,hzero,hdigits⟩ :=
    Direct80FixedCongruence.graph_fixed_congruence p v hp0 hp2 hp3 hv hz
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hqexp : q p v=Exp.exp (67*((8807:V)*N)) := by rw [←mul_assoc]; exact hq
  have hqdef : q p v=1+b p v := by dsimp [q]; ring
  have hbands := ModelBandCut.graph_congruence_to_bands pos (p 1:V) ((8807:V)*N)
    (q p v) (b p v) (Cnat p v) (v 5) (v 1) hn hpos hqdef hqexp hK hcongr
  have hM : 0<Exp.exp (67*((8807:V)*N))-1 := by
    rw [←hqexp,hqdef,add_comm,add_tsub_cancel_right]
    exact hpos
  have hwexp : v 5=Exp.exp (rankNat p v-67*((8807:V)*N)) := by rw [←mul_assoc]; exact hw
  have ht := ActualTemporalBand.graph_temporal_word ((8807:V)*N) (q p v) (v 1) (v 2)
    (Cnat p v) (rankNat p v) (v 5)
    (rotatedBand pos 4393 (8807*N) (Cnat p v)+rotatedBand pos 5495 (8807*N) (Cnat p v)+
      TwoBand.bareRotated (8807*N) (Cnat p v)) (v 1)
    hn hM hqexp (hv 1) rfl hwexp hbands
  exact ⟨N,hN,hJ,hq,hle,hw,hpos,hF,ht.1,ht.2.1,ht.2.2,hzero,hdigits⟩

#print axioms Direct80BandTemporal.graph_band_temporal
end Direct80BandTemporal

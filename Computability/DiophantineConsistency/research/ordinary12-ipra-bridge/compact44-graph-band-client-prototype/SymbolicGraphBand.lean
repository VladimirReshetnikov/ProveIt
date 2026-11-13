import DiophantineConsistency.ModelBandCut
import DiophantineConsistency.FreeJGraphCongruenceExplore
import DiophantineConsistency.SymbolicKBandDraft
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymbolicGraphBand
open DiophantineConsistency CompactPartialBandRotation SymbolicKBandDraft
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat

theorem symbolic_bands (B K L H : ℕ) (v : Fin 12 → V) (pos : Fin 41 → ℕ)
    (hB : (B:V)+1=Exp.exp ((67:V)*8807)) (hL : L=lowNat) (hH : H=highNat)
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (ports B K L H j:ℤ))) v)
    (hK : (K:V)=kernelBand pos 4393+kernelBand pos 5495+TwoBand.bareKernel) :
    let p := ports B K L H
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      ((rotatedBand pos 4393 (8807*N) C + rotatedBand pos 5495 (8807*N) C +
        TwoBand.bareRotated (8807*N) C)+w*C) % (Exp.exp (67*(8807*N))-1)=v 1 ∧
      dig 67 C 0=1 ∧ ∀ k<8807*N, dig 67 C k≤3 := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hgraph,h0,hlim⟩ :=
    FreeJGraphCongruenceExplore.symbolic_aligned B K L H v hB hL hH hv hz
  dsimp only at *
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hqexp : 1+v 0*(ports B K L H 0:V)=Exp.exp (67*((8807:V)*N)) := by
    rw [← mul_assoc]; exact hq
  have hp : (ports B K L H 1:V) = (K:V) := by rfl
  rw [hp] at hgraph
  have hbands := ModelBandCut.graph_congruence_to_bands pos (K:V) ((8807:V)*N)
    (1+v 0*(ports B K L H 0:V)) (v 0*(ports B K L H 0:V))
    (1+v 0*(ports B K L H 0:V)-v 1-v 2) w (v 1)
    hn hpos rfl hqexp hK hgraph
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hbands,h0,hlim⟩

theorem fixed_symbolic_bands (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      ((rotatedBand position 4393 (8807*N) C + rotatedBand position 5495 (8807*N) C +
        TwoBand.bareRotated (8807*N) C)+w*C) % (Exp.exp (67*(8807*N))-1)=v 1 ∧
      dig 67 C 0=1 ∧ ∀ k<8807*N, dig 67 C k≤3 := by
  exact symbolic_bands CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat v position
    CompactFixedBeta.beta_identity rfl rfl hv hz (symbolic_kernel_band_cast (V:=V))
#print axioms SymbolicGraphBand.symbolic_bands
#print axioms SymbolicGraphBand.fixed_symbolic_bands
end SymbolicGraphBand

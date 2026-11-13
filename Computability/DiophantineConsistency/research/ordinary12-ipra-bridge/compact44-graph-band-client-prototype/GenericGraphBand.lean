import DiophantineConsistency.ModelBandCut
import DiophantineConsistency.FreeJGraphCongruenceExplore
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace GenericGraphBand
open DiophantineConsistency CompactPartialBandRotation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_bands (p : Fin 4 → ℕ) (v : Fin 12 → V) (pos : Fin 41 → ℕ)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hbeta : (46:V)≤(p 0:V)) (hport : (p 0:V)=Exp.exp ((67:V)*8807)-1)
    (hK : (p 1:V) = kernelBand pos 4393 + kernelBand pos 5495 + TwoBand.bareKernel) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ (67*8807)*N≤R ∧
      w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      ((rotatedBand pos 4393 (8807*N) C + rotatedBand pos 5495 (8807*N) C +
        TwoBand.bareRotated (8807*N) C)+w*C) % (Exp.exp (67*(8807*N))-1)=v 1 := by
  obtain ⟨N,w,hN,hq,hle,hw,hv5,hpos,hbound,hgraph⟩ :=
    FreeJGraphCongruenceExplore.graph_aligned_congruence p v ((67:V)*8807)
      hb hl hh hv hz hbeta (by norm_num) hport
  dsimp only at *
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hqexp : 1+v 0*(p 0:V)=Exp.exp (67*((8807:V)*N)) := by
    rw [← mul_assoc]; exact hq
  have hbands := ModelBandCut.graph_congruence_to_bands pos (p 1:V) ((8807:V)*N)
    (1+v 0*(p 0:V)) (v 0*(p 0:V)) (1+v 0*(p 0:V)-v 1-v 2) w (v 1)
    hn hpos rfl hqexp hK hgraph
  exact ⟨N,w,hN,hq,hle,hw,hv5,hpos,hbound,hbands⟩
#print axioms GenericGraphBand.graph_bands
end GenericGraphBand

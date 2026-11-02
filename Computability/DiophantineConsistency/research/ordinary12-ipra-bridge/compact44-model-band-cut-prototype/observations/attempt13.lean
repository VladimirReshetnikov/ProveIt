import DiophantineConsistency.SymbolicKBandDraft
import DiophantineConsistency.CompactSameWitnessSaturation2
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SameWitnessBand
open DiophantineConsistency CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactPartialBandRotation SymbolicKBandDraft CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat

theorem same_witness_graph_bands (v : Fin 12 → V)
    (hv : ∀ j, 0 < v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j : ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      ((rotatedBand position 4393 (8807*N) C + rotatedBand position 5495 (8807*N) C +
        TwoBand.bareRotated (8807*N) C) + w*C) % (Exp.exp (67*(8807*N))-1)=v 1 ∧
      dig 67 C 0=1 ∧ (∀ k<8807*N, dig 67 C k≤3) ∧
      NoCarry (C-1) ((p 2:V)*v 0+1) ∧ NoCarry (v 1) ((highNat:V)*v 0-1) := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hcongr,h0,hlim,hc1,hc2⟩ :=
    CompactSameWitnessSaturation.fixed_graph_saturation (paramKernel rho) v hv hz
  dsimp only at *
  have hn : 0 < (8807:V)*N := mul_pos (by norm_num) hN
  have hm : Exp.exp (67*((8807:V)*N))-1 = v 0*((ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat 0):V) := by
    rw [← mul_assoc, ← hq, add_comm, add_tsub_cancel_right]
  have hp : ((ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat 1):V) = ((paramKernel rho:ℕ):V) := by rfl
  have hg := hcongr
  rw [hp, ← hm] at hg
  have hb := TwoBand.combined_congr position ((paramKernel rho:ℕ):V) ((8807:V)*N)
    (1+v 0*((ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat 0):V)-v 1-v 2) w (v 1)
    hn (by rw [hm]; exact hpos) (symbolic_kernel_band_cast (V:=V)) hg
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hb,h0,hlim,hc1,hc2⟩
#print axioms SameWitnessBand.same_witness_graph_bands
end SameWitnessBand

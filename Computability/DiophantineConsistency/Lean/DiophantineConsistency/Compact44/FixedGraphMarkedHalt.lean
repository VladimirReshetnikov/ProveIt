/- SOURCE-ONLY DRAFT: not compiled; requires coherent suffix and review. -/
import DiophantineConsistency.Compact44.OldWordIdentification
import DiophantineConsistency.ArithmeticWangSoundness
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphMarkedHaltDraft
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticWindowDigits ArithmeticPackingBlocks ArithmeticWangSoundness ArithmeticCantor
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_halts (v : Fin 12 → V) (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N W s t : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ s<N ∧
      ((R-67*(8807*N))/67)%(8807*N)=8807*s ∧
      Blocks 10 (OrbitRowWord.row C N 1) N W ∧ t<N ∧
      first (ArithmeticMachineRun215.run t)=0 := by
  obtain ⟨N,W,s,hN,hq,hs,hshift,hW,hword⟩ := CompactLocalWord.graph_local_word v hv hz
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-v 1-v 2
  let b : V → V := OrbitRowWord.row C N 1
  letI : 𝚺₁-Function₁ b := OrbitRowWord.row_definable C N 1
  have hm := OldWordIdentificationDraft.local_to_marked hword
  letI : 𝚺₁-Function₁ (fun j => CompactInverseDraft.inverseLookup (b j)) := hm.1
  obtain ⟨t,ht,hh⟩ := ArithmeticWangSoundness.marked_halts hm.2
  exact ⟨N,W,s,t,hN,hq,hs,hshift,hW,ht,hh⟩
#print axioms FixedGraphMarkedHaltDraft.graph_halts
end FixedGraphMarkedHaltDraft

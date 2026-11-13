import DiophantineConsistency.FixedGraphMarkedHalt
import FreeJHaltModelZero

/-! Conditional model equivalence for the exact common symbolic tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactSymbolicModelIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ModelDifferenceRing ArithmeticRepunit
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactConstructedRank
open CompactHaltPackedWord FreeJHaltModelZero
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)

/-- The reverse direction needs only the exact symbolic literal and positivity.
The forward direction retains four explicit model port-cast conditions. -/
theorem model_iff
    (hbeta : ∀ T : V, ι (rep 590069 (haltLength T))*((p 0 : ℤ) : DiffRing V) =
      ι (Exp.exp ((590069:V)*haltLength T)-1))
    (hK : ((p 1 : ℤ) : DiffRing V)=ι (paramKernel rho : V))
    (hMC : ((p 2 : ℤ) : DiffRing V)=ι (low:V))
    (hMF : ((p 3 : ℤ) : DiffRing V)=ι (high+(Exp.exp (590069:V)-1))) :
    (∃ v : Fin 12 → V, (∀ j, 0<v j) ∧ InternalZero (literal p) v) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    have h := FixedGraphMarkedHaltDraft.graph_halts v hv hz
    obtain ⟨N,W,s,t,hN,hq,hs,hshift,hW,ht,hh⟩ := h
    exact ⟨t,hh⟩
  · rintro ⟨T,hT⟩
    exact halt_positive_zero_of_ports T p hT (hbeta T) hK hMC hMF

#print axioms CompactSymbolicModelIff.model_iff
end CompactSymbolicModelIff

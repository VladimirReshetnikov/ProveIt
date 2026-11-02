import DiophantineConsistency.CompactSymbolicKernelOpaque
import DiophantineConsistency.CompactGraphDerivedRadix
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactDirectParamGraphDraft
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts

def directK : ℕ := CompactSymbolicKernelOpaque.paramKernel CompactSymbolicKernel.rho
attribute [local irreducible] directK
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem direct_graph_digits (v : Fin 12 → V) (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j =>
      (ports CompactFixedBeta.betaNat directK lowNat highNat j:ℤ))) v) :
    ∃ N : V, 0<N ∧
      (let q : V := 1+v 0*(ports CompactFixedBeta.betaNat directK lowNat highNat 0:V)
       let C : V := q-v 1-v 2
       q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
         dig 67 C 0=1 ∧ ∀ k < 8807*N, dig 67 C k≤3) := by
  exact CompactGraphDerivedRadix.fixed_graph_digits directK v hv hz
#print axioms CompactDirectParamGraphDraft.direct_graph_digits
end CompactDirectParamGraphDraft

import Trace75BFSCarry
import Trace75FixedSlots
import DiophantineConsistency.CleanModelSupport

/-! Actual trace75 graph carry and low-mask support, at the same radix length. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75BFSSupport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits
open CompactPartialBandRotation CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten CompactHeterogeneousCarry CleanGeometry
open Trace75Factors Trace75Rank Trace75NaturalTransport
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_support_carry (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ N : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      (67*8807)*N≤rankNat p v ∧ v 5=Exp.exp (rankNat p v-(67*8807)*N) ∧
      CarryInput 67 (8807*N) (v 1) 1
        (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
        (GenericBandCarryFamily.coefficient (fun x => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies x : V)))
        (GenericBandCarryFamily.word (8807*N) (Cnat p v) (bandOffsets position)
          (temporalWord (8807*N) (rankNat p v-67*(8807*N)) (Cnat p v))) ∧
      dig 67 (Cnat p v) 0=1 ∧
      (∀ j<8807*N, ¬Bad (j%8807) → dig 67 (Cnat p v) j=0) ∧
      (∀ j<8807*N, j%8807≠1063 → dig 67 (Cnat p v) j≤1) := by
  obtain ⟨N,hN,hJ,hq,hle,hw,hcarry⟩ :=
    Trace75BFSCarry.graph_indexed_carry p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N',_hN',_hJ',hq',_hC,hzero,hslots,_hhigh⟩ :=
    Trace75FixedSlots.graph_fixed_slots p v hp0 hp2 hp3 hv hz
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  refine ⟨N,hN,hJ,hq,hle,hw,hcarry,hzero,?_,?_⟩
  · exact CleanModelSupport.zero_outside _ _ hslots
  · apply CleanModelSupport.boolean_away_special _ _ ?_ hslots
    rw [hzero]

#print axioms Trace75BFSSupport.graph_support_carry
end Trace75BFSSupport

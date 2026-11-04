import DiophantineConsistency.Compact44.FixedGraphSupportCarry
import DiophantineConsistency.Compact44.CleanSafeSource
import DiophantineConsistency.Compact44.CyclicAnyPhase
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphSafeSource
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten CleanGeometry
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_safe_sources (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      CarryInput 67 (8807*N) (v 1) 1
        (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
        (GenericBandCarryFamily.coefficient (fun x => (alignedCoeff selectors copies x : V)))
        (GenericBandCarryFamily.word (8807*N) C (bandOffsets position)
          (temporalWord (8807*N) (R-67*(8807*N)) C)) ∧
      (∀ D : V, ∃ k, (k=cyc (8807*N) 4393 D ∨ k=cyc (8807*N) 5495 D) ∧
         k<8807*N ∧ dig 67 C k=0 ∧
         dig 67 C (cyc (8807*N) k 1)≤1 ∧ dig 67 C (cyc (8807*N) k 2)≤1) := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,h0,hzero,hbool⟩ :=
    FixedGraphSupportCarry.graph_support_carry v hv hz
  dsimp only at *
  refine ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,?_⟩
  intro D
  let k₁ := cyc (8807*N) 4393 D
  let k₂ := cyc (8807*N) 5495 D
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hp₁ : k₁%8807=cyc 8807 4393 D := by
    dsimp [k₁]
    rw [CyclicAnyPhase.cyc_period 8807 N 4393 D (by norm_num) hN,
      mod_eq_self_of_lt (by norm_num : (4393:V)<8807)]
  have hp₂ : k₂%8807=cyc 8807 5495 D := by
    dsimp [k₂]
    rw [CyclicAnyPhase.cyc_period 8807 N 5495 D (by norm_num) hN,
      mod_eq_self_of_lt (by norm_num : (5495:V)<8807)]
  exact CleanSafeSource.choose_source N _ D k₁ k₂ hN (cyc_lt hn _ _) (cyc_lt hn _ _) hp₁ hp₂ hzero hbool
#print axioms FixedGraphSafeSource.graph_safe_sources
end FixedGraphSafeSource

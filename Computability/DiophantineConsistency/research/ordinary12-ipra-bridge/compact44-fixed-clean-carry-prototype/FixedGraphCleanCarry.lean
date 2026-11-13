import DiophantineConsistency.FixedGraphTemporalClean
import DiophantineConsistency.TemporalCarryExact
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphCleanCarry
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_clean_carry (v : Fin 12 → V)
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
      dig 67 (v 1) t=raw 67 a X t := by
  obtain ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,htcase,hcarry,hTzero,hTpred⟩ :=
    FixedGraphTemporalClean.graph_temporal_clean v hv hz
  dsimp only at *
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8807*N
  let T : V := temporalWord n (R-67*n) C
  let A := fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V)
  have hnge : (8807:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8807)
    simpa only [n,mul_one] using h
  have ht : t<n := by
    rcases htcase with ht | ht <;> rw [ht] <;> exact lt_of_lt_of_le (by norm_num) hnge
  have hroom : (∑ j, A j*3)+1<Exp.exp 66 := ConcreteCarryRoom.aligned_room
  have hclean := TemporalCarryExact.clean_exact n C T (v 1) A (bandOffsets position) hcarry t ht hroom hTzero hTpred
  exact ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,htcase,hcarry,hTzero,hTpred,hclean.1,hclean.2⟩
#print axioms FixedGraphCleanCarry.graph_clean_carry
end FixedGraphCleanCarry

import DiophantineConsistency.FixedGraphSafeSource
import DiophantineConsistency.TemporalSafeCyclic
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphTemporalClean
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_temporal_clean (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w t : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      (t=4393 ∨ t=5495) ∧
      CarryInput 67 (8807*N) (v 1) 1
        (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
        (GenericBandCarryFamily.coefficient (fun x => (alignedCoeff selectors copies x : V)))
        (GenericBandCarryFamily.word (8807*N) C (bandOffsets position)
          (temporalWord (8807*N) (R-67*(8807*N)) C)) ∧
      dig 67 (temporalWord (8807*N) (R-67*(8807*N)) C) t=0 ∧
      dig 67 (temporalWord (8807*N) (R-67*(8807*N)) C) (cyc (8807*N) t 1)≤Exp.exp 66 := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,hsources⟩ :=
    FixedGraphSafeSource.graph_safe_sources v hv hz
  dsimp only at *
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8807*N
  let E : V := R-67*n
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8807:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8807)
    simpa only [n,mul_one] using h
  have hqexp : q=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (67*n) := by
    dsimp [C]
    exact BandCarryInputs.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  obtain ⟨k,hkcase,hkin,hkzero,hkone,hktwo⟩ := hsources ((E/67)%n)
  obtain ⟨t,htcase,hkeq⟩ : ∃ t : V, (t=4393 ∨ t=5495) ∧ k=cyc n t ((E/67)%n) := by
    rcases hkcase with hk1 | hk2
    · exact ⟨4393,Or.inl rfl,hk1⟩
    · exact ⟨5495,Or.inr rfl,hk2⟩
  have ht : t<n := by
    rcases htcase with ht | ht <;> rw [ht] <;> exact lt_of_lt_of_le (by norm_num) hnge
  have hzero : dig 67 C (cyc n t ((E/67)%n))=0 := by simpa only [←hkeq] using hkzero
  have hone : dig 67 C (cyc n (cyc n t ((E/67)%n)) 1)≤1 := by simpa only [←hkeq] using hkone
  have htwo : dig 67 C (cyc n (cyc n t ((E/67)%n)) 2)≤1 := by simpa only [←hkeq] using hktwo
  have hclean := TemporalSafeCyclic.safe C n E t hn ht hC hzero hone htwo
  refine ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,htcase,hcarry,?_⟩
  exact hclean
#print axioms FixedGraphTemporalClean.graph_temporal_clean
end FixedGraphTemporalClean

import DiophantineConsistency.BFS943.FixedSourceBFSSupport
import DiophantineConsistency.Compact44.CleanSafeSource
import DiophantineConsistency.Compact44.CyclicAnyPhase
import DiophantineConsistency.Compact44.TemporalSafeCyclic
import DiophantineConsistency.Compact44.TemporalCarryExact

/-! FixedSource copy of `Trace75BFSCleanCarry`: the same proof with the 75 graph zero replaced by `BFS943FixedSource.FixedSource p v`.
A clean compact band column from an actual trace75 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FixedSourceBFSCleanCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry
open CompactPartialBandRotation CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten CompactHeterogeneousCarry CleanGeometry
open Trace75Factors Trace75Rank Trace75NaturalTransport
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_clean_carry (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : BFS943FixedSource.FixedSource p v) :
    ∃ N t : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      (67*8807)*N≤rankNat p v ∧ v 5=Exp.exp (rankNat p v-(67*8807)*N) ∧
      (t=4393 ∨ t=5495) ∧
      let n := 8807*N
      let T := temporalWord n (rankNat p v-67*n) (Cnat p v)
      let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
      let X := GenericBandCarryFamily.word n (Cnat p v) (bandOffsets position) T
      CarryInput 67 n (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧
      dig 67 T t=0 ∧ dig 67 T (cyc n t 1)≤Exp.exp 66 ∧
      carry 67 n a X (cyc n t 1)=0 ∧ dig 67 (v 1) t=raw 67 a X t := by
  obtain ⟨N,hN,hJ,hq,hle,hw,hcarry,_h0,hzero,hbool⟩ :=
    FixedSourceBFSSupport.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz
  let n : V := 8807*N
  let E : V := rankNat p v-67*n
  let T := temporalWord n E (Cnat p v)
  let A := fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V)
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8807:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8807)
    simpa only [n,mul_one] using h
  have hqexp : q p v=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : Cnat p v<Exp.exp (67*n) := by
    dsimp [Cnat]
    exact BandCarryInputs.source_word_bound (q p v) n (v 1) (v 2) hqexp (hv 1)
  let D : V := (E/67)%n
  let k1 := cyc n 4393 D
  let k2 := cyc n 5495 D
  have hp1 : k1%8807=cyc 8807 4393 D := by
    dsimp [k1,n]
    rw [CyclicAnyPhase.cyc_period 8807 N 4393 D (by norm_num) hN,
      mod_eq_self_of_lt (by norm_num : (4393:V)<8807)]
  have hp2 : k2%8807=cyc 8807 5495 D := by
    dsimp [k2,n]
    rw [CyclicAnyPhase.cyc_period 8807 N 5495 D (by norm_num) hN,
      mod_eq_self_of_lt (by norm_num : (5495:V)<8807)]
  obtain ⟨k,hcase,hkin,hkzero,hkone,hktwo⟩ :=
    CleanSafeSource.choose_source N (Cnat p v) D k1 k2 hN (cyc_lt hn _ _) (cyc_lt hn _ _) hp1 hp2 hzero hbool
  obtain ⟨t,htcase,hkeq⟩ : ∃ t : V, (t=4393 ∨ t=5495) ∧ k=cyc n t D := by
    rcases hcase with hk1 | hk2
    · exact ⟨4393,Or.inl rfl,hk1⟩
    · exact ⟨5495,Or.inr rfl,hk2⟩
  have ht : t<n := by
    rcases htcase with ht | ht <;> rw [ht] <;> exact lt_of_lt_of_le (by norm_num) hnge
  have hz0 : dig 67 (Cnat p v) (cyc n t D)=0 := by simpa only [←hkeq] using hkzero
  have hz1 : dig 67 (Cnat p v) (cyc n (cyc n t D) 1)≤1 := by simpa only [←hkeq] using hkone
  have hz2 : dig 67 (Cnat p v) (cyc n (cyc n t D) 2)≤1 := by simpa only [←hkeq] using hktwo
  obtain ⟨hTzero,hTpred⟩ := TemporalSafeCyclic.safe (Cnat p v) n E t hn ht hC hz0 hz1 hz2
  have hnat := DirectBFSModelMass.natural_mass
  have hm := congrArg (fun x : ℕ => (x:V)) hnat
  have hcoeff : (∑ j, A j)≤(DirectBFSCoefficientMass.stencilMass:V) := by
    have hc : (∑ j, A j)+1=(DirectBFSCoefficientMass.stencilMass:V) := by
      simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_sum] using hm
    rw [←hc]
    exact le_add_of_nonneg_right (by simp)
  have hroom : (∑ j, A j*3)+1<Exp.exp 66 := by
    have h3 : (∑ j, A j*3)≤3*(DirectBFSCoefficientMass.stencilMass:V) := by
      rw [←Finset.sum_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcoeff (by simp : (0:V)≤3)
    have hs : (∑ j, A j*3)+1≤3*(DirectBFSCoefficientMass.stencilMass:V)+1 := by
      simpa only [add_comm] using add_le_add_right h3 1
    exact lt_of_le_of_lt hs DirectBFSModelMass.stencil_below_half
  have hclean := TemporalCarryExact.clean_exact n (Cnat p v) T (v 1) A (bandOffsets position)
    hcarry t ht hroom hTzero hTpred
  exact ⟨N,t,hN,hJ,hq,hle,hw,htcase,hcarry,hTzero,hTpred,hclean.1,hclean.2⟩

#print axioms FixedSourceBFSCleanCarry.graph_clean_carry
end FixedSourceBFSCleanCarry

import DiophantineConsistency.Source34.Source34Source
import DiophantineConsistency.Mixed121.W121.TemporalSafeCyclic
import DiophantineConsistency.Mixed121.W121.TemporalCarryExact

/-! # A clean clause column at the source34 ports

`Mixed121CleanCarry` at the source34 tuple; both declarations are links of
the halting chain and are re-declared on `Source34Source.graph_safe_sources`.
The width-121 window lemmas (`W121.TemporalSafeCyclic.safe`,
`W121.TemporalCarryExact.clean_exact`) and the carry room
`Mixed121Flatten.aligned_room` are shared.

From `LeafFacts` at the source34 ports there is a clause target
`t ∈ {4393, 5495}` at which the temporal word is `0`, its predecessor digit is
at most `2^120`, the carry into `t + 1` is `0`, and the graph digit `F_t`
equals the raw band column at `t`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34CleanCarry
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open CompactHeterogeneousCarry CompactGenericAlignedMass Source34Rotation Source34Flatten
open Mixed121Rotation (coefficient word cap)
open Mixed121Flatten (selectors copies aligned_room)
attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_temporal_clean (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w t : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      (t=4393 ∨ t=5495) ∧
      CarryInput 121 (8801*N) (v 1) 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
        (coefficient (fun x => (alignedCoeff selectors copies x : V)))
        (word 121 (8801*N) C bandOffsets
          (Mixed121Temporal.temporalWord (8801*N) (R-121*(8801*N)) C)) ∧
      dig 121 (Mixed121Temporal.temporalWord (8801*N) (R-121*(8801*N)) C) t=0 ∧
      dig 121 (Mixed121Temporal.temporalWord (8801*N) (R-121*(8801*N)) C)
        (cyc (8801*N) t 1)≤Exp.exp 120 := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,hsources⟩ :=
    Source34Source.graph_safe_sources v hv hz
  dsimp only at *
  let p := Source34Ports.ports
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8801*N
  let E : V := R-121*n
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8801:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [n,mul_one] using h
  have hqexp : q=Exp.exp (121*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (121*n) := by
    dsimp [C]
    exact Mixed121Temporal.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  obtain ⟨k,hkcase,hkin,hkzero,hkone,hktwo⟩ := hsources ((E/121)%n)
  obtain ⟨t,htcase,hkeq⟩ : ∃ t : V, (t=4393 ∨ t=5495) ∧ k=cyc n t ((E/121)%n) := by
    rcases hkcase with hk1 | hk2
    · exact ⟨4393,Or.inl rfl,hk1⟩
    · exact ⟨5495,Or.inr rfl,hk2⟩
  have ht : t<n := by
    rcases htcase with ht | ht <;> rw [ht] <;> exact lt_of_lt_of_le (by norm_num) hnge
  have hzero : dig 121 C (cyc n t ((E/121)%n))=0 := by simpa only [←hkeq] using hkzero
  have hone : dig 121 C (cyc n (cyc n t ((E/121)%n)) 1)≤1 := by simpa only [←hkeq] using hkone
  have htwo : dig 121 C (cyc n (cyc n t ((E/121)%n)) 2)≤1 := by simpa only [←hkeq] using hktwo
  have hclean := W121.TemporalSafeCyclic.safe C n E t hn ht hC hzero hone htwo
  refine ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,htcase,hcarry,?_⟩
  exact hclean

theorem graph_clean_carry (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    ∃ N w t : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧ (t=4393 ∨ t=5495) ∧
      let T := Mixed121Temporal.temporalWord (8801*N) (R-121*(8801*N)) C
      let X := word 121 (8801*N) C bandOffsets T
      CarryInput 121 (8801*N) (v 1) 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121) a X ∧
      dig 121 T t=0 ∧ dig 121 T (cyc (8801*N) t 1)≤Exp.exp 120 ∧
      carry 121 (8801*N) a X (cyc (8801*N) t 1)=0 ∧
      dig 121 (v 1) t=raw 121 a X t := by
  obtain ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,htcase,hcarry,hTzero,hTpred⟩ :=
    graph_temporal_clean v hv hz
  dsimp only at *
  let n : V := 8801*N
  let A := fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V)
  have hnge : (8801:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [n,mul_one] using h
  have ht : t<n := by
    rcases htcase with ht | ht <;> rw [ht] <;> exact lt_of_lt_of_le (by norm_num) hnge
  have hclean := W121.TemporalCarryExact.clean_exact n _ _ (v 1) A bandOffsets hcarry t ht
    aligned_room hTzero hTpred
  exact ⟨N,w,t,hN,hq,hJ,hle,hw,hv5,htcase,hcarry,hTzero,hTpred,hclean.1,hclean.2⟩
end Source34CleanCarry
#print axioms Source34CleanCarry.graph_temporal_clean
#print axioms Source34CleanCarry.graph_clean_carry

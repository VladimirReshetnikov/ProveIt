import DiophantineConsistency.Mixed121.Mixed121Temporal
import DiophantineConsistency.Mixed121.Mixed121Flatten

/-! # The carry input of the 121x8801 band family

This module adds three results.

* `family_mass` is the mass hypothesis of the width-generic
  `Mixed121Rotation.carry_input` at `b = 1`. It follows from the carry room
  `3·mass + 1 < 2^120` (`Mixed121Flatten.aligned_room`).
* `carry_input` is the counterpart of Compact44's
  `CompactTwoBandCarry.carry_input`. The flattened family of the two rotated
  bands, the bare part and a temporal word `T` is a `CarryInput` at width `121`.
* `graph_carry` is the counterpart of
  `FixedGraphIndexedCarry.graph_carry_facts`. From `LeafFacts` at the
  121x8801 ports it gives that `CarryInput`, with `T` the temporal word of the
  native word `C`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Mixed121Carry
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open CompactHeterogeneousCarry CompactGenericAlignedMass Mixed121Rotation Mixed121Flatten
attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem family_mass :
    ((∑ i : Aligned (Fin 943) (Fin 44), (alignedCoeff selectors copies i : V)*3) +
      (Exp.exp 121-1))+1 ≤ (1+1)*(Exp.exp 121-1) := by
  have h := aligned_room (V:=V)
  generalize (∑ i : Aligned (Fin 943) (Fin 44), (alignedCoeff selectors copies i : V)*3) = S at h ⊢
  have he : Exp.exp (121:V) = 2*Exp.exp 120 := by
    simpa only [show (120:V)+1=121 by norm_num, mul_comm] using (exp_succ (120:V))
  obtain ⟨y, hy⟩ : ∃ y, Exp.exp (120:V) = y+1 :=
    ⟨Exp.exp 120 - 1, (tsub_add_cancel_of_le (one_le_exp _)).symm⟩
  have hsub : Exp.exp (121:V)-1 = 2*y+1 := by
    rw [he, hy, show (2:V)*(y+1) = (2*y+1)+1 by ring, add_tsub_cancel_right]
  rw [hy] at h
  have hS : S+1 ≤ y := lt_iff_succ_le.mp ((add_lt_add_iff_right (1:V)).mp h)
  rw [hsub]
  calc (S+(2*y+1))+1 = (S+1)+(2*y+1) := by ring
    _ ≤ y+(2*y+1) := add_le_add hS le_rfl
    _ ≤ (1+1)*(2*y+1) := by
        have hr : y+(2*y+1)+(y+1) = (1+1)*(2*y+1) := by ring
        rw [← hr]
        exact le_add_of_nonneg_right (by simp)

theorem carry_input (n C T F : V)
    (hn : 0<n) (hM : 0<Exp.exp (121*n)-1)
    (hC : C<Exp.exp (121*n)) (hCcap : ∀ k<n, dig 121 C k≤3)
    (hT : T<Exp.exp (121*n)) (hTcap : ∀ k<n, dig 121 T k≤Exp.exp 121-1)
    (hF : F<Exp.exp (121*n)-1)
    (hgraph : ((rotatedBand 4393 n C + rotatedBand 5495 n C + bareRotated n C)+T)
      % (Exp.exp (121*n)-1)=F) :
    CarryInput 121 n F 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
      (coefficient (fun x => (alignedCoeff selectors copies x : V)))
      (word 121 n C bandOffsets T) := by
  apply Mixed121Rotation.carry_input 121 n C T F 1
    (fun x : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies x : V))
    bandOffsets hn hM hC hCcap hT hTcap hF
  · simpa only [exact_bands] using hgraph
  · exact family_mass

theorem graph_carry (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      CarryInput 121 (8801*N) (v 1) 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
        (coefficient (fun x => (alignedCoeff selectors copies x : V)))
        (word 121 (8801*N) C bandOffsets
          (Mixed121Temporal.temporalWord (8801*N) (R-121*(8801*N)) C)) := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hgraph,hT,hTcap,_,hcap⟩ :=
    Mixed121Temporal.graph_temporal v hv hz
  dsimp only at *
  let p := Mixed121Ports.ports
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8801*N
  let T := Mixed121Temporal.temporalWord n (R-121*n) C
  have hn : 0<n := mul_pos (by norm_num) hN
  have hqexp : q=Exp.exp (121*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hmod : Exp.exp (121*n)-1=v 0*(p 0:V) := by
    rw [← hqexp]; dsimp [q]; rw [add_comm,add_tsub_cancel_right]
  have hM : 0<Exp.exp (121*n)-1 := by rw [hmod]; exact hpos
  have hF : v 1<Exp.exp (121*n)-1 := by rw [hmod]; exact hbound
  have hC : C<Exp.exp (121*n) := by
    dsimp [C]
    exact Mixed121Temporal.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  refine ⟨N,w,hN,hq,hJ,hle,hw,hv5,?_⟩
  exact carry_input n C T (v 1) hn hM hC hcap hT (fun k _ => hTcap k) hF hgraph
end Mixed121Carry
#print axioms Mixed121Carry.family_mass
#print axioms Mixed121Carry.carry_input
#print axioms Mixed121Carry.graph_carry

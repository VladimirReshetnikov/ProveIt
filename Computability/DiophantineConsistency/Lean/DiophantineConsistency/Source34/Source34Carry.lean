import DiophantineConsistency.Source34.Source34Temporal
import DiophantineConsistency.Source34.Source34Flatten
import DiophantineConsistency.Mixed121.Mixed121Carry

/-! # The carry input of the source34 band family

`Mixed121Carry` at the source34 tuple. The mass hypothesis
`Mixed121Carry.family_mass` depends only on the shared coefficient family and
is used directly. Re-declared:

* `carry_input`: the flattened family of the two rotated source34 bands, the
  source34 bare part and a temporal word `T` is a `CarryInput` at width `121`
  (the offsets are `Source34Flatten.bandOffsets`);
* `graph_carry`: from `LeafFacts` at the source34 ports, that `CarryInput`
  with `T` the temporal word of the native word `C`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Source34Carry
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open CompactHeterogeneousCarry CompactGenericAlignedMass Source34Rotation Source34Flatten
open Mixed121Rotation (coefficient word cap)
open Mixed121Flatten (selectors copies)
attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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
  · exact Mixed121Carry.family_mass

theorem graph_carry (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
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
    Source34Temporal.graph_temporal v hv hz
  dsimp only at *
  let p := Source34Ports.ports
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
end Source34Carry
#print axioms Source34Carry.carry_input
#print axioms Source34Carry.graph_carry

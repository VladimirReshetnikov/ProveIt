import DiophantineConsistency.Source34.Source34Clean
import DiophantineConsistency.Mixed121.Mixed121Source

/-! # Safe temporal sources at the source34 ports

`Mixed121Source` at the source34 tuple. Every lemma of `Mixed121Source` up to
`choose_source` is stated over the shared hull `Mixed121Clean.Bad`, the period
`8801` and the clause targets `4393, 5495` (which still differ by `1102`), so
they are used directly. Only the halting-chain link `graph_safe_sources` is
re-declared, on `Source34Clean.graph_support_carry`: for every temporal phase
`D`, one of the two clause targets gives a cell `k` with `C_k = 0` whose two
cyclic predecessors are Boolean. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34Source
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open ArithmeticStandardCasts
open CompactHeterogeneousCarry CompactGenericAlignedMass Source34Rotation Source34Flatten
open Mixed121Rotation (coefficient word cap)
open Mixed121Flatten (selectors copies)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho

theorem graph_safe_sources (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
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
          (Mixed121Temporal.temporalWord (8801*N) (R-121*(8801*N)) C)) ∧
      (∀ D : V, ∃ k, (k=cyc (8801*N) 4393 D ∨ k=cyc (8801*N) 5495 D) ∧
         k<8801*N ∧ dig 121 C k=0 ∧
         dig 121 C (cyc (8801*N) k 1)≤1 ∧ dig 121 C (cyc (8801*N) k 2)≤1) := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,h0,hzero,hbool⟩ :=
    Source34Clean.graph_support_carry v hv hz
  dsimp only at *
  refine ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,?_⟩
  intro D
  let k₁ := cyc (8801*N) 4393 D
  let k₂ := cyc (8801*N) 5495 D
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  have hp₁ : k₁%8801=cyc 8801 4393 D := by
    dsimp [k₁]
    rw [CyclicAnyPhase.cyc_period 8801 N 4393 D (by norm_num) hN,
      mod_eq_self_of_lt (by norm_num : (4393:V)<8801)]
  have hp₂ : k₂%8801=cyc 8801 5495 D := by
    dsimp [k₂]
    rw [CyclicAnyPhase.cyc_period 8801 N 5495 D (by norm_num) hN,
      mod_eq_self_of_lt (by norm_num : (5495:V)<8801)]
  exact Mixed121Source.choose_source N _ D k₁ k₂ hN (cyc_lt hn _ _) (cyc_lt hn _ _) hp₁ hp₂
    hzero hbool
end Source34Source
#print axioms Source34Source.graph_safe_sources

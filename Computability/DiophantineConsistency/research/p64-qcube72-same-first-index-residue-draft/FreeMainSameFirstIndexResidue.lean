import FreeMainFixedCompactIndexWindow

/-! Unchecked draft: first Pell residue for the actual extracted same index. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainSameFirstIndexResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticPellRecurrence ArithmeticPellCongruences
open FreeMainActualRankWindowCompact
attribute [local irreducible] CompactFixedBeta.betaNat CompactSymbolicPorts.lowNat
  CompactSymbolicPorts.highNat Nat.ofDigits CompactListMask.digits
  CompactConcreteMask.support CompactHighPopulation.highDigits CompactConcreteIncrement.mask
  compactPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_residue (P k n : V) (hP : 0<P)
    (hny : 2*ycoord n (2*(P-1)+1)=k) :
    ∃ s : V, k=2*n+4*P*s := by
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hB : 2*P ∣ 2*(P-1)+1+1 :=
    ⟨1, by calc
      2*(P-1)+1+1=2*(P-1+1) := by ring
      _=2*P*1 := by rw [hP1]; ring⟩
  obtain ⟨_,s,_,hys⟩ := residue_quotients n (2*(P-1)+1) (2*P) hB
  refine ⟨s,?_⟩
  rw [←hny,hys]
  ring

theorem fixed_window_residue (K : ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph
      (fun j => (compactPorts K j:ℤ))).output v) :
    let p := compactPorts K
    let q : V := (p 0:V)*v 0+1
    let Y := q*q*q*v 7
    let X := v 8*q
    let P := (X*Y)*Y
    let k := v 10+v 11
    let R := FreeMainAuxNorm.rank p v
    ∃ n s : V, n<R ∧ R<2*n ∧ xcoord n (2*(P-1)+1)=v 9 ∧
      2*ycoord n (2*(P-1)+1)=k ∧ k=2*n+4*P*s := by
  let p := compactPorts K
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let X : V := v 8*q
  let P : V := (X*Y)*Y
  let k : V := v 10+v 11
  let R : V := FreeMainAuxNorm.rank p v
  have hq : 0<q := by dsimp [q]; simp
  have hY : 0<Y := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 7)
  have hX : 0<X := mul_pos (hv 8) hq
  have hP : 0<P := mul_pos (mul_pos hX hY) hY
  obtain ⟨n,hn1,hn2,hnx,hny⟩ := FreeMainFixedCompactIndexWindow.first_index_window K v hv hz
  change n<R at hn1
  change R<2*n at hn2
  change xcoord n (2*(P-1)+1)=v 9 at hnx
  change 2*ycoord n (2*(P-1)+1)=k at hny
  obtain ⟨s,hs⟩ := first_residue P k n hP hny
  exact ⟨n,s,hn1,hn2,hnx,hny,hs⟩

#print axioms first_residue
#print axioms fixed_window_residue
end FreeMainSameFirstIndexResidue

import FreeMainFixedCompactFirstIndex
import FreeMainHalfIndexLower

/-! Unchecked draft: the first index lies strictly between half the main rank
and the rank at an actual fixed compact-port zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainFixedCompactIndexWindow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticPellRecurrence
open FreeMainActualRankWindowCompact FreeMainConditionalRank
attribute [local irreducible] CompactFixedBeta.betaNat CompactSymbolicPorts.lowNat
  CompactSymbolicPorts.highNat Nat.ofDigits CompactListMask.digits
  CompactConcreteMask.support CompactHighPopulation.highDigits CompactConcreteIncrement.mask
  compactPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_index_window (K : ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph
      (fun j => (compactPorts K j:ℤ))).output v) :
    let p := compactPorts K
    let q : V := (p 0:V)*v 0+1
    let Y := q*q*q*v 7
    let X := v 8*q
    let P := (X*Y)*Y
    let k := v 10+v 11
    let R := FreeMainAuxNorm.rank p v
    ∃ n : V, n<R ∧ R<2*n ∧
      xcoord n (2*(P-1)+1)=v 9 ∧ 2*ycoord n (2*(P-1)+1)=k := by
  let p := compactPorts K
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let X : V := v 8*q
  let P : V := (X*Y)*Y
  let k : V := v 10+v 11
  let R : V := FreeMainAuxNorm.rank p v
  obtain ⟨n,hnlt,hnx,hny⟩ := FreeMainFixedCompactFirstIndex.first_index_lt_rank K v hv hz
  change n<R at hnlt
  change xcoord n (2*(P-1)+1)=v 9 at hnx
  change 2*ycoord n (2*(P-1)+1)=k at hny
  obtain ⟨_,g,_,_,hmy⟩ := FreeMainFixedCompactRankedMain.fixed_main_at_rank K v hv hz
  change ycoord R (X*Y+Y)=(v 10+v 11)*Y+v 10 at hmy
  have htwice := FreeMainHalfIndexLower.main_lt_twice_first X Y (v 10) (v 11) n R (hv 11) hny hmy
  exact ⟨n,hnlt,htwice,hnx,hny⟩

#print axioms first_index_window
end FreeMainFixedCompactIndexWindow

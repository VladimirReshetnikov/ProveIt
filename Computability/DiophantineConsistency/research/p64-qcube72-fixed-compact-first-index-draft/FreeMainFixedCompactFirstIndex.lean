import FreeMainFixedCompactRankedMain
import FreeMainFirstIndexExtraction
import FreeMainFirstIndexComparison

/-! Unchecked draft: first index is below actual main rank at compact ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainFixedCompactFirstIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticPellRecurrence
open FreeMainActualRankWindowCompact FreeMainConditionalRank
attribute [local irreducible] CompactFixedBeta.betaNat CompactSymbolicPorts.lowNat
  CompactSymbolicPorts.highNat Nat.ofDigits CompactListMask.digits
  CompactConcreteMask.support CompactHighPopulation.highDigits CompactConcreteIncrement.mask
  compactPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_index_lt_rank (K : ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph
      (fun j => (compactPorts K j:ℤ))).output v) :
    let p := compactPorts K
    let q : V := (p 0:V)*v 0+1
    let Y := q*q*q*v 7
    let X := v 8*q
    let P := (X*Y)*Y
    let k := v 10+v 11
    ∃ n : V, n<FreeMainAuxNorm.rank p v ∧
      xcoord n (2*(P-1)+1)=v 9 ∧ 2*ycoord n (2*(P-1)+1)=k := by
  let p := compactPorts K
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let X : V := v 8*q
  let P : V := (X*Y)*Y
  let k : V := v 10+v 11
  let R : V := FreeMainAuxNorm.rank p v
  have hb := CompactSymbolicMaskData.data (V:=V)
  have hq33 : 33≤q := by
    dsimp only [q,p]
    rw [compactPorts_zero]
    exact FreeMainSymbolicPortRankedMain.q_lower (CompactFixedBeta.betaNat:V) (v 0)
      hb.2.2.2 (hv 0)
  have hq0 : 0<q := lt_of_lt_of_le (by norm_num) hq33
  have hq1 : 1≤q := le_trans (by norm_num) hq33
  have hY : 2≤Y := by
    dsimp [Y]
    calc (2:V)≤q := le_trans (by norm_num) hq33
      _≤q*q := le_mul_of_one_le_right (Arithmetic.zero_le _) hq1
      _≤q*q*q := le_mul_of_one_le_right (Arithmetic.zero_le _) hq1
      _≤q*q*q*v 7 := le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp (hv 7))
  have hX : 0<X := mul_pos (hv 8) hq0
  obtain ⟨n,_,hnx,hny⟩ := FreeMainFirstIndexExtraction.first_index p v hv hz
  change xcoord n (2*(P-1)+1)=v 9 at hnx
  change 2*ycoord n (2*(P-1)+1)=k at hny
  obtain ⟨_,g,_,_,hmy⟩ := FreeMainFixedCompactRankedMain.fixed_main_at_rank K v hv hz
  change ycoord R (X*Y+Y)=k*Y+v 10 at hmy
  have hlt := FreeMainFirstIndexComparison.first_lt_main X Y k (v 10) n R hX hY (hv 10) hny hmy
  exact ⟨n,hlt,hnx,hny⟩

#print axioms first_index_lt_rank
end FreeMainFixedCompactFirstIndex

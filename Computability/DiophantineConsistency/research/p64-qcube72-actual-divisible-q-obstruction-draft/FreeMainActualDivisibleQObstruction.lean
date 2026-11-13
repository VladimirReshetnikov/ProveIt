import FreeMainFixedCompactCarrierCancel
import FreeMainDivisibleQObstruction
import FreeMainGraphMainRoot

/-! Unchecked draft: actual 72 zero with 3|q has non-divisible carrier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainActualDivisibleQObstruction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticPellRecurrence
open FreeMainActualRankWindowCompact
attribute [local irreducible] CompactFixedBeta.betaNat CompactSymbolicPorts.lowNat
  CompactSymbolicPorts.highNat Nat.ofDigits CompactListMask.digits
  CompactConcreteMask.support CompactHighPopulation.highDigits CompactConcreteIncrement.mask
  compactPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem actual_zero (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v)
    (h3 : (3:V)∣(p 0:V)*v 0+1) :
    let q : V := (p 0:V)*v 0+1
    let Y := q*q*q*v 7
    ¬(Y*Y∣v 13) := by
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let X : V := v 8*q
  let a : V := X*Y+Y
  let c : V := (v 10+v 11)*Y+v 10
  let U : V := Y*Y
  have hq : 0<q := by dsimp [q]; simp
  have hY : 0<Y := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 7)
  have hU : 0<U := mul_pos hY hY
  obtain ⟨g,m,hg,hcar,_,_⟩ := FreeMainGraphMainRoot.main_index p v hv hz
  change g*g=1+delta a*c*c at hg
  change U*g=U*(X+a*c)+(4*a+3)*v 13 at hcar
  exact FreeMainDivisibleQObstruction.not_dvd q (v 8) (v 7) U g c (v 13) h3 hU hg hcar

theorem fixed_zero (K : ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph
      (fun j => (compactPorts K j:ℤ))).output v)
    (h3 : (3:V)∣(compactPorts K 0:V)*v 0+1) :
    let q : V := (compactPorts K 0:V)*v 0+1
    let Y := q*q*q*v 7
    ¬(Y*Y∣v 13) :=
  actual_zero (compactPorts K) v hv hz h3

#print axioms actual_zero
#print axioms fixed_zero
end FreeMainActualDivisibleQObstruction

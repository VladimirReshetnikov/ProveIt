import FreeMainConditionalOldCarrier
import FreeMainActualDivisibleQObstruction

/-! Unchecked draft: no same-witness old carrier at fixed compact zeros with 3|q. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainDivisibleQNoOldGamma
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open FreeMainActualRankWindowCompact
attribute [local irreducible] CompactFixedBeta.betaNat CompactSymbolicPorts.lowNat
  CompactSymbolicPorts.highNat Nat.ofDigits CompactListMask.digits
  CompactConcreteMask.support CompactHighPopulation.highDigits CompactConcreteIncrement.mask
  compactPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem carrier_forces_dvd (U X R n k h gamma s : V) (hU : 0<U)
    (hn : 2*n=R+1) (hks : k=2*n+4*(X*U)*s)
    (hold : h+k=U*gamma+(R+1)) : U∣h := by
  have he : h+U*(4*X*s)=U*gamma := by
    apply add_right_cancel (b := R+1)
    calc
      (h+U*(4*X*s))+(R+1)=h+(2*n+4*(X*U)*s) := by rw [hn]; ring
      _=h+k := by rw [hks]
      _=U*gamma+(R+1) := hold
  apply mod_eq_zero_iff_dvd.mp
  have hh := congrArg (fun z : V => z%U) he
  rw [show U*gamma=0+U*gamma by simp,
    mod_add_mul' _ _ hU,mod_add_mul' _ _ hU] at hh
  simpa using hh

theorem fixed_no_gamma (K : ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph
      (fun j => (compactPorts K j:ℤ))).output v)
    (h3 : (3:V)∣(compactPorts K 0:V)*v 0+1) :
    let p := compactPorts K
    let q : V := (p 0:V)*v 0+1
    let Y := q*q*q*v 7
    let k := v 10+v 11
    let R := FreeMainAuxNorm.rank p v
    ¬ ∃ gamma : V, v 13+k=(Y*Y)*gamma+(R+1) := by
  let p := compactPorts K
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let X : V := v 8*q
  let P : V := (X*Y)*Y
  let k : V := v 10+v 11
  let R : V := FreeMainAuxNorm.rank p v
  have hq : 0<q := by dsimp [q]; simp
  have hY : 0<Y := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 7)
  have hU : 0<Y*Y := mul_pos hY hY
  have hnot := FreeMainActualDivisibleQObstruction.fixed_zero K v hv hz h3
  change ¬(Y*Y∣v 13) at hnot
  rintro ⟨gamma,hold⟩
  change v 13+k=(Y*Y)*gamma+(R+1) at hold
  obtain ⟨n,s,_,_,_,_,hks,hn⟩ := FreeMainConditionalOldCarrier.fixed_of_witness K v gamma hv hz hold
  change k=2*n+4*P*s at hks
  change 2*n=R+1 at hn
  have hks' : k=2*n+4*(X*(Y*Y))*s := by simpa only [P,mul_assoc] using hks
  exact hnot (carrier_forces_dvd (Y*Y) X R n k (v 13) gamma s hU hn hks' hold)

#print axioms carrier_forces_dvd
#print axioms fixed_no_gamma
end FreeMainDivisibleQNoOldGamma

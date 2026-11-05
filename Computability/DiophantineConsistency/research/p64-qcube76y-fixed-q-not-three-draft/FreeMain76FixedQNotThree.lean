import P64QCube72FreeForward
import FreeMainDivisibleQNoOldGamma

/-! Unchecked draft: a fixed compact 76Y zero has q not divisible by 3. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMain76FixedQNotThree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap FreeMainActualRankWindowCompact
attribute [local irreducible] CompactFixedBeta.betaNat CompactSymbolicPorts.lowNat
  CompactSymbolicPorts.highNat Nat.ofDigits CompactListMask.digits
  CompactConcreteMask.support CompactHighPopulation.highDigits CompactConcreteIncrement.mask
  compactPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fixed_q_not_divisible (K : ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube76Y.graph
      (fun j => (compactPorts K j:ℤ))).output v) :
    ¬ ((3:V)∣(compactPorts K 0:V)*v 0+1) := by
  let p := compactPorts K
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let w := lift p v
  let zw : Fin 14 → DiffRing V := fun i => ι (w i)
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let k : V := v 10+v 11
  let R : V := FreeMainAuxNorm.rank p v
  obtain ⟨h,hpos,hh⟩ := FreeMainGraphForward.exists_positive_main_gap p v hv hz
  let u := Function.update v 13 h
  have hup : ∀ i,0<u i := by
    intro i
    by_cases hi : i=13
    · subst i; simpa [u] using hpos
    · simpa [u,hi] using hv i
  have hgap : (ι h:DiffRing V)=P64QCube72FreeBinding.gap pp z := by
    dsimp [P64QCube72FreeBinding.gap,pp,z]
    rw [←P64QCubeMap.lift_cast p v]
    simpa [P64QCubeMap.lift] using hh
  have hcast : (fun i => (ι (u i):DiffRing V))=P64QCube72FreeBinding.liftRing pp z := by
    funext i
    by_cases hi : i=13
    · subst i; simpa [u,P64QCube72FreeBinding.liftRing] using hgap
    · simp [u,P64QCube72FreeBinding.liftRing,hi,z]
  have hz72 : InternalZero (P64QCube72Free.graph pp).output u := by
    rw [internalZero_iff] at hz ⊢
    change (P64QCube72Free.graph pp).output.evalRing (fun i => ι (u i))=0
    rw [hcast,P64QCube72FreeBinding.output]
    exact hz
  obtain ⟨_,_,_,_,hlt⟩ := IndependentYGraphDraft.residuals p v hv hz
  have hlt' : InternalZero (P64Graph.graph pp).Lt w := by
    rw [internalZero_iff]
    change (P64QCube76Y.graph pp).Lt.evalRing z=0 at hlt
    rw [IndependentYGraphDraft.transport_same pp,P64QCube78GraphSplit.transport_same pp,
      ←P64QCubeBinding.transport pp z,←P64QCubeMap.lift_cast p v] at hlt
    exact hlt
  have hwp := P64QCubeMap.lift_pos p v hv
  have hF : w 1≤(p 0:V)*w 0+1 := by
    have hg := (P64Root.transport p w hwp hlt').1
    exact le_trans (by simp) (le_of_lt hg)
  change (ι h:DiffRing V)=(P64Graph.vals pp zw).U*zw 13-
    (((P64Graph.vals pp zw).k-(P64Graph.vals pp zw).RR)-1) at hh
  rw [P64Root.c_U,P64Root.c_k,P64Root.c_RR p w hF] at hh
  have hh' : (ι h:DiffRing V)=(ι (Y*Y))*ι (v 13)-((ι k-ι R)-1) := by
    simpa [w,zw,lift,q,Y,k,R,FreeMainAuxNorm.rank] using hh
  have hold : h+k=(Y*Y)*v 13+(R+1) := by
    apply ι_injective
    simp only [map_add,map_mul,map_one]
    simp only [map_mul] at hh'
    linear_combination hh'
  have hold_u : u 13+(u 10+u 11)=
      (((p 0:V)*u 0+1)*((p 0:V)*u 0+1)*((p 0:V)*u 0+1)*u 7)*
      (((p 0:V)*u 0+1)*((p 0:V)*u 0+1)*((p 0:V)*u 0+1)*u 7)*v 13+
      (FreeMainAuxNorm.rank p u+1) := by
    simpa [u,R,FreeMainAuxNorm.rank,q,Y,k] using hold
  intro h3
  have h3u : (3:V)∣(compactPorts K 0:V)*u 0+1 := by simpa [u,p] using h3
  have hno := FreeMainDivisibleQNoOldGamma.fixed_no_gamma K u hup hz72 h3u
  exact hno ⟨v 13,hold_u⟩

#print axioms fixed_q_not_divisible
end FreeMain76FixedQNotThree

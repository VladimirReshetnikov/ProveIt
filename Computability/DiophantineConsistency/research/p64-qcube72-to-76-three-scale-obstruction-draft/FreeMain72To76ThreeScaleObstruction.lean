import P64QCube72FreeForward
import FreeMainTwoZeroScaleObstruction
import FreeMainActualFirstOrdinateUnique

/-! Unchecked draft: no equal-scale 76Y target for a 72 zero with 3|q. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMain72To76ThreeScaleObstruction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap FreeMainActualRankWindowCompact FreeMainConditionalRank
attribute [local irreducible] CompactFixedBeta.betaNat CompactSymbolicPorts.lowNat
  CompactSymbolicPorts.highNat Nat.ofDigits CompactListMask.digits
  CompactConcreteMask.support CompactHighPopulation.highDigits CompactConcreteIncrement.mask
  compactPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem no_fixed_scale_target (K : ℕ) (src v : Fin 14 → V)
    (hsrc : ∀ i,0<src i) (hv : ∀ i,0<v i)
    (hzsrc : InternalZero (P64QCube72Free.graph
      (fun j => (compactPorts K j:ℤ))).output src)
    (hz : InternalZero (P64QCube76Y.graph
      (fun j => (compactPorts K j:ℤ))).output v)
    (h3 : (3:V)∣(compactPorts K 0:V)*src 0+1)
    (hX : src 8*qval (compactPorts K) src=v 8*qval (compactPorts K) v)
    (hY : yval (compactPorts K) src=yval (compactPorts K) v)
    (hc : cval (compactPorts K) src=cval (compactPorts K) v) : False := by
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
  have hXu : src 8*qval p src=u 8*qval p u := by simpa [u,qval] using hX
  have hYu : yval p src=yval p u := by simpa [u,yval,qval] using hY
  have hcu : cval p src=cval p u := by simpa [u,cval,yval,qval] using hc
  have hku : src 10+src 11=u 10+u 11 :=
    FreeMainActualFirstOrdinateUnique.same_k p src u hsrc hup hzsrc hz72 hXu hYu hcu
  have hno := FreeMainTwoZeroScaleObstruction.two_zero_no_old_gamma K src u
    hsrc hup hzsrc hz72 h3 hXu hYu hcu hku
  exact hno ⟨v 13,hold_u⟩

#print axioms no_fixed_scale_target
end FreeMain72To76ThreeScaleObstruction

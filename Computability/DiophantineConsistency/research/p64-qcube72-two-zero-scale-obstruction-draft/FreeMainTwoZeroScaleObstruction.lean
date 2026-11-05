import FreeMainScaleRigidity
import FreeMainDivisibleQNoOldGamma

/-! Unchecked draft: equal-scale fixed-port 72 zeros cannot have an old carrier
on the second valuation when the first has 3|q. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainTwoZeroScaleObstruction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticPellRecurrence ArithmeticPellCongruences
open FreeMainActualRankWindowCompact FreeMainConditionalRank
attribute [local irreducible] CompactFixedBeta.betaNat CompactSymbolicPorts.lowNat
  CompactSymbolicPorts.highNat Nat.ofDigits CompactListMask.digits
  CompactConcreteMask.support CompactHighPopulation.highDigits CompactConcreteIncrement.mask
  compactPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem two_zero_no_old_gamma (K : ℕ) (v w : Fin 14 → V)
    (hv : ∀ i,0<v i) (hw : ∀ i,0<w i)
    (hzv : InternalZero (P64QCube72Free.graph
      (fun j => (compactPorts K j:ℤ))).output v)
    (hzw : InternalZero (P64QCube72Free.graph
      (fun j => (compactPorts K j:ℤ))).output w)
    (h3 : (3:V)∣(compactPorts K 0:V)*v 0+1)
    (hX : v 8*qval (compactPorts K) v=w 8*qval (compactPorts K) w)
    (hY : yval (compactPorts K) v=yval (compactPorts K) w)
    (hc : cval (compactPorts K) v=cval (compactPorts K) w)
    (hk : v 10+v 11=w 10+w 11) :
    let p := compactPorts K
    let Y := yval p w
    let R := FreeMainAuxNorm.rank p w
    ¬ ∃ gamma : V, w 13+(w 10+w 11)=(Y*Y)*gamma+(R+1) := by
  let p := compactPorts K
  let X : V := v 8*qval p v
  let Y : V := yval p v
  let a : V := aval p v
  let c : V := cval p v
  let R : V := FreeMainAuxNorm.rank p v
  let R' : V := FreeMainAuxNorm.rank p w
  have ha : aval p v=aval p w := by dsimp [aval]; rw [hX,hY]
  obtain ⟨g,m,_,hcar,hx,hy⟩ := FreeMainGraphMainRoot.main_index p v hv hzv
  change (Y*Y)*g=(Y*Y)*(X+a*c)+(4*a+3)*v 13 at hcar
  change xcoord m a=g at hx
  change ycoord m a=c at hy
  obtain ⟨g',m',_,hcar',hx',hy'⟩ := FreeMainGraphMainRoot.main_index p w hw hzw
  change (yval p w*yval p w)*g'=(yval p w*yval p w)*
    (w 8*qval p w+aval p w*cval p w)+(4*aval p w+3)*w 13 at hcar'
  change xcoord m' (aval p w)=g' at hx'
  change ycoord m' (aval p w)=cval p w at hy'
  rw [←hY,←hX,←ha,←hc] at hcar'
  rw [←ha] at hx'
  rw [←ha,←hc] at hy'
  change (Y*Y)*g'=(Y*Y)*(X+a*c)+(4*a+3)*w 13 at hcar'
  change xcoord m' a=g' at hx'
  change ycoord m' a=c at hy' 
  obtain ⟨_,_,hh⟩ := FreeMainScaleRigidity.same_rank_root_carrier
    a X Y c m m' g g' (v 13) (w 13) hy hy' hx hx' hcar hcar'
  obtain ⟨_,_,_,_,hyR⟩ := FreeMainFixedCompactRankedMain.fixed_main_at_rank K v hv hzv
  change ycoord R a=c at hyR
  obtain ⟨_,_,_,_,hyR'⟩ := FreeMainFixedCompactRankedMain.fixed_main_at_rank K w hw hzw
  change ycoord R' (aval p w)=cval p w at hyR'
  rw [←ha,←hc] at hyR'
  change ycoord R' a=c at hyR'
  have hRR : R=R' := (y_strictMono a).injective (hyR.trans hyR'.symm)
  have hno := FreeMainDivisibleQNoOldGamma.fixed_no_gamma K v hv hzv h3
  change ¬ ∃ gamma : V, w 13+(w 10+w 11)=(yval p w*yval p w)*gamma+(R'+1)
  rintro ⟨gamma,hold⟩
  change ¬ ∃ gamma : V, v 13+(v 10+v 11)=(Y*Y)*gamma+(R+1) at hno
  apply hno
  refine ⟨gamma,?_⟩
  change w 13+(w 10+w 11)=(yval p w*yval p w)*gamma+(R'+1) at hold
  rw [←hh,←hk,←hY,←hRR] at hold
  exact hold

#print axioms two_zero_no_old_gamma
end FreeMainTwoZeroScaleObstruction

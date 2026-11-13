import FreeMainFixedCompactCarrierCancel
import DiophantineConsistency.Compact44.P72Exact

/-! Unchecked draft: a supplied old carrier witness forces the first index. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainConditionalOldCarrier
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open FreeMainActualRankWindowCompact
attribute [local irreducible] CompactFixedBeta.betaNat CompactSymbolicPorts.lowNat
  CompactSymbolicPorts.highNat Nat.ofDigits CompactListMask.digits
  CompactConcreteMask.support CompactHighPopulation.highDigits CompactConcreteIncrement.mask
  compactPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem index_eq_of_witness (U X R n k h gamma e mu s : V)
    (hn : n<R) (hRmu : R+1<mu) (hmu : 0<mu)
    (hU : U=e*mu) (hdiv : mu∣h) (hks : k=2*n+4*(X*U)*s)
    (hold : h+k=U*gamma+(R+1)) : 2*n=R+1 := by
  obtain ⟨t,ht⟩ := hdiv
  have heq : 2*n+mu*(t+4*X*e*s)=(R+1)+mu*(e*gamma) := by
    calc
      2*n+mu*(t+4*X*e*s)=mu*t+(2*n+4*(X*(e*mu))*s) := by ring
      _=h+k := by rw [ht,hks,hU]
      _=U*gamma+(R+1) := hold
      _=(R+1)+mu*(e*gamma) := by rw [hU]; ring
  have hmod : (2*n)%mu=R+1 := by
    have hh := congrArg (fun z : V => z%mu) heq
    rw [mod_add_mul' _ _ hmu,mod_add_mul' _ _ hmu,mod_eq_self_of_lt hRmu] at hh
    exact hh
  exact P72Exact.index_close R n mu R hRmu hmod hn rfl

theorem fixed_of_witness (K : ℕ) (v : Fin 14 → V) (gamma : V)
    (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph
      (fun j => (compactPorts K j:ℤ))).output v)
    (hold : let p := compactPorts K
      let q : V := (p 0:V)*v 0+1
      let Y := q*q*q*v 7
      v 13+(v 10+v 11)=(Y*Y)*gamma+(FreeMainAuxNorm.rank p v+1)) :
    let p := compactPorts K
    let q : V := (p 0:V)*v 0+1
    let Y := q*q*q*v 7
    let X := v 8*q
    let P := (X*Y)*Y
    let k := v 10+v 11
    let R := FreeMainAuxNorm.rank p v
    ∃ n s : V, n<R ∧ R<2*n ∧ xcoord n (2*(P-1)+1)=v 9 ∧
      2*ycoord n (2*(P-1)+1)=k ∧ k=2*n+4*P*s ∧ 2*n=R+1 := by
  let p := compactPorts K
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let X : V := v 8*q
  let P : V := (X*Y)*Y
  let k : V := v 10+v 11
  let R : V := FreeMainAuxNorm.rank p v
  obtain ⟨n,s,e,mu,hn,hn2,hnx,hny,hks,_,hU,_,hmu,hbound,hdiv⟩ :=
    FreeMainFixedCompactCarrierCancel.fixed_data K v hv hz
  change n<R at hn
  change R<2*n at hn2
  change xcoord n (2*(P-1)+1)=v 9 at hnx
  change 2*ycoord n (2*(P-1)+1)=k at hny
  change k=2*n+4*P*s at hks
  change Y*Y=e*mu at hU
  change q*(q*(q*q))≤mu at hbound
  change v 13+k=(Y*Y)*gamma+(R+1) at hold
  have hwindow := (FreeMainFixedCompactRankedMain.fixed_main_at_rank K v hv hz).1.2
  change (ι R:DiffRing V)+1<(ι q)*(ι q*((ι q)*(ι q))) at hwindow
  have hbound' : (ι q:DiffRing V)*(ι q)*((ι q)*(ι q))≤ι mu := by
    have hh := (ι_le_ι (V:=V)).mpr hbound
    simpa only [map_mul,mul_assoc] using hh
  have hRmu : R+1<mu := by
    apply (ι_lt_ι (V:=V)).mp
    simp only [map_add,map_one]
    exact lt_of_lt_of_le hwindow (by simpa only [mul_assoc] using hbound')
  have hks' : k=2*n+4*(X*(Y*Y))*s := by simpa only [P,mul_assoc] using hks
  have heq := index_eq_of_witness (Y*Y) X R n k (v 13) gamma e mu s
    hn hRmu hmu hU hdiv hks' hold
  exact ⟨n,s,hn,hn2,hnx,hny,hks,heq⟩

#print axioms index_eq_of_witness
#print axioms fixed_of_witness
end FreeMainConditionalOldCarrier

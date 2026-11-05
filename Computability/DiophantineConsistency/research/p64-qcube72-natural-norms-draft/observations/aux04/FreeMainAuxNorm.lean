import FreeMainStrongNorm
import IndependentYStrictDraft

/-! Unchecked draft: natural independent-y auxiliary norm at the graph rank. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainAuxNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap ArithmeticPellRecurrence ArithmeticPellHalfIndex
open IndependentYStrictDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def rank (p : Fin 4 → ℕ) (v : Fin 14 → V) : V :=
  let q : V := (p 0:V)*v 0+1
  ((p 0:V)*v 0*(q-v 1)+v 2)*(q*q-1)+((p 2:V)+q*(p 3:V))*v 0

theorem auxiliary_same (p : Fin 4 → ℤ) : (P64QCube72Free.graph p).Na=(P64QCube76Y.graph p).Na := by rfl

theorem auxiliary (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v) :
    let q : V := (p 0:V)*v 0+1
    let Y := q*q*q*v 7
    let c := (v 10+v 11)*Y+v 10
    let R := rank p v
    let z := absdiff ((v 4*v 4)*(v 6*c)) ((v 4*v 4)*R+c)
    (v 5*c*c)*(v 5*c*c)*z*z+v 12*v 12 =
      1+(v 5*c*c)*(v 5*c*c)*v 12*v 12 := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let w : Fin 14 → V := lift p v
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let X : V := v 8*q
  let a : V := X*Y+Y
  let c : V := (v 10+v 11)*Y+v 10
  let R : V := rank p v
  let I : V := v 5*c*c
  let L : V := (v 4*v 4)*(v 6*c)
  let N : V := (v 4*v 4)*R+c
  obtain ⟨_,_,_,hna,hlt⟩ := FreeMainGraphResiduals.residuals p v hv hz
  have hlt' : InternalZero (P64Graph.graph pp).Lt w := by
    rw [internalZero_iff]
    change (P64QCube72Free.graph pp).Lt.evalRing z=0 at hlt
    rw [FreeMainGraphResiduals.transport_same pp,P64QCube78GraphSplit.transport_same pp,
      ←P64QCubeBinding.transport pp z,←P64QCubeMap.lift_cast p v] at hlt
    exact hlt
  have hwp := P64QCubeMap.lift_pos p v hv
  have hgap := (P64Root.transport p w hwp hlt').1
  have hF : w 1≤(p 0:V)*w 0+1 := le_trans (by simp) (le_of_lt hgap)
  have hrank : rankValue pp z = ι R := by
    have he : rankValue pp z=(P64Graph.vals pp (P64QCubeMap.liftRing pp z)).RR := by
      simp [rankValue,P64Graph.vals,P64QCubeMap.liftRing]
    rw [he,←P64QCubeMap.lift_cast p v]
    simpa [w,lift,R,rank,q] using P64Root.c_RR p w hF
  have hc : cValue pp z = ι c := by simp [cValue,pp,z,q,Y,c]
  have ha : aValue pp z = ι a := by simp [aValue,pp,z,q,Y,X,a]
  have hdelta : deltaValue pp z = ι (delta a) := by
    dsimp [deltaValue]
    rw [ha]
    simp [delta,map_add,map_mul,map_ofNat]
    ring
  have hV : P64QCube76YBinding.oldV pp z = ι L-ι N := by
    rw [oldV_decomposition]
    dsimp [termValue]
    rw [hc,hrank]
    simp only [z,L,N,map_add,map_mul]
    ring
  have hs := FreeMainStrongNorm.strong p v hv hz
  change I*I+delta a=delta a*(v 4*v 4) at hs
  have hI : (ι I:DiffRing V)*(ι I)=ι (delta a)*(z 4*z 4-1) := by
    have hh := congrArg (fun t : V => (ι t:DiffRing V)) hs
    simp only [map_add,map_mul] at hh
    change (ι I:DiffRing V)*(ι I)+ι (delta a)=ι (delta a)*(z 4*z 4) at hh
    linear_combination hh
  change (P64QCube72Free.graph pp).Na.evalRing z=1 at hna
  rw [auxiliary_same pp,auxiliary_eval pp z,hdelta,←hI,hV] at hna
  change I*I*(absdiff L N)*(absdiff L N)+v 12*v 12 =
    1+I*I*v 12*v 12
  apply ι_injective
  simp only [map_add,map_mul,map_one]
  rw [show (ι I:DiffRing V)*(ι I)*ι (absdiff L N)*ι (absdiff L N) =
      (ι I)*(ι I)*(ι (absdiff L N)*ι (absdiff L N)) by ring]
  rw [P72Aux.ι_absdiff_sq]
  change (ι I:DiffRing V)*(ι I)*((ι L-ι N)*(ι L-ι N))+z 12*z 12 =
    1+(ι I)*(ι I)*z 12*z 12
  linear_combination hna

#print axioms FreeMainAuxNorm.auxiliary_same
#print axioms FreeMainAuxNorm.auxiliary
end FreeMainAuxNorm

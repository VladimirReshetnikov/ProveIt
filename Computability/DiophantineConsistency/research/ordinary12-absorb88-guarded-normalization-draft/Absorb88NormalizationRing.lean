import Absorb88First
import Mathlib.Tactic.LinearCombination

/-! Draft: ring identities for a guarded negative-transport normalization. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88NormalizationRing
open DiophantineConsistency FreeJAbsorb88 Absorb88First
variable {R : Type*} [CommRing R]

def normalize (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) : Fin 12 → R :=
  let b := v 0*(p 0:R)
  let q := 1+b
  let k := v 8+v 9
  let A := (p 1:R)+v 5
  let D := q*(q*A+1)
  Function.update (Function.update (Function.update v 1 (v 1-b*j)) 2 (v 2-b*b*j)) 7
    (first+(1+k*b)*(D*j-u))

@[simp] theorem norm_0 (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) : normalize p v j u first 0=v 0 := by simp [normalize]
@[simp] theorem norm_1 (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) : normalize p v j u first 1=v 1-(v 0*(p 0:R))*j := by simp [normalize]
@[simp] theorem norm_2 (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) : normalize p v j u first 2=v 2-(v 0*(p 0:R))*(v 0*(p 0:R))*j := by simp [normalize]
@[simp] theorem norm_3 (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) : normalize p v j u first 3=v 3 := by simp [normalize]
@[simp] theorem norm_4 (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) : normalize p v j u first 4=v 4 := by simp [normalize]
@[simp] theorem norm_5 (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) : normalize p v j u first 5=v 5 := by simp [normalize]
@[simp] theorem norm_6 (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) : normalize p v j u first 6=v 6 := by simp [normalize]
@[simp] theorem norm_7 (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) : normalize p v j u first 7=first+(1+(v 8+v 9)*(v 0*(p 0:R)))*((1+v 0*(p 0:R))*((1+v 0*(p 0:R))*((p 1:R)+v 5)+1)*j-u) := by simp [normalize]
@[simp] theorem norm_8 (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) : normalize p v j u first 8=v 8 := by simp [normalize]
@[simp] theorem norm_9 (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) : normalize p v j u first 9=v 9 := by simp [normalize]
@[simp] theorem norm_10 (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) : normalize p v j u first 10=v 10 := by simp [normalize]
@[simp] theorem norm_11 (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) : normalize p v j u first 11=v 11 := by simp [normalize]

theorem main_invariant (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) :
    (graph p).main.evalRing (normalize p v j u first)=(graph p).main.evalRing v := by
  simp only [graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    Int.cast_one,Int.cast_ofNat,Nat.cast_one,Nat.cast_ofNat,
    norm_0,norm_1,norm_2,norm_3,norm_4,norm_5,norm_6,norm_7,norm_8,norm_9,norm_10,norm_11]
  have hG : v 2-(v 0*(p 0:R))*(v 0*(p 0:R))*j +
      ((1+v 0*(p 0:R))-(v 1-(v 0*(p 0:R))*j))*(v 0*(p 0:R)) =
      v 2+((1+v 0*(p 0:R))-v 1)*(v 0*(p 0:R)) := by ring
  rw [hG]

theorem ordinary_invariant (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) :
    (graph p).ordinary.evalRing (normalize p v j u first)=(graph p).ordinary.evalRing v := by
  simp only [graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    Int.cast_one,Int.cast_ofNat,Nat.cast_one,Nat.cast_ofNat,
    norm_0,norm_1,norm_2,norm_3,norm_4,norm_5,norm_6,norm_7,norm_8,norm_9,norm_10,norm_11]
  have hG : v 2-(v 0*(p 0:R))*(v 0*(p 0:R))*j +
      ((1+v 0*(p 0:R))-(v 1-(v 0*(p 0:R))*j))*(v 0*(p 0:R)) =
      v 2+((1+v 0*(p 0:R))-v 1)*(v 0*(p 0:R)) := by ring
  rw [hG]

theorem first_root (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R)
    (htransport : let b := v 0*(p 0:R); let q := 1+b; let A := (p 1:R)+v 5
      q*((q-v 1-v 2)*A-v 1) = -b*u) :
    (firstParts p).1.evalRing (normalize p v j u first)=(v 0*(p 0:R))*first := by
  let b := v 0*(p 0:R)
  let q := 1+b
  let A := (p 1:R)+v 5
  let D := q*(q*A+1)
  change q*((q-v 1-v 2)*A-v 1) = -b*u at htransport
  have hnew : q*((q-(v 1-b*j)-(v 2-b*b*j))*A-(v 1-b*j))=b*(D*j-u) := by
    calc
      _=q*((q-v 1-v 2)*A-v 1)+b*D*j := by dsimp [D,q]; ring
      _=b*(D*j-u) := by rw [htransport]; ring
  simp only [firstParts,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    Int.cast_one,Int.cast_ofNat,Nat.cast_one,Nat.cast_ofNat,
    norm_0,norm_1,norm_2,norm_3,norm_4,norm_5,norm_6,norm_7,norm_8,norm_9,norm_10,norm_11]
  change b*((first+(1+(v 8+v 9)*b)*(D*j-u))-
    (v 8+v 9)*(q*((q-(v 1-b*j)-(v 2-b*b*j))*A-(v 1-b*j))))-
      q*((q-(v 1-b*j)-(v 2-b*b*j))*A-(v 1-b*j))=b*first
  rw [hnew]
  ring

theorem new_transport (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R)
    (htransport : let b := v 0*(p 0:R); let q := 1+b; let A := (p 1:R)+v 5
      q*((q-v 1-v 2)*A-v 1) = -b*u) :
    let w := normalize p v j u first
    let b := v 0*(p 0:R)
    let q := 1+b
    let A := (p 1:R)+v 5
    let D := q*(q*A+1)
    q*((q-w 1-w 2)*A-w 1)=b*(D*j-u) := by
  dsimp only
  simp only [norm_1,norm_2]
  dsimp only at htransport
  linear_combination htransport

theorem first_rhs (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R) :
    let b := v 0*(p 0:R)
    let q := 1+b
    let X := q*v 5
    let Y := (q*(q*q))*v 6
    let P := (X*Y)*Y
    let k := v 8+v 9
    (firstParts p).2.evalRing (normalize p v j u first)=b*b*(1+P*(P+1)*k*k) := by
  simp only [firstParts,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    Int.cast_one,Int.cast_ofNat,Nat.cast_one,Nat.cast_ofNat,
    norm_0,norm_1,norm_2,norm_3,norm_4,norm_5,norm_6,norm_7,norm_8,norm_9,norm_10,norm_11]
  ring

theorem first_zero (p : Fin 4 → ℤ) (v : Fin 12 → R) (j u first : R)
    (htransport : let b := v 0*(p 0:R); let q := 1+b; let A := (p 1:R)+v 5
      q*((q-v 1-v 2)*A-v 1) = -b*u)
    (hnorm : let q := 1+v 0*(p 0:R); let X := q*v 5; let Y := (q*(q*q))*v 6
      let P := (X*Y)*Y; let k := v 8+v 9
      first*first=1+P*(P+1)*k*k) :
    (graph p).first.evalRing (normalize p v j u first)=0 := by
  rw [first_shape]
  simp only [Expr.evalRing_sub,Expr.evalRing_mul]
  rw [first_root p v j u first htransport,first_rhs p v j u first]
  dsimp only at hnorm
  rw [←hnorm]
  ring

#print axioms Absorb88NormalizationRing.main_invariant
#print axioms Absorb88NormalizationRing.ordinary_invariant
#print axioms Absorb88NormalizationRing.first_root
#print axioms Absorb88NormalizationRing.new_transport
#print axioms Absorb88NormalizationRing.first_rhs
#print axioms Absorb88NormalizationRing.first_zero
end Absorb88NormalizationRing

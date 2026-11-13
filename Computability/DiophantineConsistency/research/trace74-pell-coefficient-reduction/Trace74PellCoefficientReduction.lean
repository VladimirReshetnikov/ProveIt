import Trace74PellBitlistChecker

/-! Sparse Pell coefficients modulo a square-minus-one modulus. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace Trace74PellCoefficientReduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem same_add {m x y z w : V} (hm : 0<m)
    (h : x%m=y%m) (h' : z%m=w%m) : (x+z)%m=(y+w)%m := by
  rw [mod_add hm,mod_add (a:=y) hm,h,h']

private theorem same_mul {m x y z w : V} (hm : 0<m)
    (h : x%m=y%m) (h' : z%m=w%m) : (x*z)%m=(y*w)%m := by
  rw [mod_mul hm,mod_mul (a:=y) hm,h,h']

/-- Reduce the base and discriminant when `Y=q³` and `m=q²−1`.
The remaining explicit premise is the power residue `X ≡ x (mod m)`. -/
theorem sparse_coefficients (q m X x : V) (hm : 0<m)
    (hq : q*q=m+1) (hx : X%m=x%m) :
    let A := (q*q*q)*(X+1)
    (A+1)%m=(q*(x+1)+1)%m ∧
      (A*(A+2))%m=((x+1)*(x+1)+2*q*(x+1))%m := by
  have hqq : (q*q)%m=(1:V)%m := by
    rw [hq,show m+1=1+m*1 by ring,mod_add_mul' _ _ hm]
  have hy : (q*q*q)%m=q%m := by
    have hp := same_mul hm hqq (show q%m=q%m from rfl)
    simpa only [one_mul] using hp
  have ha : ((q*q*q)*(X+1))%m=(q*(x+1))%m :=
    same_mul hm hy (same_add hm hx rfl)
  constructor
  · exact same_add hm ha rfl
  · calc
      (((q*q*q)*(X+1))*((q*q*q)*(X+1)+2))%m =
          ((((q*q*q)*(X+1))*((q*q*q)*(X+1)))+
            2*((q*q*q)*(X+1)))%m := by congr 1 <;> ring
      _ = ((q*(x+1))*(q*(x+1))+2*(q*(x+1)))%m :=
        same_add hm (same_mul hm ha ha) (same_mul hm rfl ha)
      _ = ((q*q)*(x+1)*(x+1)+2*q*(x+1))%m := by congr 1 <;> ring
      _ = ((x+1)*(x+1)+2*q*(x+1))%m := by
        simpa only [one_mul] using
          same_add hm (same_mul hm (same_mul hm hqq rfl) rfl) rfl

#print axioms Trace74PellCoefficientReduction.sparse_coefficients
end Trace74PellCoefficientReduction

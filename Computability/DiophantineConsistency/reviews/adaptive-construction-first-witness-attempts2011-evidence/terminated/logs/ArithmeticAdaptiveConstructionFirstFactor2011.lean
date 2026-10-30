import DiophantineConsistency.ArithmeticAdaptiveConstructionFactorLemmas2011
import DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011

/-! The actual literal first factor from its signed additive carrier. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionFirstFactor2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
  ArithmeticAdaptiveFirstDivisibility2011 ArithmeticAdaptiveConstructionFactorLemmas2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual signed first root is the natural scaled old root when its
additive carrier identity holds; the first norm makes the literal factor +1. -/
theorem first_factor_of_additive (p : Fin 4 → ℕ) (v : Fin 13 → V) (tau : V)
    (hcut : let b : V := v 0*(p 0:V)
      let q := 1+b
      let Q := q*(q*q)
      let k := v 9+v 10
      let ell := (v 6*v 7)*(v 7*k)
      let M := Q*b
      let W := 1+k*b
      let A := v 6+(p 1:V)*q
      let Bp := q*A
      let Bn := (v 1+v 2)*A+v 1*q
      M*(ell+k+v 8)+v 7*b+Bn*(W*Q)=Bp*(W*Q)+M*tau)
    (hnorm : let k : V := v 9+v 10
      let ell := (v 6*v 7)*(v 7*k)
      tau*tau=1+ell*(ell+k)) :
    (pairEval (factors (fun j => (p j:ℤ))).1 v).1 =
      (pairEval (factors (fun j => (p j:ℤ))).1 v).2+1 := by
  let b : V := v 0*(p 0:V)
  let q := 1+b
  let Q := q*(q*q)
  let k := v 9+v 10
  let ell := (v 6*v 7)*(v 7*k)
  let M := Q*b
  let W := 1+k*b
  let A := v 6+(p 1:V)*q
  let Bp := q*A
  let Bn := (v 1+v 2)*A+v 1*q
  let root := M*tau
  let rhs := M*M*(1+ell*(ell+k))
  have hrep := first_root_rep p v
  have hroot : Equivalent (pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v)
      (natural root) := by
    apply equivalent_trans hrep
    change (M*(ell+k+v 8)+v 7*b+Bn*(W*Q))+0=Bp*(W*Q)+root
    simpa only [add_zero,root] using hcut
  have hrhs : Equivalent (pairEval (rightTerm (factors (fun j => (p j:ℤ))).1) v)
      (natural rhs) := by
    rw [first_rhs_pair p v]
    exact equivalent_refl _
  have hsq : root*root=rhs := by
    change (M*tau)*(M*tau)=M*M*(1+ell*(ell+k))
    calc _=M*M*(tau*tau) := by ring
         _=M*M*(1+ell*(ell+k)) := by rw [show tau*tau=1+ell*(ell+k) from hnorm]
  rw [first_shape (fun j => (p j:ℤ))]
  exact square_factor_unit _ _ v root rhs hroot hrhs hsq
end DiophantineConsistency.ArithmeticAdaptiveConstructionFirstFactor2011

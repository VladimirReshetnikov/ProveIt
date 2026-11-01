import DiophantineConsistency.ArithmeticAdaptiveConstructionFactorLemmas2011
import DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011

/-! The actual literal main factor from additive carrier data. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionMainFactor2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
  ArithmeticAdaptiveMainOrientation2011 ArithmeticAdaptiveConstructionFactorLemmas2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual signed main root is the natural scaled old root once its
additive shift relation holds; the old norm makes the literal factor +1. -/
theorem main_factor_of_additive (p : Fin 4 → ℕ) (v : Fin 13 → V) (gammaOld : V)
    (hF : v 1≤1+v 0*(p 0:V))
    (hshift : let b : V := v 0*(p 0:V)
      let q := 1+b
      let U := v 7*(q*q)
      let E := v 6*v 7
      let k := v 9+v 10
      let R := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
      U*v 12+E*q+R+1=k+U*gammaOld)
    (hnorm : let k : V := v 9+v 10
      let c := v 9+v 7*k
      let a := v 6*v 7+v 7
      let H := 3+4*a
      let D := H+a*a
      (v 6+a*c+H*gammaOld)*(v 6+a*c+H*gammaOld)=1+D*(c*c)) :
    (pairEval (factors (fun j => (p j:ℤ))).2.1 v).1 =
      (pairEval (factors (fun j => (p j:ℤ))).2.1 v).2+1 := by
  let b : V := v 0*(p 0:V)
  let q := 1+b
  let U := v 7*(q*q)
  let E := v 6*v 7
  let k := v 9+v 10
  let c := v 9+v 7*k
  let a := E+v 7
  let H := 3+4*a
  let D := H+a*a
  let R := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  let root := U*(v 6+a*c+H*gammaOld)
  let rhs := U*U*(1+D*(c*c))
  have hrep := main_root_rep p v (by simp) hF
  have hroot : Equivalent (pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v)
      (natural root) := by
    apply equivalent_trans hrep
    change (U*(v 6+a*c)+H*(U*v 12+E*q+R+1))+0=H*k+root
    rw [show U*v 12+E*q+R+1=k+U*gammaOld from hshift]
    dsimp only [root]
    ring
  have hrhs : Equivalent (pairEval (rightTerm (factors (fun j => (p j:ℤ))).2.1) v)
      (natural rhs) := by
    rw [main_rhs_pair p v]
    exact equivalent_refl _
  have hsq : root*root=rhs := by
    change (U*(v 6+a*c+H*gammaOld))*(U*(v 6+a*c+H*gammaOld))=
      U*U*(1+D*(c*c))
    calc _=U*U*((v 6+a*c+H*gammaOld)*(v 6+a*c+H*gammaOld)) := by ring
         _=U*U*(1+D*(c*c)) := by rw [show (v 6+a*c+H*gammaOld)*
           (v 6+a*c+H*gammaOld)=1+D*(c*c) from hnorm]
  rw [main_shape (fun j => (p j:ℤ))]
  exact square_factor_unit _ _ v root rhs hroot hrhs hsq
end DiophantineConsistency.ArithmeticAdaptiveConstructionMainFactor2011

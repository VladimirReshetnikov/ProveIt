import Absorb88Graph
import Absorb88First

/-! The forward map from the 89 graph to the 88 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Absorb88Forward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb88 Absorb88First
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def transform (p : Fin 4 → ℕ) (v : Fin 12 → V) : Fin 12 → V :=
  let q : V := 1+v 0*(p 0:V)
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  let ell : V := (X*Y)*(Y*k)
  Function.update v 7 (ell+k+v 7)

theorem lift_cast (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    (fun i => ι (transform p v i)) = liftR (integerPorts p) (fun i => ι (v i)) := by
  funext i
  by_cases h : i = 7
  · subst i
    simp [transform,liftR,integerPorts,map_add,map_mul]
  · simp [transform,liftR,h]

theorem zero_iff (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    InternalZero (graph (integerPorts p)).output (transform p v) ↔
      InternalZero (FreeJAbsorb89.graph (integerPorts p)).output v := by
  let a := (graph (integerPorts p)).first
  let b := (graph (integerPorts p)).main
  let c := (graph (integerPorts p)).ordinary
  let a' := (FreeJAbsorb89.graph (integerPorts p)).first
  let b' := (FreeJAbsorb89.graph (integerPorts p)).main
  let c' := (FreeJAbsorb89.graph (integerPorts p)).ordinary
  have hout : (graph (integerPorts p)).output = a*a+b*b+c*c := by rfl
  have hout' : (FreeJAbsorb89.graph (integerPorts p)).output = a'*a'+b'*b'+c'*c' := by rfl
  rw [internalZero_iff,internalZero_iff,lift_cast,hout,hout']
  simp only [Expr.evalRing_add,Expr.evalRing_mul]
  rw [first_eval,main_eval,ordinary_eval]

theorem transform_pos (p : Fin 4 → ℕ) (v : Fin 12 → V) (hv : ∀j,0<v j) :
    ∀j,0<transform p v j := by
  intro j
  by_cases h : j=7
  · subst j
    simp only [transform,Function.update_self]
    exact add_pos_of_nonneg_of_pos (by simp) (hv 7)
  · simpa [transform,h] using hv j

#print axioms Absorb88Forward.zero_iff
#print axioms Absorb88Forward.transform_pos
end Absorb88Forward

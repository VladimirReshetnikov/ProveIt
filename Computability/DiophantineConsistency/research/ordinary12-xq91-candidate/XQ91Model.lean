import XQ91

/-! A model-level zero comparison after the explicit X=q*w substitution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJXQ91Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ModelDifferenceRing
open FreeJXQ91

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def integerPorts (p : Fin 4 → ℕ) : Fin 4 → ℤ := fun i => (p i : ℤ)

def transform (p : Fin 4 → ℕ) (v : Fin 12 → V) : Fin 12 → V :=
  Function.update v 5 ((1 + v 0 * (p 0 : V)) * v 5)

theorem lift_cast (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    (fun i => ι (transform p v i)) =
      liftX (integerPorts p) (fun i => ι (v i)) := by
  funext i
  by_cases h : i = 5
  · subst i
    simp [transform, liftX, integerPorts, map_add, map_mul, Int.cast_natCast]
  · simp [transform, liftX, h]

theorem zero_iff_transformed (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    InternalZero (graph (integerPorts p)).output v ↔
      InternalZero (FreeJQCube92.graph (integerPorts p)).output (transform p v) := by
  let a := (graph (integerPorts p)).first
  let b := (graph (integerPorts p)).main
  let c := (graph (integerPorts p)).ordinary
  let a' := (FreeJQCube92.graph (integerPorts p)).first
  let b' := (FreeJQCube92.graph (integerPorts p)).main
  let c' := (FreeJQCube92.graph (integerPorts p)).ordinary
  have hout : (graph (integerPorts p)).output = a*a+b*b+c*c := by rfl
  have hout' : (FreeJQCube92.graph (integerPorts p)).output = a'*a'+b'*b'+c'*c' := by rfl
  rw [internalZero_iff, internalZero_iff, lift_cast, hout, hout']
  simp only [Expr.evalRing_add, Expr.evalRing_mul]
  rw [FreeJXQ91.first_eval, FreeJXQ91.main_eval, FreeJXQ91.ordinary_eval]

#print axioms FreeJXQ91Model.lift_cast
#print axioms FreeJXQ91Model.zero_iff_transformed
end FreeJXQ91Model

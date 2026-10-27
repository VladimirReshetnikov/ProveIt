import DiophantineConsistency.ArithmeticCarrierSoundness2011

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticCarrierSoundness2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ObjectCurrentEquation2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Transport comes from this same literal zero, with no prior norm assumptions. -/
theorem zero_transport (v : Fin 14 → V) (hv : ∀j,0<v j)
    (hz : expression.splitNatural.1.evalSemiring v=expression.splitNatural.2.evalSemiring v) :
    let q:=(CurrentMasks2011.beta:V)*v 0+1
    ((CurrentKernel2011.K:V)+v 8)*q+q=
      ((CurrentKernel2011.K:V)+v 8)*(v 1+v 2)+v 1+v 3*(q-1)+1 :=
  (current_equations v hv hz).1

example (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j)
    (hz : (expressionAt (fun j => (p j:ℤ))).splitNatural.1.evalSemiring v=
      (expressionAt (fun j => (p j:ℤ))).splitNatural.2.evalSemiring v) :
    Equations (p 0:V) (p 1:V) (p 2:V) (p 3:V) v :=
  expressionAt_equations p v hb hl hh hv hz

example (v : Fin 14 → V)
    (hz : naturalExpression.splitNatural.1.evalSemiring v=
      naturalExpression.splitNatural.2.evalSemiring v) :
    Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
      (fun j => v j+1) := current_natural_equations v hz

-- The positive shift is by one; the actual source high mask is shifted once too.
example : CurrentWindowCarry2011.ports 3=
    ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):ℤ) := rfl

#print axioms ArithmeticCarrierSoundness2011.expressionAt_equations
#print axioms ArithmeticCarrierSoundness2011.current_bounds
#print axioms ArithmeticCarrierSoundness2011.current_equations
#print axioms ArithmeticCarrierSoundness2011.current_natural_equations
#print axioms zero_transport
end DiophantineConsistency.ArithmeticCarrierSoundness2011Checks

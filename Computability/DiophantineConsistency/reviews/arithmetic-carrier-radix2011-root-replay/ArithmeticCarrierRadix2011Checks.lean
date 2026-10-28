import DiophantineConsistency.ArithmeticCarrierRadix2011

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticCarrierRadix2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierRadix2011 ObjectCurrentEquation2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (v : Fin 14 → V) (hv : ∀j,0<v j)
    (hz : expression.splitNatural.1.evalSemiring v=expression.splitNatural.2.evalSemiring v) :
    (X v=Exp.exp (rank v) ∧ Exponential (rank v) (X v) ∧ Exp.exp (rank v)<Y v) ∧
      Radix v := current_radix v hv hz

example (v : Fin 14 → V)
    (hz : naturalExpression.splitNatural.1.evalSemiring v=
      naturalExpression.splitNatural.2.evalSemiring v) :
    Radix (fun j => v j+1) := (current_natural_radix v hz).2

-- A zero residual exponent forces w=1, so no strict bound is asserted.
example (v : Fin 14 → V) (L : V)
    (hw : v 8=Exp.exp (rank v-(CurrentMasks2011.width:V)*L))
    (hzero : (CurrentMasks2011.width:V)*L=rank v) : v 8=1 := by
  simpa only [hzero,tsub_self,exp_zero] using hw

example : (CurrentMasks2011.beta:V)+1=Exp.exp (94517:V) := by
  rw [←(current_width (V:=V)).1]
  exact current_beta_exp_add_one

-- The actual high port is shifted once, independently of the domain shift.
example : CurrentWindowCarry2011.ports 3=
    ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):ℤ) := rfl

#print axioms exp_nat_cast
#print axioms current_beta_exp_add_one
#print axioms current_beta_exp
#print axioms current_width
#print axioms current_power
#print axioms current_radix
#print axioms current_natural_power
#print axioms current_natural_radix
end DiophantineConsistency.ArithmeticCarrierRadix2011Checks

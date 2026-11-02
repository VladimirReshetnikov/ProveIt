import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

/-! Generic carrier negative-unit exclusions, independent of port values,
rank recovery and the actual twelve-variable literal binding. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Ordinary12CarrierExclusions
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private def x (i : Fin 8) : Expr (Fin 8) := .var i

/-- First carrier: q,z,n are represented as arbitrary signed pairs. -/
def firstFactor : Expr (Fin 8) :=
  let q := x 0 - x 1
  let z := x 2 - x 3
  let n := x 4 - x 5
  let m := q*q*q*(q-1)
  1 + z*z - m*m*n

/-- Main carrier: u,a,c,d are represented as arbitrary signed pairs. -/
def mainFactor : Expr (Fin 8) :=
  let u := x 0 - x 1
  let a := x 2 - x 3
  let c := x 4 - x 5
  let d := x 6 - x 7
  1 + d*d - u*u*(1+(a*a+4*a+3)*c*c)

theorem first_factor_ne_negative_one (v : Fin 8 → V) :
    (pairEval firstFactor v).1 + 1 ≠ (pairEval firstFactor v).2 := by
  intro h
  have hn := negative_residue h
  rw [pairEval_residue] at hn
  let q := residue (v 0) - residue (v 1)
  let z := residue (v 2) - residue (v 3)
  let n := residue (v 4) - residue (v 5)
  have he : syntaxEval (fun i => residue (v i)) firstFactor =
      1 + z^2 - (q^3*(q-1))^2*n := by
    simp only [firstFactor, x, syntax_add, syntax_sub, syntax_mul, syntax_var,
      syntax_ofNat, Nat.cast_one, Nat.cast_ofNat]
    dsimp only [q,z,n]
    ring
  rw [he] at hn
  exact first_bad q z n hn

theorem main_factor_ne_negative_one (v : Fin 8 → V) :
    (pairEval mainFactor v).1 + 1 ≠ (pairEval mainFactor v).2 := by
  intro h
  have hn := negative_residue h
  rw [pairEval_residue] at hn
  let u := residue (v 0) - residue (v 1)
  let a := residue (v 2) - residue (v 3)
  let c := residue (v 4) - residue (v 5)
  let d := residue (v 6) - residue (v 7)
  have he : syntaxEval (fun i => residue (v i)) mainFactor =
      1+d^2-u^2*(1+(a^2+4*a+3)*c^2) := by
    simp only [mainFactor, x, syntax_add, syntax_sub, syntax_mul, syntax_var,
      syntax_ofNat, Nat.cast_one, Nat.cast_ofNat]
    dsimp only [u,a,c,d]
    ring
  rw [he] at hn
  exact main_bad u a c d hn

end DiophantineConsistency.Ordinary12CarrierExclusions
#print axioms DiophantineConsistency.Ordinary12CarrierExclusions.first_factor_ne_negative_one
#print axioms DiophantineConsistency.Ordinary12CarrierExclusions.main_factor_ne_negative_one

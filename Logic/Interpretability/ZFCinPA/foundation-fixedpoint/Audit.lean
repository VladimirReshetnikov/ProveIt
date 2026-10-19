import Foundation.FirstOrder.Bootstrapping.FixedPoint

set_option autoImplicit false

namespace LO.FirstOrder.Arithmetic

#print axioms LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic.substNumeral_app_quote
#print axioms LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic.substNumerals_app_quote
#print axioms LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic.substNumerals_app_quote_quote
#print axioms LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic.substNumeralParams_app_quote
#print axioms LO.FirstOrder.Arithmetic.diagonal
#print axioms LO.FirstOrder.Arithmetic.multidiagonal
#print axioms LO.FirstOrder.Arithmetic.exclusiveMultifixedpoint_inj_iff
#print axioms LO.FirstOrder.Arithmetic.exclusiveMultidiagonal
#print axioms LO.FirstOrder.Arithmetic.multifixedpoint_pi
#print axioms LO.FirstOrder.Arithmetic.exclusiveMultifixedpoint_pi
#print axioms LO.FirstOrder.Arithmetic.parameterized_diagonal
#print axioms LO.FirstOrder.Arithmetic.parameterized_diagonal₁

open Bootstrapping Bootstrapping.Arithmetic

section InternalSubstitution
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {k : ℕ}

example (σ π : ArithmeticSemisentence 1) :
    substNumeral ⌜σ⌝ (⌜π⌝ : V) = ⌜(σ/[⌜π⌝] : ArithmeticSentence)⌝ :=
  substNumeral_app_quote σ π

example (σ : ArithmeticSemisentence k) (v : Fin k → ℕ) :
    (substNumerals ⌜σ⌝ (v ·) : V) =
      ⌜((Rew.subst (fun i ↦ ↑(v i))) ▹ σ : ArithmeticSentence)⌝ :=
  substNumerals_app_quote σ v

example (σ : ArithmeticSemisentence k) (π : Fin k → ArithmeticSemisentence k) :
    substNumerals (⌜σ⌝ : V) (fun i ↦ ⌜π i⌝) =
      ⌜((Rew.subst (fun i ↦ ⌜π i⌝)) ▹ σ : ArithmeticSentence)⌝ :=
  substNumerals_app_quote_quote σ π

example (σ τ : ArithmeticSemisentence (k + 1)) :
    (substNumeralParams k ⌜σ⌝ ⌜τ⌝ : V) =
      ⌜((Rew.subst (⌜τ⌝ :> fun i : Fin k ↦ #i)) ▹ σ : ArithmeticSemisentence k)⌝ :=
  substNumeralParams_app_quote σ τ
end InternalSubstitution

section FixedPoints
variable {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T] {k : ℕ} {i : Fin k}

example (θ : ArithmeticSemisentence 1) :
    T ⊢ fixedpoint θ 🡘 θ/[⌜fixedpoint θ⌝] := diagonal θ

example (θ : Fin k → ArithmeticSemisentence k) :
    T ⊢ multifixedpoint θ i 🡘 (Rew.subst fun j ↦ ⌜multifixedpoint θ j⌝) ▹ (θ i) :=
  multidiagonal θ

example (θ : Fin k → ArithmeticSemisentence k) :
    T ⊢ exclusiveMultifixedpoint θ i 🡘
      (Rew.subst fun j ↦ ⌜exclusiveMultifixedpoint θ j⌝) ▹ θ i :=
  exclusiveMultidiagonal θ

example (θ : ArithmeticSemisentence (k + 1)) :
    T ⊢ ∀⁰* (parameterizedFixedpoint θ 🡘 “!θ !!(⌜parameterizedFixedpoint θ⌝) ⋯”) :=
  parameterized_diagonal θ

example (θ : ArithmeticSemisentence 2) :
    T ⊢ ∀⁰ (parameterizedFixedpoint θ 🡘 θ/[⌜parameterizedFixedpoint θ⌝, #0]) :=
  parameterized_diagonal₁ θ
end FixedPoints

section Syntax
variable {k m : ℕ} {i j : Fin k}

example (θ : Fin k → ArithmeticSemisentence k) :
    exclusiveMultifixedpoint θ i = exclusiveMultifixedpoint θ j ↔ i = j :=
  exclusiveMultifixedpoint_inj_iff θ

example {θ : Fin k → ArithmeticSemisentence k}
    (h : ∀ i, Hierarchy 𝚷 (m + 1) (θ i)) :
    Hierarchy 𝚷 (m + 1) (multifixedpoint θ i) := multifixedpoint_pi h

example {θ : Fin k → ArithmeticSemisentence k}
    (h : ∀ i, Hierarchy 𝚷 (m + 1) (θ i)) :
    Hierarchy 𝚷 (m + 1) (exclusiveMultifixedpoint θ i) := exclusiveMultifixedpoint_pi h
end Syntax

end LO.FirstOrder.Arithmetic

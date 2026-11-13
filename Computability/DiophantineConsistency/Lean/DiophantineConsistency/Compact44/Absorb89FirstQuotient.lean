import DiophantineConsistency.Compact44.Absorb89First

/-! Positive first Pell root from the actual draft graph zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb89FirstQuotient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb89 Absorb89First
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveQuotients2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual graph zero and positive b yield a positive first root and
its exact Pell norm. No main residual or old graph zero is assumed. -/
theorem first_root (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (graph (integerPorts p)).output v)
    (hb : 0<v 0*(p 0:V)) :
    let q : V := 1+v 0*(p 0:V)
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let k : V := v 8+v 9
    let Q : V := (X*Y)*Y
    ∃ first : V, 0<first ∧
      magnitude (pairEval (firstParts (integerPorts p)).1 v) = (v 0*(p 0:V))*first ∧
      first*first=1+Q*(Q+1)*k*k := by
  let q : V := 1+v 0*(p 0:V)
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  let Q : V := (X*Y)*Y
  let ell : V := (X*Y)*(Y*k)
  have hs := first_scaled_norm p v hz
  obtain ⟨first,hroot,hnorm⟩ := scaled_quotient (v 0*(p 0:V))
    (magnitude (pairEval (firstParts (integerPorts p)).1 v)) (1+ell*(ell+k)) hb hs
  have hf : 0<first := pos_of_mul_pos_left (by rw [hnorm]; simp) (by simp)
  have hn : first*first=1+Q*(Q+1)*k*k := by
    calc
      first*first=1+ell*(ell+k) := hnorm
      _=1+Q*(Q+1)*k*k := by dsimp [ell,Q]; ring
  exact ⟨first,hf,hroot,hn⟩

#print axioms Absorb89FirstQuotient.first_root
end Absorb89FirstQuotient

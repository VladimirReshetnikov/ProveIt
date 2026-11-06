import DiophantineConsistency.Norm38IPRAEndpoint
import DiophantineConsistency.ModelJonesSyntax

/-! Source-only client: ring semantics for the current 38-witness seed.
The human FORMULA.md is a separate transcription and is not read by Lean. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Norm38NamedFormula
open ExecutableJones NinePolynomial

theorem eval_current {R : Type*} [CommRing R] (a : Fin 9 → R) :
    Norm38IPRAEndpoint.expression.evalRing a =
      let ν := 38
      let seed := SharingSeed38.seed CurrentWindowCarry2011.ports
      let z := indexZ seed 0
      let y := indexY seed 0
      let aa : Fin 10 → R := Fin.cons 1 a
      let b := aa 0 * (y : R) + 1 + aa 1
      let B := b ^ 5
      let q := B ^ codingL4 ν
      let n := q ^ 16
      let e := ∑ k ∈ codingStar ν 4,
        ((z : R) + (pCoefficient seed k : R)) * B ^ (codingLexp ν 4 - codingExpo ν 4 k)
      let l := ∑ i ∈ Finset.range ν, B ^ (5 ^ (i + 1))
      let lam := ∑ i ∈ Finset.range (4 * codingLexp ν 4), B ^ i
      let g := aa 2 + 1
      let θ := B - 2 * (z : R)
      let v : RingVars R := ⟨rankCode (aa 0) (z : R) b e g l n q θ lam, n, b, g,
        32 * b * B ^ (5 ^ ν), aa 3 + 1, aa 4 + 1, aa 5 + 1, aa 6, aa 7 + 1, aa 8 + 1⟩
      RefinedPair.value (v.rad 0) (v.rad 1) (v.wt 0) (v.wt 1) (a 8) v.dvsr v.dvnd v.marg := by
  rw [Norm38IPRAEndpoint.expression, ModelJonesSyntax.evalRing_expression,
    ModelJonesSyntax.mapVars_syntaxVars]

#print axioms eval_current
end DiophantineConsistency.Norm38NamedFormula

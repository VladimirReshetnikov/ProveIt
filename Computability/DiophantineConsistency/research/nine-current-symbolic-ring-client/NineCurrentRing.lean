import DiophantineConsistency.IPRANineCurrent

/-! A closed-coefficient ring description of the checked nine-coordinate syntax.
The enormous finite sums and powers are kept symbolic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.NineCurrentRing
open ExecutableJones NinePolynomial

/-- Exact integer evaluation, with the seed's coefficients fixed symbolically. -/
theorem eval_current (a : Fin 9 → ℤ) :
    IPRANineCurrent.expression.evalRing a =
      let ν := QuarticCompiler.witnessCount IPRANineCurrent.left IPRANineCurrent.right
      let seed := IPRANineCurrent.seed
      let z := indexZ seed 0
      let y := indexY seed 0
      let aa : Fin 10 → ℤ := Fin.cons 1 a
      let b := aa 0 * (y : ℤ) + 1 + aa 1
      let B := b ^ 5
      let q := B ^ codingL4 ν
      let n := q ^ 16
      let e := ∑ k ∈ codingStar ν 4,
        ((z : ℤ) + (pCoefficient seed k : ℤ)) * B ^ (codingLexp ν 4 - codingExpo ν 4 k)
      let l := ∑ i ∈ Finset.range ν, B ^ (5 ^ (i + 1))
      let lam := ∑ i ∈ Finset.range (4 * codingLexp ν 4), B ^ i
      let g := aa 2 + 1
      let θ := B - 2 * (z : ℤ)
      let v : RingVars ℤ := ⟨rankCode (aa 0) (z : ℤ) b e g l n q θ lam, n, b, g,
        32 * b * B ^ (5 ^ ν), aa 3 + 1, aa 4 + 1, aa 5 + 1, aa 6, aa 7 + 1, aa 8 + 1⟩
      RefinedPair.value (v.rad 0) (v.rad 1) (v.wt 0) (v.wt 1) (a 8) v.dvsr v.dvnd v.marg := by
  rw [IPRANineCurrent.expression, ModelJonesSyntax.evalRing_expression,
    ModelJonesSyntax.mapVars_syntaxVars]

#print axioms eval_current
end DiophantineConsistency.NineCurrentRing

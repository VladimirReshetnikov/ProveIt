import OAI.Combinatorics.Progressions.Nilpotent.NativeIntegerChartNiltest

namespace OAI

universe universeLevel

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M : Type universeLevel} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
  (E : RationalFilteredNilmanifold M s e)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {σ₀ σ τ ι κ : Type*} {w₀ : σ₀ → ℕ} {w : σ → ℕ}

theorem pairOrbitSymbol_withOrbit_integerChartPullback_eq
    (v : τ → ℕ) (β : σ → MvPolynomial τ ℤ)
    (hβ : ∀ i, integerSampledRealChart β i ∈ weightedSupportLE v (w i))
    (reference : D.Niltest w₀) (p : D.filtration.realification.PolynomialOrbit v)
    (selected ambient : E.Niltest w) (horbit : selected.orbit = ambient.orbit)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i})) :
    pairOrbitSymbol D E (reference.withOrbit p).orbit
      (selected.integerChartPullback v β hβ).orbit b ω hF =
    pairOrbitSymbol D E p (ambient.integerChartPullback v β hβ).orbit b ω hF := by
  change pairOrbitSymbol D E p (selected.integerChartPullback v β hβ).orbit b ω hF = _
  rw [selected.integerChartPullback_orbit_eq_of_orbit_eq v β hβ ambient horbit]

theorem pairOrbitSymbol_withOrbit_integerChartPullback
    (v : τ → ℕ) (β : σ → MvPolynomial τ ℤ)
    (hβ : ∀ i, integerSampledRealChart β i ∈ weightedSupportLE v (w i))
    (reference : D.Niltest w₀) (p : D.filtration.realification.PolynomialOrbit v)
    (selected ambient : E.Niltest w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i})) :
    pairOrbitSymbol D E (reference.withOrbit p).orbit
      ((selected.withOrbit ambient.orbit).integerChartPullback v β hβ).orbit b ω hF =
    pairOrbitSymbol D E p (ambient.integerChartPullback v β hβ).orbit b ω hF := rfl

theorem pairOrbitSymbol_withOrbit_frozen_integerChartPullback_eq
    (β : σ → MvPolynomial τ ℤ)
    (hβ : ∀ i, integerSampledRealChart β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (keep : τ → Prop) (fixed fixed' : {i // ¬keep i} → ℤ)
    (hfreeze : ∀ i, integerSampledRealChart (fun z => freezePolynomial keep fixed (β z)) i ∈
      weightedSupportLE (fun _ : {i // keep i} => 1) (w i))
    (hfreeze' : ∀ i, integerSampledRealChart (fun z => freezePolynomial keep fixed' (β z)) i ∈
      weightedSupportLE (fun _ : {i // keep i} => 1) (w i))
    (reference : D.Niltest w₀)
    (p : D.filtration.realification.PolynomialOrbit (fun _ : {i // keep i} => 1))
    (selected ambient : E.Niltest w) (horbit : selected.orbit = ambient.orbit)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hE : ∀ k, E.filtration.layer k = Submodule.span ℚ (c '' {i | k ≤ ν i})) :
    pairOrbitSymbol D E (reference.withOrbit p).orbit
      (selected.integerChartPullback (fun _ : {i // keep i} => 1)
        (fun z => freezePolynomial keep fixed (β z)) hfreeze).orbit b ω hF =
    pairOrbitSymbol D E p
      (ambient.integerChartPullback (fun _ : {i // keep i} => 1)
        (fun z => freezePolynomial keep fixed' (β z)) hfreeze').orbit b ω hF := by
  rw [pairOrbitSymbol_withOrbit_integerChartPullback_eq D E
    (fun _ : {i // keep i} => 1) (fun z => freezePolynomial keep fixed (β z))
    hfreeze reference p selected ambient horbit b ω hF]
  have lift (Q Q' : E.Niltest (fun _ : {i // keep i} => 1))
      (heq : Q.symbol c ν hE = Q'.symbol c ν hE) :
      pairOrbitSymbol D E p Q.orbit b ω hF = pairOrbitSymbol D E p Q'.orbit b ω hF := by
    apply pairOrbitSymbol_eq_of_right_symbol_eq D E b ω hF c ν hE
    exact heq
  exact lift
    (ambient.integerChartPullback (fun _ : {i // keep i} => 1)
      (fun z => freezePolynomial keep fixed (β z)) hfreeze)
    (ambient.integerChartPullback (fun _ : {i // keep i} => 1)
      (fun z => freezePolynomial keep fixed' (β z)) hfreeze')
    (ambient.integerChartPullback_frozen_symbol_independent
      β hβ keep fixed fixed' hfreeze hfreeze' c ν hE)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

import OAI.Combinatorics.Progressions.Lattices.IntegerFrozenChart

namespace OAI

universe universeLevel

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] BoolLieFamily

variable {L M : Type universeLevel} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    {σ τ ι : Type*} {w : σ → ℕ} {v : τ → ℕ}

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart
  weightedAdaptedRealChartHom realPolynomialSymbolHom realSymbolHomogeneousPullbackHom

theorem pairOrbit_polynomialOrbitRealChart_log
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    (pairOrbit D E (D.filtration.polynomialOrbitRealChart w v β hβ p)
      (E.filtration.polynomialOrbitRealChart w v β hβ q)).log =
        realChartSubstitute β (pairOrbit D E p q).log := by
  simp only [pairOrbit, piRealOrbit, PolynomialOrbit.log, polynomialOrbitOfLog, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases i
  · change VectorPolynomial.map
      ((realProductSingle (L := BoolLieFamily L M) false).restrictScalars ℚ)
      (E.filtration.polynomialOrbitRealChart w v β hβ q).log =
      realChartSubstitute β (VectorPolynomial.map
        ((realProductSingle (L := BoolLieFamily L M) false).restrictScalars ℚ) q.log)
    rw [polynomialOrbitRealChart_log]
    exact (realChartSubstitute_map β
      (realProductSingle (L := BoolLieFamily L M) false) q.log).symm
  · change VectorPolynomial.map
      ((realProductSingle (L := BoolLieFamily L M) true).restrictScalars ℚ)
      (D.filtration.polynomialOrbitRealChart w v β hβ p).log =
      realChartSubstitute β (VectorPolynomial.map
        ((realProductSingle (L := BoolLieFamily L M) true).restrictScalars ℚ) p.log)
    rw [polynomialOrbitRealChart_log]
    exact (realChartSubstitute_map β
      (realProductSingle (L := BoolLieFamily L M) true) p.log).symm

attribute [local irreducible] pairOrbit

theorem pairOrbitSymbol_polynomialOrbitRealChart
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    pairOrbitSymbol D E (D.filtration.polynomialOrbitRealChart w v β hβ p)
      (E.filtration.polynomialOrbitRealChart w v β hβ q) b ω hF =
        (pi (pairModels D E)).filtration.realPolynomialSymbolHom b ω hF v
          ((pi (pairModels D E)).filtration.weightedAdaptedRealChartHom w v β hβ
            ⟨⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩⟩) := by
  unfold pairOrbitSymbol
  apply congrArg ((pi (pairModels D E)).filtration.realPolynomialSymbolHom b ω hF v)
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact (pairOrbit_polynomialOrbitRealChart_log D E p q β hβ).trans
    ((pi (pairModels D E)).filtration.weightedAdaptedRealChartHom_coord
      w v β hβ ⟨⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩⟩).symm

theorem pairOrbitSymbol_chart_eq_of_homogeneous_eq
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (β' : σ → MvPolynomial τ ℝ)
    (hβ' : ∀ i, β' i ∈ weightedSupportLE v (w i))
    (htop : (fun i => MvPolynomial.weightedHomogeneousComponent v (w i) (β i)) =
      (fun i => MvPolynomial.weightedHomogeneousComponent v (w i) (β' i))) :
    pairOrbitSymbol D E (D.filtration.polynomialOrbitRealChart w v β hβ p)
      (E.filtration.polynomialOrbitRealChart w v β hβ q) b ω hF =
    pairOrbitSymbol D E (D.filtration.polynomialOrbitRealChart w v β' hβ' p)
      (E.filtration.polynomialOrbitRealChart w v β' hβ' q) b ω hF := by
  rw [pairOrbitSymbol_polynomialOrbitRealChart, pairOrbitSymbol_polynomialOrbitRealChart,
    realPolynomialSymbolHom_weightedAdaptedRealChart,
    realPolynomialSymbolHom_weightedAdaptedRealChart]
  congr 1
  congr 1

theorem pairOrbitSymbol_frozenCoordinate_independent
    (p : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (q : E.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (keep : σ → Prop) (fixed fixed' : {i // ¬keep i} → ℝ)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i})) :
    pairOrbitSymbol D E
      (D.filtration.polynomialOrbitRealChart (fun _ : σ => 1)
        (fun _ : {i // keep i} => 1) (frozenCoordinate keep fixed)
        (frozenCoordinate_support keep fixed) p)
      (E.filtration.polynomialOrbitRealChart (fun _ : σ => 1)
        (fun _ : {i // keep i} => 1) (frozenCoordinate keep fixed)
        (frozenCoordinate_support keep fixed) q) b ω hF =
    pairOrbitSymbol D E
      (D.filtration.polynomialOrbitRealChart (fun _ : σ => 1)
        (fun _ : {i // keep i} => 1) (frozenCoordinate keep fixed')
        (frozenCoordinate_support keep fixed') p)
      (E.filtration.polynomialOrbitRealChart (fun _ : σ => 1)
        (fun _ : {i // keep i} => 1) (frozenCoordinate keep fixed')
        (frozenCoordinate_support keep fixed') q) b ω hF := by
  apply pairOrbitSymbol_chart_eq_of_homogeneous_eq D E p q b ω hF
    (frozenCoordinate keep fixed) (frozenCoordinate_support keep fixed)
    (frozenCoordinate keep fixed') (frozenCoordinate_support keep fixed')
  funext i
  change MvPolynomial.homogeneousComponent 1 (frozenCoordinate keep fixed i) =
    MvPolynomial.homogeneousComponent 1 (frozenCoordinate keep fixed' i)
  simpa only [freezePolynomial, MvPolynomial.aeval_X] using
    (freezePolynomial_top_independent keep fixed fixed'
      (P := MvPolynomial.X i) (d := 1)
      (by simp only [MvPolynomial.totalDegree_X, le_refl]))

end Erdos3.RationalFilteredNilmanifold

end

end OAI

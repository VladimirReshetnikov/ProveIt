/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Mathematical statements are unchanged from the pinned upstream source.
Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.FactoredPositiveShiftContradiction
import OAI.Combinatorics.Progressions.Nilpotent.SimultaneousNiltestFactorization

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_selected_product_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {ι J σ : Type*} [Fintype ι] [Fintype J] [Fintype σ] [DecidableEq σ]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (base : ∀ i, (D i).Niltest (fun _ : σ => 1))
      (rows : J → ∀ i, (D i).Niltest (fun _ : σ => 1))
      (active : J → Finset ι) (eta : J → ∀ i, L i →ₗ[ℚ] ℚ) {p : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (Fintype.card σ : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (∀ j i, i ∈ active j → (rows j i).orbit = (base i).orbit) →
      (∀ j i, i ∈ active j → (rows j i).ComplexityLE p) →
      (∀ j i, i ∈ active j → (rows j i).normBound ≤ 1) →
      (∀ j i, i ∈ active j → ∀ k, rationalLogHeight (eta j i ((D i).basis k)) ≤ p) →
      (∀ j i, i ∈ active j → ∀ z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
        (rows j i).observable (z • x) = CircleFourier.character
          ((realifyFunctional (eta j i) z.coord : ℝ) : CircleFourier.Circle) * (rows j i).observable x) →
      ∀ (weight : ∀ i, Fin (d i) → ℕ)
        (hFlayers : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ ((D i).basis '' {k | j ≤ weight i k}))
        (origin : J → σ → ℤ) (lengths : J → σ → ℕ),
      (∀ j i, 0 < lengths j i) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j),
        ∏ i ∈ active j, (rows j i).eval x‖) →
      ∀ side : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ side i) →
      (∀ j i, Real.exp (-p) * side i ≤ lengths j i) →
    let omega := productBasisWeight weight
    let hTotal := pi_layer_span D weight hFlayers
    let orbit := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration)
      (fun i => (base i).orbit)
    let g : ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
      ⟨⟨orbit.log, orbit.property⟩⟩
    let freq := fun j => piFrequency
      (selectedOrbitFrequencies (eta j) (active j))
    ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded)
      (m : ℕ) (κ : (pi D).RealGroup)
      (E b R : ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal) omega W.toSubmodule ∧
      (∀ i k, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal).repr (v i) k) ≤
        (p + C) ^ C) ∧
      (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s → realifyFunctional (freq j) x = 0) ∧
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ κ ∈ (pi D).realLattice ∧
      E * b * R * (pi D).filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
      (∀ α i, |((pi D).basis.baseChange ℝ).repr
        (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α) i| ≤
          Real.exp ((p + C) ^ C) / monomialScale side α) ∧
      ((fun z : (σ →₀ ℕ) × Fin (Fintype.card (Σ i, Fin (d i))) => ((pi D).basis.baseChange ℝ).repr
        (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) z.1) z.2) ∈ realDenominatorGrid m) ∧
      coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
        (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
      (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) ∈
        realificationLieSubalgebra ((pi D).filtration.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨c, _, hfactor⟩ := exists_lattice_normalized_niltest_factorization s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4
  let F := Q + (Q + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget F
  refine ⟨C, hC, ?_⟩
  intro ι J σ _ _ _ _ L _ _ d _ _ _ _ _ _ _ _ D base rows active eta p
    hp hι hJ hσ hD horbit hcomp hcap hheight hvert weight hFlayers
    origin lengths hlengths hbias side hside hrelative
  have hp0 : 0 ≤ p := by linarith
  let q := productNiltestBudget p
  have hpq : p ≤ q := by
    exact (by nlinarith [sq_nonneg p] : p ≤ (p + 2) ^ 2).trans (productNiltestBudget_geometry hp0)
  have hq : 0 ≤ q := hp0.trans hpq
  have hbudget' : q + (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [F, Q, X, q, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow] using hbudget p hp0
  have hcC : (q + c) ^ c ≤ (p + C) ^ C := by linarith
  have hsidepos : ∀ i, 0 < side i := fun i => (Real.exp_pos _).trans_le (hside i)
  obtain ⟨S0, S, hS0, hS0c, hS⟩ := exists_common_product_niltest_family D base rows active eta
    hp hι hD horbit hcomp hcap hheight hvert
  let omega := productBasisWeight weight
  let hTotal := pi_layer_span D weight hFlayers
  let freq := fun j => piFrequency
    (selectedOrbitFrequencies (eta j) (active j))
  have hcorr : ∀ j, Real.exp (-q) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j), (S j).eval x‖ := by
    intro j
    apply (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans
    simpa only [(hS j).2.2.2.1] using hbias j
  have hrel : ∀ j i, Real.exp (-q) * side i ≤ lengths j i := fun j i =>
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq)) (hsidepos i).le).trans (hrelative j i)
  obtain ⟨W, v, m, κ, E, b, R, hv, hW, hheight, hfreq, hm, hmp, hκ, hebr,
      hE, hR, hb0, hR0, hcoeff, hvalues⟩ :=
    hfactor (pi D) omega hTotal S0 S (fun j => (hS j).1) freq q hq hS0c.1
      (by exact (show (Fintype.card σ : ℝ) ≤ p from hσ).trans hpq)
      (hJ.trans hpq) (fun j => (hS j).2.2.1)
      (fun j k => ((hS j).2.2.2.2.1 k).trans hpq) (fun j => (hS j).2.2.2.2.2)
      origin lengths hlengths hcorr side (fun i => (Real.exp_le_exp.mpr hcC).trans (hside i)) hrel
  let orbit := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration)
    (fun i => (base i).orbit)
  let g : ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
    ⟨⟨orbit.log, orbit.property⟩⟩
  have hg : (⟨⟨S0.orbit.log, S0.orbit.property⟩⟩ :
      ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) = g := by
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact congrArg (fun o : (pi D).filtration.realification.PolynomialOrbit (fun _ : σ => 1) => o.log) hS0
  refine ⟨W, v, m, κ, E, b, R, hv, hW, (fun i k => (hheight i k).trans hcC), hfreq, hm,
    hmp.trans (Real.exp_le_exp.mpr hcC), hκ, hebr.trans hg, ?_, hR, hb0, hR0, hcoeff, hvalues⟩
  intro α i
  exact (hE α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hcC)
    (monomialScale_pos side hsidepos α).le)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_anchored_option_product_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {J σ : Type*} [Fintype J] [Fintype σ] [DecidableEq σ] {L : (Option (Option J ⊕ J)) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Option (Option J ⊕ J)) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (P : (D none).Niltest (fun _ : σ => 1)) (P₀ : (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (U : J → (D none).Niltest (fun _ : σ => 1)) (V : J → (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (A : ∀ j, (D (some (.inl (some j)))).Niltest (fun _ : σ => 1)) (B : ∀ j, (D (some (.inr j))).Niltest (fun _ : σ => 1))
    (eta : J → L none →ₗ[ℚ] ℚ) (theta : J → L (some (.inl none)) →ₗ[ℚ] ℚ)
    (alpha : ∀ j, L (some (.inl (some j))) →ₗ[ℚ] ℚ) (beta : ∀ j, L (some (.inr j)) →ₗ[ℚ] ℚ)
    {p : ℝ} (_hp : 2 ≤ p) (_hcard : (Fintype.card (Option (Option J ⊕ J)) : ℝ) ≤ p)
    (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hD : ∀ i, (D i).GeometryComplexityLE p)
    (_hU : ∀ j, (U j).ComplexityLE p ∧ (U j).orbit = P.orbit ∧ (U j).normBound ≤ 1)
    (_hV : ∀ j, (V j).ComplexityLE p ∧ (V j).orbit = P₀.orbit ∧ (V j).normBound ≤ 1)
    (_hA : ∀ j, (A j).ComplexityLE p ∧ (A j).normBound ≤ 1)
    (_hB : ∀ j, (B j).ComplexityLE p ∧ (B j).normBound ≤ 1)
    (_heta : ∀ j k, rationalLogHeight (eta j ((D none).basis k)) ≤ p)
    (_htheta : ∀ j k, rationalLogHeight (theta j ((D (some (.inl none))).basis k)) ≤ p)
    (_halpha : ∀ j k, rationalLogHeight (alpha j ((D (some (.inl (some j)))).basis k)) ≤ p)
    (_hbeta : ∀ j k, rationalLogHeight (beta j ((D (some (.inr j))).basis k)) ≤ p)
    (_hvertU : ∀ j z, z ∈ (D none).filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (_hvertV : ∀ j z, z ∈ (D (some (.inl none))).filtration.realification.subgroup s → ∀ x,
      (V j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (theta j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x)
    (_hvertA : ∀ j z, z ∈ (D (some (.inl (some j)))).filtration.realification.subgroup s → ∀ x,
      (A j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (alpha j) z.coord : ℝ) : CircleFourier.Circle) * (A j).observable x)
    (_hvertB : ∀ j z, z ∈ (D (some (.inr j))).filtration.realification.subgroup s → ∀ x,
      (B j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (beta j) z.coord : ℝ) : CircleFourier.Circle) * (B j).observable x)
    (weight : ∀ i, Fin (d i) → ℕ)
    (hFlayers : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ ((D i).basis '' {k | j ≤ weight i k}))
    (origin : J → σ → ℤ) (lengths : J → σ → ℕ) (_hlengths : ∀ j i, 0 < lengths j i)
    (_hbias : ∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j),
      (U j).eval x * star ((V j).eval x) * (A j).eval x * (B j).eval x‖)
    (side : σ → ℝ) (_hside : ∀ i, Real.exp ((p + C) ^ C) ≤ side i)
    (_hrelative : ∀ j i, Real.exp (-p) * side i ≤ lengths j i),
    let omega := productBasisWeight weight
    let hTotal := pi_layer_span D weight hFlayers
    let orbit := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration)
      (fun i => (anchoredOptionReferenceData P P₀ A B i).orbit)
    let g : ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
      ⟨⟨orbit.log, orbit.property⟩⟩
    let freq := fun j => piFrequency
      (selectedOrbitFrequencies (anchoredOptionFrequencyData eta theta alpha beta j) (anchoredOptionInputs j))
    ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded)
      (m : ℕ) (κ : (pi D).RealGroup)
      (E b R : ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal) omega W.toSubmodule ∧
      (∀ i k, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal).repr (v i) k) ≤
        (p + C) ^ C) ∧
      (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s → realifyFunctional (freq j) x = 0) ∧
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ κ ∈ (pi D).realLattice ∧
      E * b * R * (pi D).filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
      (∀ α i, |((pi D).basis.baseChange ℝ).repr
        (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α) i| ≤
          Real.exp ((p + C) ^ C) / monomialScale side α) ∧
      ((fun z : (σ →₀ ℕ) × Fin (Fintype.card (Σ i, Fin (d i))) => ((pi D).basis.baseChange ℝ).repr
        (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) z.1) z.2) ∈ realDenominatorGrid m) ∧
      coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
        (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
      (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) ∈
        realificationLieSubalgebra ((pi D).filtration.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨C, hC, hfactor⟩ := exists_selected_product_factorization s hs
  refine ⟨C, hC, ?_⟩
  intro J σ _ _ _ L _ _ d _ _ _ _ _ _ _ _ D P P₀ U V A B eta theta alpha beta p
    hp hcard hσ hD hU hV hA hB heta htheta halpha hbeta hvertU hvertV hvertA hvertB
    weight hFlayers origin lengths hlengths hbias side hside hrelative
  let base := anchoredOptionReferenceData P P₀ A B
  let rows := anchoredOptionObservableData U V A B
  let freq := anchoredOptionFrequencyData eta theta alpha beta
  have hJ : (Fintype.card J : ℝ) ≤ p := by
    have hh := hcard
    simp only [Fintype.card_option, Fintype.card_sum, Nat.cast_add, Nat.cast_one] at hh
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card J)]
  have horbit (j i) (_hi : i ∈ anchoredOptionInputs j) : (rows j i).orbit = (base i).orbit := by
    rcases i with _ | ((_ | k) | k)
    · exact (hU j).2.1
    · exact (hV j).2.1
    · rfl
    · rfl
  have hcomp (j i) (_hi : i ∈ anchoredOptionInputs j) : (rows j i).ComplexityLE p := by
    rcases i with _ | ((_ | k) | k)
    · exact (hU j).1
    · exact (hV j).1
    · exact (hA k).1
    · exact (hB k).1
  have hcap (j i) (_hi : i ∈ anchoredOptionInputs j) : (rows j i).normBound ≤ 1 := by
    rcases i with _ | ((_ | k) | k)
    · exact (hU j).2.2
    · exact (hV j).2.2
    · exact (hA k).2
    · exact (hB k).2
  have hheight (j i) (_hi : i ∈ anchoredOptionInputs j) (t) :
      rationalLogHeight (freq j i ((D i).basis t)) ≤ p := by
    rcases i with _ | ((_ | k) | k)
    · exact heta j t
    · change rationalLogHeight ((-theta j) ((D (some (.inl none))).basis t)) ≤ p
      simpa [rationalLogHeight] using htheta j t
    · exact halpha k t
    · exact hbeta k t
  have hvert (j i) (_hi : i ∈ anchoredOptionInputs j) (z)
      (hz : z ∈ (D i).filtration.realification.subgroup s) (x) :
      (rows j i).observable (z • x) = CircleFourier.character
        ((realifyFunctional (freq j i) z.coord : ℝ) : CircleFourier.Circle) * (rows j i).observable x := by
    rcases i with _ | ((_ | k) | k)
    · exact hvertU j z hz x
    · exact (V j).conjugate_vertical (theta j) (hvertV j) z hz x
    · exact hvertA k z hz x
    · exact hvertB k z hz x
  have hbias' (j) : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j),
      ∏ i ∈ anchoredOptionInputs j, (rows j i).eval x‖ := by
    simpa only [rows, anchoredOptionObservableData_product] using hbias j
  exact hfactor D base rows anchoredOptionInputs freq hp hcard hJ hσ hD horbit hcomp hcap hheight hvert
    weight hFlayers origin lengths hlengths hbias' side hside hrelative

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_anchored_option_mode_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {J σ : Type*} [Fintype J] [Fintype σ] [DecidableEq σ] {L : (Option (Option J ⊕ J)) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Option (Option J ⊕ J)) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (P : (D none).Niltest (fun _ : σ => 1)) (P₀ : (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (U : J → (D none).Niltest (fun _ : σ => 1)) (V : J → (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (A : ∀ j, (D (some (.inl (some j)))).Niltest (fun _ : σ => 1)) (B : ∀ j, (D (some (.inr j))).Niltest (fun _ : σ => 1))
    (eta : J → L none →ₗ[ℚ] ℚ) (theta : J → L (some (.inl none)) →ₗ[ℚ] ℚ)
    {p : ℝ} (_hp : 2 ≤ p) (_hcard : (Fintype.card (Option (Option J ⊕ J)) : ℝ) ≤ p)
    (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hD : ∀ i, (D i).GeometryComplexityLE p)
    (_hU : ∀ j, (U j).ComplexityLE p ∧ (U j).orbit = P.orbit ∧ (U j).normBound ≤ 1)
    (_hV : ∀ j, (V j).ComplexityLE p ∧ (V j).orbit = P₀.orbit ∧ (V j).normBound ≤ 1)
    (_hA : ∀ j, (A j).ComplexityLE p ∧ (A j).normBound ≤ 1)
    (_hB : ∀ j, (B j).ComplexityLE p ∧ (B j).normBound ≤ 1)
    (_heta : ∀ j k, rationalLogHeight (eta j ((D none).basis k)) ≤ p)
    (_htheta : ∀ j k, rationalLogHeight (theta j ((D (some (.inl none))).basis k)) ≤ p)
    (_hvertU : ∀ j z, z ∈ (D none).filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (_hvertV : ∀ j z, z ∈ (D (some (.inl none))).filtration.realification.subgroup s → ∀ x,
      (V j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (theta j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x)
    (weight : ∀ i, Fin (d i) → ℕ)
    (hFlayers : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ ((D i).basis '' {k | j ≤ weight i k}))
    (origin : J → σ → ℤ) (lengths : J → σ → ℕ) (_hlengths : ∀ j i, 0 < lengths j i)
    (_hbias : ∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j),
      (U j).eval x * star ((V j).eval x) * (A j).eval x * (B j).eval x‖)
    (side : σ → ℝ) (_hside : ∀ i, Real.exp ((p + C) ^ C) ≤ side i)
    (_hrelative : ∀ j i, Real.exp (-p) * side i ≤ lengths j i),
    let omega := productBasisWeight weight
    let hTotal := pi_layer_span D weight hFlayers
    ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded) (m : ℕ),
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal)
        omega W.toSubmodule ∧
      (∀ i k, rationalLogHeight
        (((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal).repr (v i) k) ≤
          (p + C) ^ C) ∧
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      HasFixedProductOrbitFactors D none
        (fun i => (anchoredOptionReferenceData P P₀ A B i).orbit) eta side ((p + C) ^ C) m W := by
  classical
  obtain ⟨c, _, hmodes⟩ := exists_native_vertical_pair_power
  obtain ⟨k, _, hfactor⟩ := exists_anchored_option_product_factorization s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C c) ^ c + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C k) ^ k)
  refine ⟨C, hC, ?_⟩
  intro J σ _ _ _ L _ _ d _ _ _ _ _ _ _ _ D P P₀ U V A B eta theta p
    hp hcard hσ hD hU hV hA hB heta htheta hvertU hvertV
    weight hFlayers origin lengths hlengths hbias side hside hrelative
  have hp0 : 0 ≤ p := by linarith
  let q := p + (p + c) ^ c + 2
  have hpow : 0 ≤ (p + c) ^ c := pow_nonneg (by positivity) _
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 2 ≤ q := by dsimp [q]; linarith
  have hmodeq : (p + c) ^ c ≤ q := by dsimp [q]; linarith
  have hbud : q + (q + k) ^ k ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp0
  have hkC : (q + k) ^ k ≤ (p + C) ^ C := by linarith
  have hsidepos (i) : 0 < side i := (Real.exp_pos _).trans_le (hside i)
  have hmodes' (j : J) := hmodes (D (some (.inl (some j)))) (D (some (.inr j)))
    (A j) (B j) p hp0 (hA j).1 (hB j).1
    (by exact_mod_cast (hA j).2) (by exact_mod_cast (hB j).2)
    (translatedIntegerBox (origin j) (lengths j))
    (by
      refine ⟨origin j, (mem_translatedIntegerBox _ _ _).mpr ?_⟩
      intro i
      have hi := hlengths j i
      constructor <;> omega)
    (fun x => x) (fun x => (U j).eval x * star ((V j).eval x))
    (by
      intro x _
      rw [norm_mul, norm_star]
      have hu : ‖(U j).eval x‖ ≤ 1 :=
        ((U j).norm_eval_le x).trans (by exact_mod_cast (hU j).2.2)
      have hv : ‖(V j).eval x‖ ≤ 1 :=
        ((V j).norm_eval_le x).trans (by exact_mod_cast (hV j).2.2)
      simpa only [one_mul] using mul_le_mul hu hv (norm_nonneg _) zero_le_one)
    (hbias j)
  choose alpha beta A' B' hAc hAo hAn hBc hBo hBn hAh hBh hAv hBv hcorr using hmodes'
  have hAcap (j) : (A' j).normBound ≤ 1 := by rw [hAn j]; exact (hA j).2
  have hBcap (j) : (B' j).normBound ≤ 1 := by rw [hBn j]; exact (hB j).2
  have hcorrq (j) : Real.exp (-q) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j),
      (U j).eval x * star ((V j).eval x) * (A' j).eval x * (B' j).eval x‖ :=
    (Real.exp_le_exp.mpr (neg_le_neg hmodeq)).trans (hcorr j)
  obtain ⟨W, v, m, κ, slow, middle, rat, hv, hW, hh, hf, hm, hmb, hκ, heq,
      hslow, hrat, hm0, hr0, hcoeff, hvalues⟩ :=
    hfactor D P P₀ U V A' B' eta theta alpha beta hq (hcard.trans hpq) (hσ.trans hpq)
      (fun i => (hD i).mono (D i) hpq)
      (fun j => ⟨(hU j).1.mono hpq, (hU j).2⟩)
      (fun j => ⟨(hV j).1.mono hpq, (hV j).2⟩)
      (fun j => ⟨(hAc j).mono hmodeq, hAcap j⟩)
      (fun j => ⟨(hBc j).mono hmodeq, hBcap j⟩)
      (fun j i => (heta j i).trans hpq) (fun j i => (htheta j i).trans hpq)
      (fun j i => (hAh j i).trans hmodeq) (fun j i => (hBh j i).trans hmodeq)
      hvertU hvertV hAv hBv weight hFlayers origin lengths hlengths hcorrq side
      (fun i => (Real.exp_le_exp.mpr hkC).trans (hside i))
      (fun j i => (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
        (hsidepos i).le).trans (hrelative j i))
  refine ⟨W, v, m, hv, hW, (fun i j => (hh i j).trans hkC), hm,
    hmb.trans (Real.exp_le_exp.mpr hkC), ?_⟩
  refine ⟨(fun j => selectedOrbitFrequencies
      (anchoredOptionFrequencyData eta theta alpha beta j) (anchoredOptionInputs j)), ?_, hf,
    κ, slow, middle, rat, hκ, ?_, ?_, hrat, hm0, hr0, hcoeff, hvalues⟩
  · intro j
    simp [selectedOrbitFrequencies, anchoredOptionFrequencyData, anchoredOptionInputs]
  · have hbase : (fun i => (anchoredOptionReferenceData P P₀ A' B' i).orbit) =
        (fun i => (anchoredOptionReferenceData P P₀ A B i).orbit) := by
      funext i
      rcases i with _ | ((_ | j) | j)
      · rfl
      · rfl
      · exact hAo j
      · exact hBo j
    simpa only [hbase] using heq
  · exact (pi D).filtration.polynomialSlowBound_mono (pi D).basis (fun _ => 1)
      side hsidepos (Real.exp_le_exp.mpr hkC) slow hslow

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_common_anchored_option_factors (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G J σ : Type*} [Fintype J] [Fintype σ] [DecidableEq σ] {L : (Option (Option J ⊕ J)) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Option (Option J ⊕ J)) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (H : Finset G) (_hH : H.Nonempty)
    (P : G → (D none).Niltest (fun _ : σ => 1)) (P₀ : (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (U : G → J → (D none).Niltest (fun _ : σ => 1)) (V : J → (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (A : ∀ j, (D (some (.inl (some j)))).Niltest (fun _ : σ => 1)) (B : G → ∀ j, (D (some (.inr j))).Niltest (fun _ : σ => 1))
    (eta : G → J → L none →ₗ[ℚ] ℚ) (theta : J → L (some (.inl none)) →ₗ[ℚ] ℚ)
    {p : ℝ} (_hp : 2 ≤ p) (_hcard : (Fintype.card (Option (Option J ⊕ J)) : ℝ) ≤ p)
    (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hD : ∀ i, (D i).GeometryComplexityLE p)
    (_hU : ∀ h ∈ H, ∀ j, (U h j).ComplexityLE p ∧ (U h j).orbit = (P h).orbit ∧ (U h j).normBound ≤ 1)
    (_hV : ∀ j, (V j).ComplexityLE p ∧ (V j).orbit = P₀.orbit ∧ (V j).normBound ≤ 1)
    (_hA : ∀ j, (A j).ComplexityLE p ∧ (A j).normBound ≤ 1)
    (_hB : ∀ h ∈ H, ∀ j, (B h j).ComplexityLE p ∧ (B h j).normBound ≤ 1)
    (_heta : ∀ h ∈ H, ∀ j k, rationalLogHeight (eta h j ((D none).basis k)) ≤ p)
    (_htheta : ∀ j k, rationalLogHeight (theta j ((D (some (.inl none))).basis k)) ≤ p)
    (_hvertU : ∀ h ∈ H, ∀ j z, z ∈ (D none).filtration.realification.subgroup s → ∀ x,
      (U h j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (eta h j) z.coord : ℝ) : CircleFourier.Circle) * (U h j).observable x)
    (_hvertV : ∀ j z, z ∈ (D (some (.inl none))).filtration.realification.subgroup s → ∀ x,
      (V j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (theta j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x)
    (_hinvariant : ∀ h ∈ H, ∀ z, z ∈ (D none).filtration.realification.subgroup s →
      (∀ j, realifyFunctional (eta h j) z.coord = 0) → ∀ x,
        (P h).observable (z • x) = (P h).observable x)
    (weight : ∀ i, Fin (d i) → ℕ)
    (hFlayers : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ ((D i).basis '' {k | j ≤ weight i k}))
    (origin : G → J → σ → ℤ) (lengths : G → J → σ → ℕ) (_hlengths : ∀ h ∈ H, ∀ j i, 0 < lengths h j i)
    (_hbias : ∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin h j) (lengths h j),
      (U h j).eval x * star ((V j).eval x) * (A j).eval x * (B h j).eval x‖)
    (side : σ → ℝ) (_hside : ∀ i, Real.exp ((p + C) ^ C) ≤ side i)
    (_hrelative : ∀ h ∈ H, ∀ j i, Real.exp (-p) * side i ≤ lengths h j i),
    let omega := productBasisWeight weight
    let hTotal := pi_layer_span D weight hFlayers
    ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded)
      (m : ℕ) (H' : Finset G),
      H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal)
        omega W.toSubmodule ∧
      (∀ i k, rationalLogHeight
        (((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal).repr (v i) k) ≤
          (p + C) ^ C) ∧
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ h ∈ H', HasFixedProductOrbitFactors D none
        (fun i => (anchoredOptionReferenceData (P h) P₀ A (B h) i).orbit)
        (eta h) side ((p + C) ^ C) m W) ∧
      ∃ freq : ({h // h ∈ H'} × J) → ∀ i, L i →ₗ[ℚ] ℚ,
        (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s →
          realifyFunctional (piFrequency (freq j)) x = 0) ∧
        (∀ h ∈ H', ∀ z, z ∈ (D none).filtration.realification.subgroup s →
          (∀ j, realifyFunctional (freq j none) z.coord = 0) → ∀ x,
            (P h).observable (z • x) = (P h).observable x) := by
  classical
  obtain ⟨c, _, hfactor⟩ := exists_anchored_option_mode_factorization s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C c) ^ c + (X + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + ((Q + 2) ^ 5 + Q))
  refine ⟨C, hC, ?_⟩
  intro G J σ _ _ _ L _ _ d _ _ _ _ _ _ _ _ D H hH P P₀ U V A B eta theta p
    hp hcard hσ hD hU hV hA hB heta htheta hvertU hvertV hinvariant
    weight hFlayers origin lengths hlengths hbias side hside hrelative
  have hp0 : 0 ≤ p := by linarith
  let q := (p + c) ^ c + (p + 2) ^ 2
  have hpow : 0 ≤ (p + c) ^ c := pow_nonneg (by positivity) _
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hfactorq : (p + c) ^ c ≤ q := le_add_of_nonneg_right (sq_nonneg _)
  have hdimq : (p + 2) ^ 2 ≤ q := le_add_of_nonneg_left hpow
  have hbud : q + ((q + 2) ^ 5 + q) ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp0
  have hqC : q ≤ (p + C) ^ C := by
    have hn : 0 ≤ (q + 2) ^ 5 := by positivity
    linarith
  have hloss : (q + 2) ^ 5 + q ≤ (p + C) ^ C := by linarith
  have hsidepos (i) : 0 < side i := (Real.exp_pos _).trans_le (hside i)
  let g := fun h i => (anchoredOptionReferenceData (P h) P₀ A (B h) i).orbit
  have hdata (h : G) (hh : h ∈ H) :
      ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
        (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded) (m : ℕ),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis
          (productBasisWeight weight) (pi_layer_span D weight hFlayers))
          (productBasisWeight weight) W.toSubmodule ∧
        (∀ i j, rationalLogHeight
          (((pi D).filtration.associatedGradedBasis (pi D).basis
            (productBasisWeight weight) (pi_layer_span D weight hFlayers)).repr (v i) j) ≤ q) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp q ∧
        HasFixedProductOrbitFactors D none (g h) (eta h) side q m W := by
    obtain ⟨W, v, m, hv, hW, hheight, hm, hmp, hf⟩ :=
      hfactor D (P h) P₀ (U h) V A (B h) (eta h) theta hp hcard hσ hD
        (hU h hh) hV hA (hB h hh) (heta h hh) htheta (hvertU h hh) hvertV
        weight hFlayers (origin h) (lengths h) (hlengths h hh) (hbias h hh) side
        (fun i => (Real.exp_le_exp.mpr (hfactorq.trans hqC)).trans (hside i)) (hrelative h hh)
    exact ⟨W, v, m, hv, hW, (fun i j => (hheight i j).trans hfactorq), hm,
      hmp.trans (Real.exp_le_exp.mpr hfactorq), hf.mono D none hfactorq hsidepos⟩
  have hdim : (Fintype.card (Σ i, Fin (d i)) : ℝ) ≤ q :=
    ((pi_geometry D hp0 hcard hD).1).trans hdimq
  obtain ⟨W, v, m, H', hsub, hnonempty, hlarge, hv, hW, hheight, hm, hmp, hf⟩ :=
    exists_common_product_orbit_factors D none weight hFlayers H hH g eta side hq0 hdim hdata
  have hf' (h : G) (hh : h ∈ H') :
      HasFixedProductOrbitFactors D none (g h) (eta h) side ((p + C) ^ C) m W :=
    (hf h hh).mono D none hqC hsidepos
  obtain ⟨freq, hfreq, hinv⟩ := exists_common_product_frequency_family D none H'
    g eta side ((p + C) ^ C) m W hf' (fun h => (P h).observable)
    (fun h hh => hinvariant h (hsub hh))
  refine ⟨W, v, m, H', hsub, hnonempty, ?_, hv, hW,
    (fun i j => (hheight i j).trans hqC), hm, hmp.trans (Real.exp_le_exp.mpr hqC),
    hf', freq, hfreq, hinv⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hloss))
    (Nat.cast_nonneg _)).trans hlarge

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

theorem exists_common_product_factors (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{u} s N q a J) {L M : Fin B.count → Type u}
      [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
      [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
      (D : ∀ j, RationalFilteredNilmanifold (L j) s (d j))
      (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))
      (w : Fin B.dim → ℕ) (v : ∀ j, Fin (d j) → ℕ) (v' : ∀ j, Fin (e j) → ℕ)
      (hw : ∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i}))
      (hv : ∀ j k, (D j).filtration.layer k = Submodule.span ℚ ((D j).basis '' {i | k ≤ v j i}))
      (hv' : ∀ j k, (E j).filtration.layer k = Submodule.span ℚ ((E j).basis '' {i | k ≤ v' j i}))
      (A : ∀ j, (D j).Niltest (fun _ : Unit => 1))
      (R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1))
      (H : Finset (ZMod N)) (h₀ : ZMod N), H ⊆ B.shifts → h₀ ∈ B.shifts →
      ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ j, (D j).GeometryComplexityLE p) → (∀ j, (E j).GeometryComplexityLE p) →
      (∀ j, (A j).ComplexityLE p ∧ (A j).normBound ≤ 1) →
      (∀ h ∈ H, ∀ j, (R h j).ComplexityLE p ∧ (R h j).normBound ≤ 1) →
      ∀ (origin : ZMod N → Fin B.count → Unit → ℤ) (lengths : ZMod N → Fin B.count → Unit → ℕ),
      (∀ h ∈ H, ∀ j i, 0 < lengths h j i) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤
        ‖𝔼 x ∈ translatedIntegerBox (origin h j) (lengths h j),
          (B.mode h j).eval x * star ((B.mode h₀ j).eval x) * (A j).eval x * (R h j).eval x‖) →
      (∀ h ∈ H, ∀ j i, Real.exp (-p) * N ≤ (lengths h j i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ N →
      let T := B.anchoredFactors D E
      let weight := B.anchoredWeights w v v'
      let hT := B.anchoredFactors_layers D E w v v' hw hv hv'
      ∃ (W : LieSubalgebra ℚ (pi T).filtration.AssociatedGraded)
        (b : Fin (Fintype.card (Σ i, Fin (B.anchoredDimension d e i))) → (pi T).filtration.AssociatedGraded)
        (m : ℕ) (H' : Finset (ZMod N)),
        H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H'.card : ℝ) ∧
        Submodule.span ℚ (Set.range b) = W.toSubmodule ∧
        BasisGradedSubmodule ((pi T).filtration.associatedGradedBasis (pi T).basis
          (productBasisWeight weight) (pi_layer_span T weight hT))
          (productBasisWeight weight) W.toSubmodule ∧
        (∀ i k, rationalLogHeight (((pi T).filtration.associatedGradedBasis (pi T).basis
          (productBasisWeight weight) (pi_layer_span T weight hT)).repr (b i) k) ≤ (p + C) ^ C) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ h ∈ H', HasFixedProductOrbitFactors T none
          (fun i => (anchoredOptionReferenceData (B.test h) (B.test h₀) A (R h) i).orbit)
          (B.frequency h) (fun _ : Unit => (N : ℝ)) ((p + C) ^ C) m W) ∧
        ∃ freq : ({h // h ∈ H'} × Fin B.count) → ∀ i, B.anchoredLieSpace L M i →ₗ[ℚ] ℚ,
          (∀ j x, x ∈ (pi T).filtration.realGradedRefiltrationLayer W s →
            realifyFunctional (piFrequency (freq j)) x = 0) ∧
          (∀ h ∈ H', ∀ z : B.model.RealGroup, z ∈ B.model.filtration.realification.subgroup s →
            (∀ j, realifyFunctional (freq j none) z.coord = 0) → ∀ x,
              (B.test h).observable (z • x) = (B.test h).observable x) := by
  classical
  obtain ⟨c, _, hfactor⟩ := exists_common_anchored_option_factors s hs
  let X : Polynomial ℕ := Polynomial.X
  let P := 2 * X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C c) ^ c + X + P)
  refine ⟨C, hC, ?_⟩
  intro N _ q a J B L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E w v v' hw hv hv' A R H h₀
    hsub hh₀ p hp hqp hH hD hE hA hR origin lengths hlengths hbias hrelative hN
  let T := B.anchoredFactors D E
  let weight := B.anchoredWeights w v v'
  have hT := B.anchoredFactors_layers D E w v v' hw hv hv'
  let : FiniteDimensional ℚ (∀ i, B.anchoredLieSpace L M i) :=
    (productFinBasis T).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, B.anchoredLieSpace L M i))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, B.anchoredLieSpace L M i))
  let := realification_moduleTopology_t2 (pi T).basis
  let t := 2 * p + 4
  have hp0 : 0 ≤ p := by linarith
  have ht : 2 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hqt : q ≤ t := hqp.trans hpt
  have hbud : (t + c) ^ c + p + t ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp0
  have hfC : (t + c) ^ c ≤ (p + C) ^ C := by linarith
  have hloss : (t + c) ^ c + p ≤ (p + C) ^ C := by linarith
  have hNm : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hHn : H.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast ((mul_pos (Real.exp_pos (-p)) hNm).trans_le hH))
  have hm : (B.count : ℝ) ≤ p := (Nat.cast_le.mpr B.count_le_dim).trans (B.geometry.1.trans hqp)
  have hcard : (Fintype.card (Option (Option (Fin B.count) ⊕ Fin B.count)) : ℝ) ≤ t := by
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    dsimp [t]
    linarith
  have hgeometry (i) : (T i).GeometryComplexityLE t :=
    (B.anchoredFactors_geometry D E hqp hD hE i).mono (T i) hpt
  obtain ⟨W, b, m, H', hHH, hH'n, hlarge, hspan, hgraded, hheight, hmpos, hmbound, hfactors, freq, hfreq, hinv⟩ :=
    hfactor T H hHn B.test (B.test h₀) B.mode (B.mode h₀) A R B.frequency (B.frequency h₀)
      ht hcard (by simpa only [Fintype.card_unit, Nat.cast_one] using (by linarith : (1 : ℝ) ≤ t))
      hgeometry
      (fun h hh j => ⟨(B.mode_complexity h (hsub hh) j).mono hqt, B.mode_orbit h (hsub hh) j, B.mode_norm h (hsub hh) j⟩)
      (fun j => ⟨(B.mode_complexity h₀ hh₀ j).mono hqt, B.mode_orbit h₀ hh₀ j, B.mode_norm h₀ hh₀ j⟩)
      (fun j => ⟨(hA j).1.mono hpt, (hA j).2⟩)
      (fun h hh j => ⟨(hR h hh j).1.mono hpt, (hR h hh j).2⟩)
      (fun h hh j i => (B.frequency_height h (hsub hh) j i).trans hqt)
      (fun j i => (B.frequency_height h₀ hh₀ j i).trans hqt)
      (fun h hh => B.mode_vertical h (hsub hh)) (B.mode_vertical h₀ hh₀)
      (fun h hh => B.test_invariant h (hsub hh)) weight hT origin lengths hlengths
      (fun h hh j => (Real.exp_le_exp.mpr (neg_le_neg hpt)).trans (hbias h hh j))
      (fun _ : Unit => (N : ℝ)) (fun _ => (Real.exp_le_exp.mpr hfC).trans hN)
      (fun h hh j i => (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpt)) hNm.le).trans
        (hrelative h hh j i))
  refine ⟨W, b, m, H', hHH, hH'n, ?_, hspan, hgraded,
    (fun i k => (hheight i k).trans hfC), hmpos, hmbound.trans (Real.exp_le_exp.mpr hfC),
    (fun h hh => (hfactors h hh).mono T none hfC (fun _ => hNm)), freq, hfreq, hinv⟩
  calc
    _ ≤ Real.exp (-((t + c) ^ c + p)) * N :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hloss)) hNm.le
    _ = Real.exp (-((t + c) ^ c)) * (Real.exp (-p) * N) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-((t + c) ^ c)) * H.card := mul_le_mul_of_nonneg_left hH (Real.exp_pos _).le
    _ ≤ H'.card := hlarge

end Erdos3.PositiveShiftBasis

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_prescribed_common_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ PrescribedCommonFactorizationSpec.{u} s C := by
  classical
  obtain ⟨c, _, hlower⟩ := exists_prescribed_lower_inputs s
  obtain ⟨k, _, hcommon⟩ := exists_common_product_factors s hs
  let X : Polynomial ℕ := Polynomial.X
  let V := (X + Polynomial.C c) ^ c
  let P := X + 2 + V
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (V + (P + Polynomial.C k) ^ k + P)
  refine ⟨C, hC, ?_⟩
  dsimp only [PrescribedCommonFactorizationSpec]
  intro N _ q a J B w hw L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ T H hH p hp hqp hsize hTc hTn χ hvert hcorr hN
  have hp0 : 0 ≤ p := by linarith
  let r := p + 2 + (p + c) ^ c
  have hV0 : 0 ≤ (p + c) ^ c := by positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hVr : (p + c) ^ c ≤ r := by dsimp [r]; linarith
  have hr : 2 ≤ r := by dsimp [r]; linarith
  have hr0 : 0 ≤ r := by linarith
  have hbud : (p + c) ^ c + (r + k) ^ k + r ≤ (p + C) ^ C := by
    simpa [V, P, X, r, Polynomial.eval₂_pow] using hbudget p hp0
  have hk0 : 0 ≤ (r + k) ^ k := by positivity
  have hVC : (p + c) ^ c ≤ (p + C) ^ C := by linarith
  have hkC : (r + k) ^ k ≤ (p + C) ^ C := by linarith
  obtain ⟨F, hFfull, hFquot, hFheight, h₀, hh₀, branches, S₀, hS₀H, hS₀n, hS₀large,
      A, R, η, γ, rSq, hA, hR, hinterval⟩ := hlower B D T H hH hp hqp hsize hTc hTn χ hvert hcorr
  let E := fun j => (F (j, true)).quotientModel
  let Q := fun j => (F (j, false)).quotientModel
  choose v hv using fun j => (F (j, true)).quotientModel_adapted
  choose v' hv' using fun j => (F (j, false)).quotientModel_adapted
  choose start len hlen hbound hshort hvol hbias using hinterval
  let origin (h : ZMod N) (j : Fin B.count) : Unit → ℤ :=
    if hh : h ∈ S₀ then fun _ => (start h hh j : ℤ) else 0
  let lengths (h : ZMod N) (j : Fin B.count) : Unit → ℕ :=
    if hh : h ∈ S₀ then fun _ => len h hh j else fun _ => 1
  have hlengths (h) (hh : h ∈ S₀) (j i) : 0 < lengths h j i := by
    simpa only [lengths, dite_eq_left hh] using hlen h hh j
  have hcorr' (h) (hh : h ∈ S₀) (j) : Real.exp (-r) ≤
      ‖𝔼 x ∈ translatedIntegerBox (origin h j) (lengths h j),
        (B.mode h j).eval x * star ((B.mode h₀ j).eval x) * (A j).eval x * (R h j).eval x‖ := by
    simpa only [origin, lengths, dite_eq_left hh] using
      (Real.exp_le_exp.mpr (neg_le_neg hVr)).trans (hbias h hh j)
  have hrelative (h) (hh : h ∈ S₀) (j i) : Real.exp (-r) * N ≤ (lengths h j i : ℝ) := by
    simpa only [lengths, dite_eq_left hh] using
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hVr)) (Nat.cast_nonneg N)).trans (hvol h hh j)
  have hsize' : Real.exp (-r) * N ≤ (S₀.card : ℝ) :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hVr)) (Nat.cast_nonneg N)).trans hS₀large
  have hRsmall (h j) : (R h j).ComplexityLE r ∧ (R h j).normBound ≤ 1 := by
    obtain ⟨_, _, _, _, hn, hc, _⟩ := hR h j
    exact ⟨hc.mono hVr, hn⟩
  obtain ⟨W, b, m, S, hSS₀, hSn, hSlarge, hspan, hgraded, hheight, hm, hmb, hfactors, freq, hfreq, hinv⟩ :=
    hcommon B E Q w v v' hw hv hv' A R S₀ h₀ (hS₀H.trans hH) (hH hh₀)
      hr (hqp.trans hpr) hsize'
      (fun j => (hFquot (j, true)).mono (E j) hVr)
      (fun j => (hFquot (j, false)).mono (Q j) hVr)
      (fun j => ⟨(hA j).2.1.mono hVr, (hA j).1⟩) (fun h _ j => hRsmall h j)
      origin lengths hlengths hcorr' hrelative ((Real.exp_le_exp.mpr hkC).trans hN)
  let G : B.CommonFactorization E Q A R h₀ H ((r + k) ^ k) := {
    weight := B.anchoredWeights w v v'
    adapted := B.anchoredFactors_layers E Q w v v' hw hv hv'
    subalgebra := W
    spanning := b
    span_eq := hspan
    graded := hgraded
    height := hheight
    denominator := m
    denominator_pos := hm
    denominator_bound := hmb
    shifts := S
    shifts_sub := hSS₀.trans hS₀H
    shifts_nonempty := hSn
    shifts_large := hSlarge
    factors := hfactors
    frequency := freq
    frequency_zero := hfreq
    invariant := hinv }
  refine ⟨F, (fun i => (hFfull i).mono (F i).fullModel hVC),
    (fun i => (hFquot i).mono (F i).quotientModel hVC),
    (fun i j l => (hFheight i j l).trans hVC), h₀, hh₀, branches, A, R, η, γ, rSq, ?_, ?_, ⟨G.mono hkC⟩⟩
  · exact fun j => ⟨(hA j).1, (hA j).2.1.mono hVC, (hA j).2.2⟩
  · intro h j
    obtain ⟨hγ, hη, hnorm, hOrbit, hn, hc, hval⟩ := hR h j
    exact ⟨hγ, (fun i => (hη i).trans (Real.exp_le_exp.mpr hVC)), hnorm, hOrbit, hn, hc.mono hVC, hval⟩

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_native_partner_contradiction (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ NativePartnerContradictionSpec s C epsilon := by
  classical
  obtain ⟨k, _, hfactor⟩ := exists_prescribed_common_factorization (s + 1) (by omega)
  obtain ⟨d, _, hcontra⟩ := exists_factored_positive_shift_contradiction s c hc hepsilon hepsilon1 hshift
  let X : Polynomial ℕ := Polynomial.X
  let V := (X + Polynomial.C k) ^ k
  let P := X + 2 + V
  let Z := (2 * P + 4) ^ 2 + P + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Z ^ d + V + P)
  refine ⟨C, hC, ?_⟩
  dsimp only [NativePartnerContradictionSpec]
  intro N _ q f₁ f₂ weight B w hw L _ _ dims _ _ _ _ D _ _ _ _ _ _ _ _ T H
    hH p hp hqp hsize hTc hTn χ hvertical hcorrelation hodd hN hf₁ hf₂ hweight hcompare
  have hp0 : 0 ≤ p := by linarith
  let v := (p + k) ^ k
  let r := p + 2 + v
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hr : 2 ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hvr : v ≤ r := by dsimp [r]; linarith
  have hbud : (productExpansionBudget r + 2) ^ d + v + r ≤ (p + C) ^ C := by
    have heq : productExpansionBudget r + 2 = (2 * r + 4) ^ 2 + r + 4 := by
      dsimp [productExpansionBudget]
      ring
    rw [heq]
    simpa [Z, P, V, X, r, v, Polynomial.eval₂_pow] using hbudget p hp0
  have hcut0 : 0 ≤ (productExpansionBudget r + 2) ^ d := by
    have := (productExpansionBudget_bounds (by linarith : 0 ≤ r)).1
    positivity
  have hvC : v ≤ (p + C) ^ C := by linarith
  have hcutC : (productExpansionBudget r + 2) ^ d ≤ (p + C) ^ C := by linarith
  obtain ⟨Y, hYfull, hYquot, hYheight, anchor, _, branches, A, R, η, γ, rSq, _, hR, ⟨F⟩⟩ :=
    hfactor B w hw D T H hH hp hqp hsize hTc hTn χ hvertical hcorrelation
      ((Real.exp_le_exp.mpr hvC).trans hN)
  let G := F.mono hvr
  have hcomparison : CyclicNiltestUpperComparison.{0} (s + 2) N ((productExpansionBudget r + 2) ^ d)
      (Real.exp (-((productExpansionBudget r + 2) ^ d))) f₁ f₂ := by
    intro K _ _ degree dim _ _ _ _ E hdegree S hS hSc
    exact (hcompare E hdegree S hS (hSc.mono hcutC)).trans
      (Real.exp_le_exp.mpr (neg_le_neg hcutC))
  exact hcontra B (fun j => (Y (j, true)).quotientModel) (fun j => D (j, false))
    (fun j => Y (j, false)) A R anchor H G hH hr (hqp.trans hpr)
    (fun j => (hYquot (j, true)).mono (Y (j, true)).quotientModel hvr)
    (fun j => (hTc (j, false)).1.mono (D (j, false)) hpr)
    (fun j => (hYfull (j, false)).mono (Y (j, false)).fullModel hvr)
    (fun j => (hYquot (j, false)).mono (Y (j, false)).quotientModel hvr)
    (fun j i l => (hYheight (j, false) i l).trans hvr)
    (fun j => (T (j, false)).orbit) branches η γ rSq
    (fun h _ j => (hR h j).1)
    (fun h _ j i => ((hR h j).2.1 i).trans (Real.exp_le_exp.mpr hvr))
    (fun h _ j => (hR h j).2.2.1) (fun h _ j => (hR h j).2.2.2.1)
    hodd ((Real.exp_le_exp.mpr hcutC).trans hN)
    (fun n => ⟨(hf₁ n).1, (hf₁ n).2.trans (Real.exp_le_exp.mpr hpr)⟩)
    (fun n => ⟨(hf₂ n).1, (hf₂ n).2.trans (Real.exp_le_exp.mpr hpr)⟩)
    (fun n => ⟨(hweight n).1, (hweight n).2.trans (Real.exp_le_exp.mpr hpr)⟩)
    hcomparison

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_native_partner_pair_contradiction (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ NativePartnerPairContradictionSpec s C epsilon := by
  classical
  obtain ⟨C, hC, hcontra⟩ := exists_native_partner_contradiction s c hc hepsilon hepsilon1 hshift
  refine ⟨C, hC, ?_⟩
  dsimp only [NativePartnerPairContradictionSpec]
  intro N _ q f₁ f₂ weight B w hw L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E V W H
    hH p hp hqp hsize hV hW hVn hWn χ χ' hχ hχ' hbias hodd hN hf₁ hf₂ hweight hcompare
  let K : Fin B.count × Bool → Type := fun j => BoolLieFamily (L j.1) (M j.1) j.2
  let dims : Fin B.count × Bool → ℕ := fun j => Bool.rec (e j.1) (d j.1) j.2
  let T : ∀ j, RationalFilteredNilmanifold (K j) (s + 1 + 1) (dims j) := fun j => by
    rcases j with ⟨j, b⟩
    cases b
    · exact E j
    · exact D j
  let U : ∀ j, (T j).Niltest (fun _ : Unit => 1) := fun j => by
    rcases j with ⟨j, b⟩
    cases b
    · exact W j
    · exact V j
  let char : ∀ j, (T j).RealGroup → CircleFourier.Circle := fun j => by
    rcases j with ⟨j, b⟩
    cases b
    · exact χ' j
    · exact χ j
  let : ∀ j, FiniteDimensional ℚ (K j) := by
    intro j
    exact (T j).basis.finiteDimensional_of_finite
  let Sq := fun j => (T j).filtration.squareLieSubalgebra
  let Qu := fun j => Sq j ⧸ (T j).filtration.squareFiltration.layerIdeal (s + 1 + 1)
  let : ∀ j, FiniteDimensional ℚ (Sq j) := fun _ => inferInstance
  let : ∀ j, FiniteDimensional ℚ (Qu j) := fun _ => inferInstance
  let : ∀ j, TopologicalSpace (ℝ ⊗[ℚ] Sq j) := fun j => moduleTopology ℝ (ℝ ⊗[ℚ] Sq j)
  let : ∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Sq j) := fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Sq j) := fun _ => inferInstance
  let : ∀ j, T2Space (ℝ ⊗[ℚ] Sq j) := fun j => realification_moduleTopology_t2 (Module.finBasis ℚ (Sq j))
  let : ∀ j, TopologicalSpace (ℝ ⊗[ℚ] Qu j) := fun j => moduleTopology ℝ (ℝ ⊗[ℚ] Qu j)
  let : ∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Qu j) := fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Qu j) := fun _ => inferInstance
  let : ∀ j, T2Space (ℝ ⊗[ℚ] Qu j) := fun j => realification_moduleTopology_t2 (Module.finBasis ℚ (Qu j))
  have hU (j) : (U j).ComplexityLE p := by
    rcases j with ⟨j, b⟩
    cases b
    · exact hW j
    · exact hV j
  have hUn (j) : (U j).normBound ≤ 1 := by
    rcases j with ⟨j, b⟩
    cases b
    · exact hWn j
    · exact hVn j
  have hchar (j z) (hz : z ∈ (T j).filtration.realification.subgroup (s + 1 + 1)) (x) :
      (U j).observable (z • x) = character (char j z) * (U j).observable x := by
    rcases j with ⟨j, b⟩
    cases b
    · exact hχ' j z hz x
    · exact hχ j z hz x
  exact hcontra B w hw T U H hH hp hqp hsize hU hUn char hchar hbias
    hodd hN hf₁ hf₂ hweight hcompare

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_two_site_model_contradiction (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ TwoSiteModelContradictionSpec s C epsilon := by
  classical
  obtain ⟨a, _, hpartners⟩ := exists_fixed_native_partners
  obtain ⟨k, _, hcontra⟩ := exists_native_partner_pair_contradiction s c hc hepsilon hepsilon1 hshift
  let X : Polynomial ℕ := Polynomial.X
  let V := (X + Polynomial.C a) ^ a
  let P := X + 2 + V
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C k) ^ k + P)
  refine ⟨C, hC, ?_⟩
  dsimp only [TwoSiteModelContradictionSpec]
  intro N _ q f₁ f₂ weight B w hw I K _ _ L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E Q R
    ea eb coeff coeff' ha hb p hp hqp hcoeff hcoeff' hQ hR hQn hRn herror hcount
    hodd hN hf₁ hf₂ hweight hcompare
  have hp0 : 0 ≤ p := by linarith
  let v := (p + a) ^ a
  let r := p + 2 + v
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hr : 2 ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hvr : v ≤ r := by dsimp [r]; linarith
  have hbud : (r + k) ^ k + r ≤ (p + C) ^ C := by
    simpa [P, V, X, r, v, Polynomial.eval₂_pow] using hbudget p hp0
  have hcut : (r + k) ^ k ≤ (p + C) ^ C := by linarith
  have hweight' (n) : |weight n| ≤ Real.exp p := by
    rw [abs_of_nonneg (hweight n).1]
    exact (hweight n).2
  obtain ⟨choice, freq, freq', V₀, W₀, H, hH, _, hsize, hV, hW, _, _, hvertV, hvertW, hbias⟩ :=
    hpartners B D E Q R ea eb coeff coeff' ha hb hqp hcoeff hcoeff' hweight' hQ hR hQn hRn herror hcount
  have hcomparison : CyclicNiltestUpperComparison.{0} (s + 2) N ((r + k) ^ k)
      (Real.exp (-((r + k) ^ k))) f₁ f₂ := by
    intro J _ _ degree dim _ _ _ _ F hdegree S hS hSc
    exact (hcompare F hdegree S hS (hSc.mono hcut)).trans
      (Real.exp_le_exp.mpr (neg_le_neg hcut))
  exact hcontra B w hw (fun j => D (choice j).1) (fun j => E (choice j).1 (choice j).2)
    V₀ W₀ H hH hr (hqp.trans hpr)
    ((mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hvr)) (Nat.cast_nonneg N)).trans hsize)
    (fun j => (hV j).1.mono hvr) (fun j => (hW j).1.mono hvr)
    (fun j => (hV j).2.2) (fun j => (hW j).2.2)
    (fun j z => ((realifyFunctional (freq j) z.coord : ℝ) : CircleFourier.Circle))
    (fun j z => ((realifyFunctional (freq' j) z.coord : ℝ) : CircleFourier.Circle))
    hvertV hvertW (fun h hh j => (Real.exp_le_exp.mpr (neg_le_neg hvr)).trans (hbias h hh j))
    hodd ((Real.exp_le_exp.mpr hcut).trans hN)
    (fun n => ⟨(hf₁ n).1, (hf₁ n).2.trans (Real.exp_le_exp.mpr hpr)⟩)
    (fun n => ⟨(hf₂ n).1, (hf₂ n).2.trans (Real.exp_le_exp.mpr hpr)⟩)
    (fun n => ⟨(hweight n).1, (hweight n).2.trans (Real.exp_le_exp.mpr hpr)⟩)
    hcomparison

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_native_detector_contradiction (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeDetectorContradictionSpec s C epsilon := by
  classical
  obtain ⟨C, hC, hcontra⟩ := exists_two_site_model_contradiction s c hc hepsilon hepsilon1 hshift
  refine ⟨C, hC, ?_⟩
  dsimp only [NativeDetectorContradictionSpec]
  intro N _ q f₁ f₂ weight B w hw p p₁ p₂ K M beta₁ beta₂ hp hp₁ hp₂ hqp hp₁p hp₂p
    hK hM hbeta₁ hbeta₂ ha hb hcoeff₁ hcoeff₂ hlength hdetect₁ hdetect₂
    hodd hN hf₁ hf₂ hweight hcompare
  have hdata := exists_shift_native_two_site_models (by omega : 1 ≤ s + 1 + 1) hp₁ hp₂
    B.testingFamily B.testingFamily_norm_le
    (fun n => ((f₁ n - (1 + epsilon) * f₂ n : ℝ) : ℂ)) (fun n => (weight n : ℂ))
    hK hM hbeta₁ hbeta₂ (Real.exp_pos _) ha hb hdetect₁ hdetect₂
  obtain ⟨n, _, f, F, coeff, ea, m, _, g, G, coeff', eb,
    hfirst, hsecond, hcoeff, hcoeff', herr, _, _, htotal⟩ := hdata
  have hvalues (i : Fin n) : (fun x => (F i).test.evalCyclic N (fun _ => x)) = f i :=
    funext (fun x => ((F i).eval x).symm)
  have herr' : shiftTestingSeminorm (fun n => (weight n : ℂ)) B.testingFamily ea +
      ∑ i, ‖coeff i‖ * shiftTestingSeminorm
        (fun x => (F i).test.evalCyclic N (fun _ => x))
        (translatedTestFamily B.testingFamily) (eb i) ≤ Real.exp (-(2 * q + 2)) := by
    simpa only [hvalues] using herr
  have htotal' : (Fintype.card (Σ i, Fin (m i)) : ℝ) ≤ Real.exp p := by
    apply htotal.trans
    simpa only [one_pow, mul_one] using hlength
  exact hcontra B w hw (fun i => (F i).model) (fun i j => (G i j).model)
    (fun i => (F i).test) (fun i j => (G i j).test) ea eb coeff coeff'
    hfirst hsecond hp hqp (hcoeff.trans hcoeff₁) (fun i => (hcoeff' i).trans hcoeff₂)
    (fun i => (F i).complexity.mono hp₁p) (fun i j => (G i j).complexity.mono hp₂p)
    (fun i => (F i).norm) (fun i j => (G i j).norm) herr' htotal'
    hodd hN hf₁ hf₂ hweight hcompare

end Erdos3.PositiveShiftBasis

end

end OAI

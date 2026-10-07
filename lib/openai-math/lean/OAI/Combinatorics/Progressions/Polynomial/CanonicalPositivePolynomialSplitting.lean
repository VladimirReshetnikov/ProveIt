/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
import OAI.Combinatorics.Progressions.Nilpotent.PositivePolynomialFactorNiltests

namespace OAI


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_positivePolynomial_source_reconstruction (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α σ L : Type*} [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [T2Space (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      (p q : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (∑ i, bound i) = t → M.ComplexityLE p → p ≤ q → (Fintype.card α : ℝ) ≤ q →
      (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q →
      M.positivePolynomialLattice p B hstable ≤
        D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) →
      (∀ c, c ≠ 0 → (∀ a, c ∉ J a) → M.filtration.layer (fun i => c i) = ⊥) →
      ∀ (u : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp q →
        (letI := D.metricSpace; LipschitzWith ℓ u) → (∀ x, ‖u x‖ ≤ 1) →
        ∃ (v : (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).Space → ℂ) (K : ℝ≥0),
          (K : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
          (letI := (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).metricSpace;
            LipschitzWith K v) ∧ (∀ y, ‖v y‖ ≤ 2) ∧
          ∀ x, v (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x)) =
            u (QuotientGroup.mk (realificationMap
              (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
              (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation x)) := by
  obtain ⟨a, _, hrec⟩ := exists_positivePolynomial_product_reconstruction t
  let P : Polynomial ℕ := (Polynomial.X + (Polynomial.X + 3) ^ 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro α σ L _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ _ _ _ _ p q B hB hstable
    ht hM hpq hα hX hmap hcover u ℓ hℓ hu hub
  let r := q + (q + 3) ^ 2
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hX.1
  have hqr : q ≤ r := le_add_of_nonneg_right (sq_nonneg _)
  let u₀ := u ∘ M.positivePolynomialEvaluationCosetMap p B hB hstable hmap
  obtain ⟨K₀, hK₀, hu₀⟩ := M.exists_positivePolynomial_observable_pullback hM hpq hX.1
    B hB hstable hmap u ℓ hℓ hu
  have hub₀ : ∀ x, ‖u₀ x‖ ≤ 1 := fun x => hub _
  obtain ⟨v, K, hK, hv, hb, heval⟩ := hrec M J hJ p r B hB hstable ht (hα.trans hqr)
    (hX.mono _ hqr) hcover u₀ K₀ hK₀ hu₀ hub₀
  have hcost : (r + a) ^ a ≤ (q + C) ^ C := by
    simpa [P, r, Polynomial.eval₂_pow] using hbudget q hq
  refine ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv, hb, ?_⟩
  intro x
  simpa only [u₀, Function.comp_apply, M.positivePolynomialEvaluationCosetMap_mk] using heval x

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_positivePolynomial_factor_approximation (t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α σ L : Type*} [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      (p q : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (∑ i, bound i) = t → M.ComplexityLE p → p ≤ q → (Fintype.card α : ℝ) ≤ q →
      (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q →
      M.positivePolynomialLattice p B hstable ≤ D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((q + 2) ^ a) →
      let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
      letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((q + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((q + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (E i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (u : D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp q →
              (letI := D.metricSpace; LipschitzWith ell u) → (∀ x, ‖u x‖ ≤ 1) →
              ∃ c : (∀ i, Fin (n i)) → ℂ, (∀ j, ‖c j‖ ≤ 2) ∧
                ∀ x, ‖u (QuotientGroup.mk (realificationMap
                    (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
                    (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation x)) -
                  ∑ j, (∏ i, (ψ i (j i) (productProjection E i
                    (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x))) : ℂ)) * c j‖ ≤ epsilon := by
  obtain ⟨b, _, hrec⟩ := exists_positivePolynomial_source_reconstruction t
  obtain ⟨c, _, happ⟩ := exists_controlled_native_product_approximation t a b
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C b + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro α σ L _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    p q B hB hstable ht hM hpq hα hX hmap hcover epsilon hepsilon hscale
  subst t
  let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  let := (pi E).metricSpace
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hX.1
  let R := q + b
  have hqR : q ≤ R := le_add_of_nonneg_right (Nat.cast_nonneg b)
  have hR : 0 ≤ R := hq.trans hqR
  have hscaleR : 1 / epsilon ≤ Real.exp ((R + 2) ^ a) :=
    hscale.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) a))
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, happrox⟩ := happ E hR (hα.trans hqR)
    (fun i => ((M.positivePolynomialDownsetModel_complexity (J i) (hJ i) p q B hB hstable hX).1).mono (E i) hqR)
    hepsilon hscaleR
  have hcost : (R + c) ^ c ≤ (q + C) ^ C := by
    simpa [P, R, Polynomial.eval₂_pow] using hbudget q hq
  have hexp := Real.exp_le_exp.mpr hcost
  refine ⟨n, hn, fun i => (hnb i).trans hexp, hcount.trans hexp,
    K, fun i => (hKb i).trans hexp, ψ, hunit, hsum, hLip, ?_⟩
  intro u ell hell hu hub
  obtain ⟨v, Kv, hKv, hv, hvb, heval⟩ := hrec M J hJ p q B hB hstable rfl hM hpq hα hX hmap hcover u ell hell hu hub
  have hKvR : (Kv : ℝ) ≤ Real.exp ((R + 2) ^ b) :=
    hKv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hR (by linarith) b))
  obtain ⟨coeff, hcoeff, herr⟩ := happrox v Kv hKvR hv hvb
  refine ⟨coeff, hcoeff, fun x => ?_⟩
  have h := herr (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x))
  convert h using 1
  congr 2
  exact (heval x).symm

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_positivePolynomial_vector_factor_approximation (t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      (p q : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (∑ i, bound i) = t → M.ComplexityLE p → p ≤ q → (Fintype.card α : ℝ) ≤ q →
      (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q →
      M.positivePolynomialLattice p B hstable ≤ D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((q + 2) ^ a) →
      (Fintype.card I : ℝ) ≤ Real.exp q →
      let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
      letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((q + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((q + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (E i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (u : I → D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp q →
              (letI := D.metricSpace; ∀ k, LipschitzWith ell (u k)) →
              (∀ k x, ‖u k x‖ ≤ 1) →
              ∃ c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I,
                (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ Real.exp (q + 2)) ∧
                ∀ x, ‖(WithLp.toLp 2 (fun k => u k (QuotientGroup.mk (realificationMap
                    (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
                    (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation x))) : EuclideanSpace ℂ I) -
                  ∑ j, (∏ i, (ψ i (j i) (productProjection E i
                    (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x))) : ℂ)) • c j‖ ≤ epsilon := by
  obtain ⟨C, hC, happ⟩ := exists_positivePolynomial_factor_approximation t (a + 1)
  refine ⟨C, hC, ?_⟩
  intro I α σ L _ _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    p q B hB hstable ht hM hpq hα hX hmap hcover epsilon hepsilon hscale hI
  classical
  let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hX.1
  obtain ⟨hprecision, hprecision_scale⟩ := vector_approximation_precision a hq hI hepsilon hscale
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, happrox⟩ :=
    happ M J hJ p q B hB hstable ht hM hpq hα hX hmap hcover
      (epsilon / (Fintype.card I + 1 : ℝ)) hprecision hprecision_scale
  refine ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, ?_⟩
  intro u ell hell hu hub
  choose coeff hcoeff herr using (fun k => happrox (u k) ell hell (hu k) (hub k))
  let c (j : ∀ i, Fin (n i)) : EuclideanSpace ℂ I := WithLp.toLp 2 (fun k => coeff k j)
  have hc : ∀ j k, ‖c j k‖ ≤ 2 := fun j k => hcoeff k j
  refine ⟨c, hc, fun j => euclidean_coefficient_norm_le_exp hq hI (c j) (hc j), ?_⟩
  intro x
  apply euclidean_error_le_of_coordinate_errors _ hepsilon.le
  intro k
  simpa only [PiLp.sub_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, c, WithLp.ofLp_toLp] using herr k x

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_uniform_positivePolynomial_splitting (t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (Fintype.card α : ℝ) ≤ p + 2 →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      M.filtration.realification.polynomialOrbitEval 0 g = 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
        (∀ i, (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) p B hB hstable).ComplexityLE ((p + C) ^ C)) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∃ n : α → ℕ, (∀ i, 0 < n i) ∧
            (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
            (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            ∃ T : ∀ i, Fin (n i) → (M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable).Niltest (fun _ : σ => 1),
              (∀ i j, (T i j).normBound = 1) ∧ (∀ i j, (T i j).UnitIntervalValued) ∧
              (∀ i j, (T i j).ComplexityLE ((p + C) ^ C)) ∧
              (∀ i j, (T i j).orbit =
                (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) p B hB hstable).orbitToOrdinary
                  (M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h)) ∧
              ∀ (u : I → D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
                (letI := D.metricSpace; ∀ k, LipschitzWith ell (u k)) →
                (∀ k x, ‖u k x‖ ≤ 1) →
                ∃ c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I,
                  (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ Real.exp ((p + C) ^ C)) ∧
                  ∀ x, ‖(WithLp.toLp 2 (fun k => u k
                      (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))) : EuclideanSpace ℂ I) -
                    ∑ j, (∏ i, (T i (j i)).eval x) • c j‖ ≤ epsilon := by
  let hmodels_exists := exists_positivePolynomial_model_uniform t
  let b := hmodels_exists.choose
  have hmodels := hmodels_exists.choose_spec
  let happ_exists := exists_positivePolynomial_vector_factor_approximation t a
  let c := happ_exists.choose
  have happ := happ_exists.choose_spec
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b + 2
  let P : Polynomial ℕ := Q + (Q + Polynomial.C c) ^ c + 2
  let hbudget_exists := exists_natPolynomial_eval_budget P
  let C := hbudget_exists.choose
  have hC : 2 ≤ C := hbudget_exists.choose_spec.1
  have hbudget : ∀ p : ℝ, 0 ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C := hbudget_exists.choose_spec.2
  refine ⟨C, hC, ?_⟩
  intro I α σ L _ _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    p ht hM hα hcover g hg epsilon hepsilon hscale hI
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let q := p + (p + b) ^ b + 2
  have hmodel_nonneg : 0 ≤ (p + b) ^ b := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith only [hmodel_nonneg]
  have hq : 0 ≤ q := hp.trans hpq
  have hαq : (Fintype.card α : ℝ) ≤ q := by dsimp [q]; linarith only [hα, hmodel_nonneg]
  have hcost : q + (q + c) ^ c + 2 ≤ (p + C) ^ C := by
    simpa [P, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (q + c) ^ c := by positivity
  have hpower_cost : (q + c) ^ c ≤ (p + C) ^ C := by linarith only [hcost, hq]
  have hq_cost : q + 2 ≤ (p + C) ^ C := by linarith only [hcost, hpow]
  let model := hmodels.2 M ht hM
  let B := model.choose
  let hB : 0 < B := model.choose_spec.choose
  let hstable : M.PositivePolynomialGridStable p B := model.choose_spec.choose_spec.choose
  have hmodel := model.choose_spec.choose_spec.choose_spec.1
  have hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) :=
    model.choose_spec.choose_spec.choose_spec.2
  have hX : (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q :=
    (hmodel.mono _ (by dsimp [q]; linarith only [hp])).1
  let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  have hE (i) := M.positivePolynomialDownsetModel_complexity (J i) (hJ i) p q B hB hstable hX
  let lift := M.filtration.exists_realPositivePolynomial_orbit g hg
  let h := lift.choose
  have hh := lift.choose_spec.1
  have hproj := lift.choose_spec.2
  have hscaleq : 1 / epsilon ≤ Real.exp ((q + 2) ^ a) :=
    hscale.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith only [hp]) (by linarith only [hpq]) a))
  have hIq : (Fintype.card I : ℝ) ≤ Real.exp q := hI.trans (Real.exp_le_exp.mpr hpq)
  let approximation :=
    happ.2 M J hJ p q B hB hstable ht hM hpq hαq hX hmap hcover epsilon hepsilon hscaleq hIq
  let n := approximation.choose
  have hn := approximation.choose_spec.1
  have hnb := approximation.choose_spec.2.1
  have hcount := approximation.choose_spec.2.2.1
  let constants := approximation.choose_spec.2.2.2
  let K := constants.choose
  have hKb := constants.choose_spec.1
  let factors := constants.choose_spec.2
  let ψ := factors.choose
  have hunit := factors.choose_spec.1
  have hsum := factors.choose_spec.2.1
  have hLip := factors.choose_spec.2.2.1
  have happrox := factors.choose_spec.2.2.2
  let T (i) (j : Fin (n i)) :=
    M.positivePolynomialFactorNiltest (J i) (hJ i) p B hB hstable h (ψ i j) (hunit i j) (K i) (hLip i j)
  have hT (i) (j : Fin (n i)) : (T i j).ComplexityLE ((p + C) ^ C) := by
    have hgeometry := (hE i).1.mono (E i) (le_add_of_nonneg_right hpow)
    have hK : (K i : ℝ) ≤ Real.exp (q + (q + c) ^ c) :=
      (hKb i).trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hq))
    exact (M.positivePolynomialFactorNiltest_complexity (J i) (hJ i) p B hB hstable h
      (ψ i j) (hunit i j) (K i) (hLip i j) hgeometry hK).mono hcost
  refine ⟨B, hB, hstable, fun i => (hE i).mono _ (by linarith only [hq_cost]), h, hh, n, hn,
    fun i => (hnb i).trans (Real.exp_le_exp.mpr hpower_cost),
    hcount.trans (Real.exp_le_exp.mpr hpower_cost), T, fun _ _ => rfl,
    fun i j => M.positivePolynomialFactorNiltest_unit_interval (J i) (hJ i) p B hB hstable h
      (ψ i j) (hunit i j) (K i) (hLip i j), hT, fun _ _ => rfl, ?_⟩
  intro u ell hell hu hub
  let coefficients := happrox u ell (hell.trans (Real.exp_le_exp.mpr hpq)) hu hub
  let coeff := coefficients.choose
  have hcoeff := coefficients.choose_spec.1
  have hcoeffnorm := coefficients.choose_spec.2.1
  have herr := coefficients.choose_spec.2.2
  refine ⟨coeff, hcoeff, fun j => (hcoeffnorm j).trans (Real.exp_le_exp.mpr hq_cost), ?_⟩
  have horbit := M.positivePolynomial_vector_error_of_lift J hJ p B hB hstable g h hproj
    n ψ coeff u epsilon herr
  intro x
  simpa only [T, M.positivePolynomialFactorNiltest_eval] using horbit x

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_canonical_positivePolynomial_splitting (t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (Fintype.card α : ℝ) ≤ p + 2 →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      M.filtration.realification.polynomialOrbitEval 0 g = 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      letI : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun _ => moduleTopology ℝ _
      letI : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun _ => IsModuleTopology.topologicalAddGroup ℝ _
      letI : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
        (∀ i, (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) p B hB hstable).ComplexityLE ((p + C) ^ C)) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∃ n : α → ℕ, (∀ i, 0 < n i) ∧
            (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
            (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            ∃ T : ∀ i, Fin (n i) → (M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable).Niltest (fun _ : σ => 1),
              (∀ i j, (T i j).normBound = 1) ∧ (∀ i j, (T i j).UnitIntervalValued) ∧
              (∀ i j, (T i j).ComplexityLE ((p + C) ^ C)) ∧
              (∀ i j, (T i j).orbit =
                (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) p B hB hstable).orbitToOrdinary
                  (M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h)) ∧
              ∀ (u : I → D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
                (letI := D.metricSpace; ∀ k, LipschitzWith ell (u k)) →
                (∀ k x, ‖u k x‖ ≤ 1) →
                ∃ c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I,
                  (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ Real.exp ((p + C) ^ C)) ∧
                  ∀ x, ‖(WithLp.toLp 2 (fun k => u k
                      (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))) : EuclideanSpace ℂ I) -
                    ∑ j, (∏ i, (T i (j i)).eval x) • c j‖ ≤ epsilon := by
  obtain ⟨C, hC, hsplit⟩ := exists_uniform_positivePolynomial_splitting t a
  refine ⟨C, hC, ?_⟩
  intro I α σ L _ _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _
    p ht hM hα hcover g hg epsilon hepsilon hscale hI
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) := fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra) :=
    realification_moduleTopology_t2 (M.positivePolynomialFinBasis p)
  let : ∀ i, FiniteDimensional ℚ (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)) :=
    fun i => (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
    restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    realification_moduleTopology_t2 (Module.finBasis ℚ _)
  exact hsplit M J hJ p ht hM hα hcover g hg epsilon hepsilon hscale hI

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end OAI

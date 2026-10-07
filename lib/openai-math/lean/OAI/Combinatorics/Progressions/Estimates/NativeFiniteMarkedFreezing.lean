import OAI.Combinatorics.Progressions.Polynomial.NativeMarkedPolynomialFreezing

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest
open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ I J L M : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem observable_common_frozenMarked_family
    (T : D.Niltest w) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ G.layer j)
    (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse S φ)
    (g E P R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (hfac : E * P * R = g)
    (EF RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (left : I → D.RealGroup) (right : J → D.RealGroup)
    (hleft : ∀ i, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ (left i) = 1)
    (hright : ∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ (right j) = 1)
    (Q M₀ : ℕ) (hQ : 0 < Q) (sides : σ → ℝ) (hsides : ∀ i, 0 < sides i)
    (leftLabel : (σ → Fin (Q + 1)) → I) (rightLabel : (σ → ZMod M₀) → J)
    (ε : ℝ)
    (hslow :
      letI := rightMetricSpace
        (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      ∀ j (v : σ → ℝ), (∀ i, |v i| ≤ sides i) →
        (∀ i, |v i - normalizedRealBoxGrid sides Q j i| ≤ sides i * (2 / Q)) →
        dist (D.filtration.adaptedPolynomialRealValueHom w v
          (E * (D.filtration.filteredRealPolynomialSection G w S hS EF)⁻¹))
          (left (leftLabel j)) ≤ ε)
    (hrational : ∀ x : σ → ℤ, ∃ γ ∈ D.realLattice,
      D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ))
        ((D.filtration.filteredRealPolynomialSection G w S hS RF)⁻¹ * R) =
        right (rightLabel (fun i => (x i : ZMod M₀))) * γ) :
    (∀ i j,
      D.filtration.realPolynomialGroupMap G φ hφ w
        (D.filtration.frozenMarkedLeft G w S hS EF (left i)) = EF ∧
      D.filtration.realPolynomialGroupMap G φ hφ w
        (D.filtration.frozenMarkedRight G w S hS RF (right j)) = RF) ∧
    ∀ x : σ → ℤ, (∀ i, |(x i : ℝ)| ≤ sides i) →
      ∃ j : σ → Fin (Q + 1),
        (∀ i, |(x i : ℝ) - normalizedRealBoxGrid sides Q j i| ≤ sides i * (2 / Q)) ∧
        ‖T.observable (QuotientGroup.mk
            (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) g)) -
          T.observable (QuotientGroup.mk
            (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ))
              (D.filtration.frozenMarkedLeft G w S hS EF (left (leftLabel j)) * P *
                D.filtration.frozenMarkedRight G w S hS RF
                  (right (rightLabel (fun i => (x i : ZMod M₀)))))))‖ ≤
          (T.lipBound : ℝ) * ε := by
  refine ⟨fun i j => D.filtration.frozenMarked_factors_mark G w φ hφ S hS hsection
    EF RF (left i) (right j) (hleft i) (hright j), ?_⟩
  intro x hx
  obtain ⟨j, hj⟩ := exists_normalizedRealBoxGrid_cell sides hsides hQ (fun i => (x i : ℝ)) hx
  refine ⟨j, hj, ?_⟩
  obtain ⟨γ, hγ, hfacR⟩ := hrational x
  have hcoset : (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
      (fun i => (x i : ℝ)) ((D.filtration.filteredRealPolynomialSection G w S hS RF)⁻¹ * R)) :
      D.Space) = QuotientGroup.mk (right (rightLabel (fun i => (x i : ZMod M₀)))) := by
    rw [hfacR]
    exact QuotientGroup.mk_mul_of_mem _ hγ
  exact (T.observable_frozenMarked_polynomial_factors G φ S hS hsection g E P R hfac EF RF
    (left (leftLabel j)) (right (rightLabel (fun i => (x i : ZMod M₀))))
    (hleft _) (hright _) (fun i => (x i : ℝ)) hcoset).trans
      (mul_le_mul_of_nonneg_left (hslow j _ hx hj) (NNReal.coe_nonneg _))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

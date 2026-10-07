import OAI.Combinatorics.Progressions.Estimates.AllocatedLongMixedCoefficientBound

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

include hσ1 C hC hchart hsmall

theorem allocatedCoefficientDensity_polynomial_decomposition
    (c : CoefficientArray (K := LayerSamplerVariables G I n B) U)
    (hc : allocatedCoefficientDensity B U b hb o hR hσ S
      (QuotientAddGroup.mk' (coefficientIntegerLattice U) c) ≠ 0) :
    ∃ Y : ∀ j, J j → MvPolynomial (LayerSamplerVariables G I n B) ℝ,
    ∃ β : ∀ j, J j → MvPolynomial (LayerSamplerVariables G I n B) ℤ,
      (∀ j i, coefficientRowPolynomial U c j i = Y j i + MvPolynomial.map (Int.castRingHom ℝ) (β j i)) ∧
      (∀ j i, (Y j i).totalDegree ≤ j.val + 1) ∧
      (∀ j i, (β j i).totalDegree ≤ j.val + 1) ∧
      (∀ j i α, |(Y j i).coeff α| ≤ (1 / 4 : ℝ) / monomialScale (layerSamplerBox B U b S) α) ∧
      (∀ j (x : LayerSamplerVariables G I n B → ℝ),
        (∀ v, |x v| ≤ layerSamplerBox B U b S v) → ∀ i, |MvPolynomial.eval x (Y j i)| < 1 / 2) := by
  obtain ⟨a, ha, _⟩ := allocatedCoefficientDensity_recover B U b hb o hR hσ S hσ1 C hC hchart hsmall hc
  obtain ⟨β, hβ⟩ := canonicalCoefficientSample_polynomial_remainder U b hb o a c ha.1.1
  refine ⟨fun j i => mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (a j) i,
    β, fun j i => (hβ j i).1, ?_, fun j i => (hβ j i).2, ?_, ?_⟩
  · intro j i
    exact mixedLiftPolynomial_degree _ (b j) (o j) Subtype.val (a j) (fun d => d.property) i
  · intro j i α
    exact allocatedLayerLiftPolynomial_coefficient_bound B U b hR hσ S hσ1 o C hC hchart hsmall
      j (a j) (ha.1.2 j).2 α i
  · intro j x hx i
    rw [mixedLiftPolynomial_eval]
    exact ha.2 j x hx i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

include hσ1 C hC hchart hsmall in
theorem allocatedLayerSupported_polynomial_quarter (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j) (allocatedLayerWidths B U b S j)
      (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (x : LayerSamplerVariables G I n B → ℝ) (hx : ∀ v, |x v| ≤ layerSamplerBox B U b S v)
    (i : J j) :
    |mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x i| < 1/4 := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have hs := (allocatedArraySupported_iff_rows Subtype.val (layerSamplerBox B U b S)
    (layerContinuousPrincipalSlots B j) (constantCoefficientSlot _ _) (R j) (σ j)
    (allocatedLayerIntegerPMFs B U b hR hσ S j) a).mp ha
  have hu (k : I j) :
      |MvPolynomial.eval x (monomialArrayPolynomial Subtype.val (a.1 k))| ≤ 3 * R j / 4 :=
    continuousPolynomialDensity_box Subtype.val _ hT _ _
      (layerContinuousPrincipalSlots_not_constant B j k) (hR j) (hσ j) (hσ1 j) (hs.1 k) x hx
  have hz (k : Fin (n j)) :
      |MvPolynomial.eval x (monomialArrayPolynomial Subtype.val
        (fun d => (a.2 k d : ℝ) / basisAxisScale (b j) k))| ≤ 3 * R j / 4 :=
    allocatedIntegerPolynomial_box (layerIntegerPrincipalSlots B j k) (constantCoefficientSlot _ _)
      (j.val + 1) (basisAxisScale (b j) k) S.value (layerTailDegree m) (Nat.zero_lt_succ _)
      (basisAxisScale_pos (b j) k) S.positive (layerSamplerBox B U b S) hT
      (layerSamplerBox_le B U b S) Subtype.val
      (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (S.gap j k) (S.width j)
      (layerIntegerPrincipalSlots_not_constant B j k) rfl (hσ1 j)
      (layerSamplerSides_integer_principal B U b R S.value j k) (a.2 k) (hs.2 k) x hx
  have hn := mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j) (hC j)
    (div_nonneg (mul_nonneg (by norm_num) (hR j).le) (by norm_num)) (hchart j) _ _ hu hz
  change ‖mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x‖ ≤
    C j * (((Fintype.card (I j) : ℝ) + 1) * (3 * R j / 4)) at hn
  have hm : C j * (((Fintype.card (I j) : ℝ) + 1) * (3 * R j / 4)) ≤ 3/16 := by
    nlinarith only [hsmall j]
  have hi : |mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x i| ≤
      ‖mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x‖ := by
    simpa only [Real.norm_eq_abs] using
      PiLp.norm_apply_le (mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x) i
  exact (hi.trans (hn.trans hm)).trans_lt (by norm_num)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

include hσ1 C hC hchart hsmall in
theorem allocatedCoefficientDensity_quarter_decomposition
    (c : CoefficientArray (K := LayerSamplerVariables G I n B) U)
    (hc : allocatedCoefficientDensity B U b hb o hR hσ S
      (QuotientAddGroup.mk' (coefficientIntegerLattice U) c) ≠ 0) :
    ∃ Y : ∀ j, J j → MvPolynomial (LayerSamplerVariables G I n B) ℝ,
    ∃ β : ∀ j, J j → MvPolynomial (LayerSamplerVariables G I n B) ℤ,
      (∀ j i, coefficientRowPolynomial U c j i = Y j i + MvPolynomial.map (Int.castRingHom ℝ) (β j i)) ∧
      (∀ j i, (Y j i).totalDegree ≤ j.val + 1) ∧
      (∀ j i, (β j i).totalDegree ≤ j.val + 1) ∧
      (∀ j i α, |(Y j i).coeff α| ≤ (1 / 4 : ℝ) / monomialScale (layerSamplerBox B U b S) α) ∧
      (∀ j (x : LayerSamplerVariables G I n B → ℝ),
        (∀ v, |x v| ≤ layerSamplerBox B U b S v) → ∀ i, |MvPolynomial.eval x (Y j i)| < 1 / 4) := by
  obtain ⟨a, ha, _⟩ := allocatedCoefficientDensity_recover B U b hb o hR hσ S hσ1 C hC hchart hsmall hc
  obtain ⟨β, hβ⟩ := canonicalCoefficientSample_polynomial_remainder U b hb o a c ha.1.1
  refine ⟨fun j i => mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (a j) i,
    β, fun j i => (hβ j i).1, ?_, fun j i => (hβ j i).2, ?_, ?_⟩
  · intro j i
    exact mixedLiftPolynomial_degree _ (b j) (o j) Subtype.val (a j) (fun d => d.property) i
  · intro j i α
    exact allocatedLayerLiftPolynomial_coefficient_bound B U b hR hσ S hσ1 o C hC hchart hsmall
      j (a j) (ha.1.2 j).2 α i
  · intro j x hx i
    rw [mixedLiftPolynomial_eval]
    exact allocatedLayerSupported_polynomial_quarter B U b hR hσ S hσ1 o C hC hchart hsmall
      j (a j) (ha.1.2 j).2 x hx i

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Polynomial.IntegerPolynomialDenominatorGrid
import OAI.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ τ : Type*}

theorem weightedHomogeneousComponent_fractional_restoration
    (F : MvPolynomial σ ℝ) (w : σ → ℕ) (d : ℕ) :
    weightedHomogeneousComponent w d F =
      weightedHomogeneousComponent w d (fractionalCoefficientPolynomial F) +
        MvPolynomial.map (Int.castRingHom ℝ)
          (weightedHomogeneousComponent w d (floorIntegerPolynomial F)) := by
  classical
  conv_lhs => rw [← floorIntegerPolynomial_add_fractionalCoefficientPolynomial F]
  rw [map_add, add_comm]
  congr 1
  ext a
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp

noncomputable def restoredMajorRemainder (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (R : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  R + MvPolynomial.map (Int.castRingHom ℚ)
    (weightedHomogeneousComponent w d (floorIntegerPolynomial F))

theorem restoredMajorRemainder_coefficientGrid (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (R : MvPolynomial σ ℚ) (q : ℕ)
    (hR : (fun a => R.coeff a) ∈ denominatorGrid q) :
    (fun a => (restoredMajorRemainder F w d R).coeff a) ∈ denominatorGrid q :=
  add_integerPolynomial_coefficientGrid R
    (weightedHomogeneousComponent w d (floorIntegerPolynomial F)) q hR

theorem integerPolynomial_map_rat_real (I : MvPolynomial σ ℤ) :
    MvPolynomial.map (algebraMap ℚ ℝ) (MvPolynomial.map (Int.castRingHom ℚ) I) =
      MvPolynomial.map (Int.castRingHom ℝ) I := by
  ext a
  simp only [coeff_map]
  simp

theorem restoredMajorRemainder_eval (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (R : MvPolynomial σ ℚ) (z : σ → ℝ) :
    eval₂ (algebraMap ℚ ℝ) z (restoredMajorRemainder F w d R) =
      eval₂ (algebraMap ℚ ℝ) z R +
        eval z (MvPolynomial.map (Int.castRingHom ℝ)
          (weightedHomogeneousComponent w d (floorIntegerPolynomial F))) := by
  rw [restoredMajorRemainder, eval₂_add]
  congr 1
  rw [← eval_map, integerPolynomial_map_rat_real]

theorem restoredMajorRemainder_isWeightedHomogeneous (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (R : MvPolynomial σ ℚ)
    (hR : R.IsWeightedHomogeneous w d) :
    (restoredMajorRemainder F w d R).IsWeightedHomogeneous w d := by
  apply hR.add
  intro a ha
  apply weightedHomogeneousComponent_isWeightedHomogeneous
    (w := w) d (floorIntegerPolynomial F)
  intro hz
  apply ha
  simp only [coeff_map, hz, map_zero]

theorem restoredMajorRemainder_degree (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (R : MvPolynomial σ ℚ)
    (hR : R ∈ weightedSupportLE w d) :
    restoredMajorRemainder F w d R ∈ weightedSupportLE w d := by
  apply (weightedSupportLE w d).add_mem hR
  intro a ha
  have hi : (MvPolynomial.map (Int.castRingHom ℚ)
      (weightedHomogeneousComponent w d (floorIntegerPolynomial F))).IsWeightedHomogeneous w d := by
    intro a ha
    apply weightedHomogeneousComponent_isWeightedHomogeneous
      (w := w) d (floorIntegerPolynomial F)
    intro hz
    apply ha
    simp only [coeff_map, hz, map_zero]
  exact (hi (mem_support_iff.mp ha)).le

theorem restoredMajorRemainder_totalDegree_le (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ) (R : MvPolynomial σ ℚ)
    {r : ℕ} (hR : R.totalDegree ≤ r) (hdr : d ≤ r) :
    (restoredMajorRemainder F w d R).totalDegree ≤ r := by
  have hI : MvPolynomial.map (Int.castRingHom ℚ)
      (weightedHomogeneousComponent w d (floorIntegerPolynomial F)) ∈
        weightedSupportLE w d := by
    simpa only [restoredMajorRemainder, zero_add] using
      restoredMajorRemainder_degree F w d 0 (Submodule.zero_mem _)
  have hdeg : (MvPolynomial.map (Int.castRingHom ℚ)
      (weightedHomogeneousComponent w d (floorIntegerPolynomial F))).totalDegree ≤ d := by
    unfold totalDegree
    apply Finset.sup_le
    intro a ha
    exact (exponentSum_le_positive_weight w hw a).trans (hI ha)
  exact (totalDegree_add _ _).trans (max_le hR (hdeg.trans hdr))

theorem algebraic_major_integer_restoration_identity
    (F : MvPolynomial σ ℝ) (w : σ → ℕ) (d : ℕ)
    (S : MvPolynomial τ ℝ) (R : MvPolynomial σ ℚ)
    (chart : (σ → ℝ) → (τ → ℝ)) (Ω : Set (σ → ℝ))
    (hidentity : ∀ z ∈ Ω,
      eval z (weightedHomogeneousComponent w d (fractionalCoefficientPolynomial F)) =
        eval (chart z) S + eval₂ (algebraMap ℚ ℝ) z R)
    (z : σ → ℝ) (hz : z ∈ Ω) :
    eval z (weightedHomogeneousComponent w d F) =
      eval (chart z) S + eval₂ (algebraMap ℚ ℝ) z (restoredMajorRemainder F w d R) := by
  rw [weightedHomogeneousComponent_fractional_restoration, map_add, hidentity z hz,
    restoredMajorRemainder_eval, add_assoc]

theorem algebraic_major_restore_integer_coefficients
    {U B : Type*} (F : MvPolynomial (U ⊕ B) ℝ)
    (w : U ⊕ B → ℕ) (d : ℕ) (K : Submodule ℝ (B → ℝ))
    (A : B → MvPolynomial U ℝ) (H : U → ℝ)
    (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ) (q : ℕ)
    (hgrid : (fun a => R.coeff a) ∈ denominatorGrid q)
    (hdegree : R ∈ weightedSupportLE w d)
    (hidentity : ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b)
          (weightedHomogeneousComponent w d (fractionalCoefficientPolynomial F)) =
        eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R) :
    let R' := restoredMajorRemainder F w d R
    (fun a => R'.coeff a) ∈ denominatorGrid q ∧ R' ∈ weightedSupportLE w d ∧
      ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
        eval (Sum.elim u b) (weightedHomogeneousComponent w d F) =
          eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S +
            eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R' := by
  refine ⟨restoredMajorRemainder_coefficientGrid F w d R q hgrid,
    restoredMajorRemainder_degree F w d R hdegree, ?_⟩
  intro u b hb
  rw [weightedHomogeneousComponent_fractional_restoration, map_add, hidentity u b hb,
    restoredMajorRemainder_eval, add_assoc]

theorem algebraic_major_restore_integer_coefficients_totalDegree
    {U B : Type*} (F : MvPolynomial (U ⊕ B) ℝ)
    (w : U ⊕ B → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ)
    (K : Submodule ℝ (B → ℝ)) (A : B → MvPolynomial U ℝ) (H : U → ℝ)
    (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ) (q r : ℕ)
    (hgrid : (fun a => R.coeff a) ∈ denominatorGrid q)
    (hdegree : R.totalDegree ≤ r) (hdr : d ≤ r)
    (hidentity : ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b)
          (weightedHomogeneousComponent w d (fractionalCoefficientPolynomial F)) =
        eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R) :
    let R' := restoredMajorRemainder F w d R
    (fun a => R'.coeff a) ∈ denominatorGrid q ∧ R'.totalDegree ≤ r ∧
      ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
        eval (Sum.elim u b) (weightedHomogeneousComponent w d F) =
          eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S +
            eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R' := by
  refine ⟨restoredMajorRemainder_coefficientGrid F w d R q hgrid,
    restoredMajorRemainder_totalDegree_le F w hw d R hdegree hdr, ?_⟩
  intro u b hb
  rw [weightedHomogeneousComponent_fractional_restoration, map_add, hidentity u b hb,
    restoredMajorRemainder_eval, add_assoc]

end Erdos3

end

end OAI

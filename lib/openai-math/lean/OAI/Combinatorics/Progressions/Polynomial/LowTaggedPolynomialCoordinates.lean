import OAI.Combinatorics.Progressions.Fourier.NormalizedTwistLocalizedFourierSelection

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

abbrev LowTaggedIndex (d : ℕ) := {i : Σ j, J j // i.1.val + 1 ≤ d}

noncomputable def lowTaggedIndex (d : ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    Σ j, J j := ((Fintype.equivFin (LowTaggedIndex J d)).symm i).val

theorem lowTaggedIndex_property (d : ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    (lowTaggedIndex J d i).1.val + 1 ≤ d :=
  ((Fintype.equivFin (LowTaggedIndex J d)).symm i).property

noncomputable def lowTaggedWeight (d : ℕ) : Fin (Fintype.card (LowTaggedIndex J d)) → ℕ :=
  fun i => (lowTaggedIndex J d i).1.val + 1

theorem lowTaggedWeight_pos (d : ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    0 < lowTaggedWeight J d i := Nat.succ_pos _

theorem lowTaggedWeight_le (d : ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    lowTaggedWeight J d i ≤ d := lowTaggedIndex_property J d i

theorem lowTaggedIndex_card_le (d : ℕ) :
    Fintype.card (LowTaggedIndex J d) ≤ Fintype.card (Σ j, J j) :=
  Fintype.card_le_of_injective Subtype.val Subtype.val_injective

theorem lowTagged_sum (d : ℕ) {V : Type*} [AddCommMonoid V] (f : (Σ j, J j) → V) :
    (∑ i : Σ j, J j, if i.1.val + 1 ≤ d then f i else 0) =
      ∑ i : Fin (Fintype.card (LowTaggedIndex J d)), f (lowTaggedIndex J d i) := by
  classical
  calc
    _ = ∑ i : LowTaggedIndex J d, f i.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) f
    _ = _ := Fintype.sum_equiv (Fintype.equivFin (LowTaggedIndex J d)) _ _
      (fun i => by simp only [lowTaggedIndex, Equiv.symm_apply_apply])

variable {X : Type*}

noncomputable def lowTaggedPolynomial (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (i : Fin (Fintype.card (LowTaggedIndex J d))) : MvPolynomial X ℝ :=
  coordinate (LinearMap.proj (lowTaggedIndex J d i).2 :
    (J (lowTaggedIndex J d i).1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom
    (poly (lowTaggedIndex J d i).1)

theorem lowTaggedPolynomial_coeff (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (i : Fin (Fintype.card (LowTaggedIndex J d))) (α : X →₀ ℕ) :
    (lowTaggedPolynomial J d poly i).coeff α =
      coefficients (poly (lowTaggedIndex J d i).1) α (lowTaggedIndex J d i).2 := by
  rw [lowTaggedPolynomial, coeff_coordinate]
  rfl

theorem lowTaggedPolynomial_eval (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (i : Fin (Fintype.card (LowTaggedIndex J d))) (u : X → ℝ) :
    MvPolynomial.eval u (lowTaggedPolynomial J d poly i) =
      eval u (poly (lowTaggedIndex J d i).1) (lowTaggedIndex J d i).2 := by
  rw [lowTaggedPolynomial, ← coordinate_eval₂]
  have he : eval₂ u (poly (lowTaggedIndex J d i).1) =
      eval u (poly (lowTaggedIndex J d i).1) := by
    simpa using (eval₂_algebraMap (S := ℝ) u (poly (lowTaggedIndex J d i).1))
  rw [he]
  rfl

theorem lowTaggedPolynomial_degree (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    (lowTaggedPolynomial J d poly i).totalDegree ≤ lowTaggedWeight J d i := by
  have hw : (lowTaggedPolynomial J d poly i).weightedTotalDegree (1 : X → ℕ) ≤
      lowTaggedWeight J d i := by
    apply (scalar_weightedDegree_le_iff _ _ _).mpr
    intro α hα
    rw [lowTaggedPolynomial_coeff, hpoly _ α hα]
    rfl
  simpa only [MvPolynomial.weightedTotalDegree_one] using hw

noncomputable def lowTaggedFrequency (d : ℕ) (a : (Σ j, J j) → ℤ) :
    Fin (Fintype.card (LowTaggedIndex J d)) → ℤ :=
  fun i => a (lowTaggedIndex J d i)

theorem lowTaggedFrequency_bound (d : ℕ) (a : (Σ j, J j) → ℤ) (B : ℝ)
    (ha : ∀ i, |(a i : ℝ)| ≤ B) :
    ∀ i, |(lowTaggedFrequency J d a i : ℝ)| ≤ B := fun i => ha (lowTaggedIndex J d i)

theorem normalizedTwistFrequencyPolynomial_low_eval (cover d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (u : X → ℝ) :
    MvPolynomial.eval u
        (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly) =
      (∑ i : Fin (Fintype.card (LowTaggedIndex J d)),
        (lowTaggedFrequency J d a i : ℝ) *
          MvPolynomial.eval u (lowTaggedPolynomial J d poly i)) / (cover : ℝ) := by
  classical
  rw [normalizedTwistFrequencyPolynomial_eval]
  calc
    _ = (∑ i : Σ j, J j, if i.1.val + 1 ≤ d then
        (a i : ℝ) * eval u (poly i.1) i.2 else 0) / (cover : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.1.val + 1 ≤ d <;>
        simp only [truncateTaggedFrequency, hi, ite_true, ite_false,
          Int.cast_zero, zero_mul, zero_div, mul_div_assoc]
    _ = _ := by
      rw [lowTagged_sum]
      simp only [lowTaggedFrequency, lowTaggedPolynomial_eval]

end Erdos3.VectorPolynomial

end

end OAI

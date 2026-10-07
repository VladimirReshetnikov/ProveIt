import OAI.Combinatorics.Progressions.Dynamics.RationalConstraintCountBudget
import OAI.Combinatorics.Progressions.Estimates.NativeModelOrbit

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_common_rational_model_coordinates
    {G : Type*} {L : G → Type*} [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
    {s d : ℕ} (D : ∀ h, RationalFilteredNilmanifold (L h) s d)
    (H : Finset G) (hH : H.Nonempty) {p : ℝ} (hp : 0 ≤ p)
    (hD : ∀ h ∈ H, (D h).GeometryComplexityLE p) :
    ∃ h₀ ∈ H, ∃ H' : Finset G, H' ⊆ H ∧ h₀ ∈ H' ∧
      (∀ h ∈ H', (D h).rationalModelCoordinates = (D h₀).rationalModelCoordinates) ∧
      Real.exp (-(3 * (d ^ 3 + (s + 1) * d ^ 2 : ℕ) * (p + 2))) * H.card ≤ (H'.card : ℝ) := by
  let S : Set (RationalModelCoordinateIndex s d → ℚ) :=
    {c | ∀ z, rationalLogHeight (c z) ≤ p}
  obtain ⟨hfinite, hcount⟩ := finite_card_bounded_height_arrays S ⌈Real.exp p⌉₊
    (fun _ hc z => rationalHeightLE_ceil_exp (hc z))
  have hcount' : (S.ncard : ℝ) ≤ Real.exp (3 * (d ^ 3 + (s + 1) * d ^ 2 : ℕ) * (p + 2)) := by
    have hh := (Nat.cast_le.mpr hcount).trans
      (rational_log_height_count_exp_bound (Fintype.card (RationalModelCoordinateIndex s d)) hp)
    have hdim : Fintype.card (RationalModelCoordinateIndex s d) = d ^ 3 + (s + 1) * d ^ 2 := by
      simp only [RationalModelCoordinateIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      ring
    simpa only [hdim] using hh
  obtain ⟨c, _, H', hsub, hnonempty, hcode, hlarge⟩ :=
    exists_exponential_constant_fiber H hH (fun h => (D h).rationalModelCoordinates)
      S hfinite (fun h hh => (D h).rationalModelCoordinates_height hp (hD h hh)) hcount'
  obtain ⟨h₀, hh₀⟩ := hnonempty
  exact ⟨h₀, hsub hh₀, H', hsub, hh₀,
    (fun h hh => (hcode h hh).trans (hcode h₀ hh₀).symm), hlarge⟩

theorem exists_common_rational_model_power (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)] {d : ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s d) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h ∈ H, (D h).GeometryComplexityLE p) →
      ∃ h₀ ∈ H, ∃ H' : Finset G, H' ⊆ H ∧ h₀ ∈ H' ∧
        (∀ h ∈ H', (D h).rationalModelCoordinates = (D h₀).rationalModelCoordinates) ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) := by
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (3 * (X ^ 3 + Polynomial.C (s + 1) * X ^ 2) * (X + 2))
  refine ⟨C, hC, ?_⟩
  intro G L _ _ d D H hH p hp hD
  obtain ⟨h₀, hh₀, H', hsub, hh₀', heq, hlarge⟩ :=
    exists_common_rational_model_coordinates D H hH hp hD
  have hd := (hD h₀ hh₀).1
  have hb : 3 * (d ^ 3 + (s + 1) * d ^ 2 : ℕ) * (p + 2) ≤ (p + C) ^ C := by
    have hb' : 3 * (p ^ 3 + (s + 1 : ℕ) * p ^ 2) * (p + 2) ≤ (p + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget p hp
    apply le_trans _ hb'
    push_cast
    gcongr
  exact ⟨h₀, hh₀, H', hsub, hh₀', heq,
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hb))
      (Nat.cast_nonneg _)).trans hlarge⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

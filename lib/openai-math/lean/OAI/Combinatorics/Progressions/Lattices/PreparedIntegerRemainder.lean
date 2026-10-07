import OAI.Combinatorics.Progressions.Polynomial.PreparedPolynomialIdentity

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {X J : Type} [Fintype J] [DecidableEq J] {m : ℕ}
variable (L : RankPreparationFamily X J m)

noncomputable def integerRemainder (ip : J → MvPolynomial X ℤ)
    (β : ∀ u, (L u).Coord → MvPolynomial X ℤ) : J → MvPolynomial X ℤ :=
  ip + ∑ u, coordinateCopySum (L u).label (β u)

omit [Fintype J] in
theorem integerRemainder_degree (ip : J → MvPolynomial X ℤ)
    (hip : ∀ j, (ip j).totalDegree ≤ m) (β : ∀ u, (L u).Coord → MvPolynomial X ℤ)
    (hβ : ∀ u i, (β u i).totalDegree ≤ u.val + 1) (j : J) :
    (L.integerRemainder ip β j).totalDegree ≤ m := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (hip j)
  rw [Finset.sum_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro u _
  exact (coordinateCopySum_polynomial_degree (L u).label (β u) (hβ u) j).trans
    (Nat.succ_le_of_lt u.isLt)

omit [Fintype J] in
theorem integerRemainder_eval (ip : J → MvPolynomial X ℤ)
    (β : ∀ u, (L u).Coord → MvPolynomial X ℤ) (x : X → ℝ) (j : J) :
    MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)) =
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (ip j)) +
        ∑ u, coordinateCopySum (L u).label
          (fun i => MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))) j := by
  let f : MvPolynomial X ℤ →+* ℝ :=
    (MvPolynomial.eval x).comp (MvPolynomial.map (Int.castRingHom ℝ))
  change f (ip j + (∑ u, coordinateCopySum (L u).label (β u)) j) = _
  rw [Finset.sum_apply, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  exact coordinateCopySum_map (L u).label f (β u) j

theorem integerRemainder_bound
    (P E : VectorPolynomial X ℝ (J → ℝ)) (ip : J → MvPolynomial X ℤ) (c : J → ℝ)
    (hP : P = L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + E)
    (β : ∀ u, (L u).Coord → MvPolynomial X ℤ) (center : ∀ u, (L u).Coord → ℝ)
    (ε : Fin m → ℝ) (hε : ∀ u, 0 ≤ ε u) {δ : ℝ} (Ω : Set (X → ℝ))
    (hsmall : ∀ x ∈ Ω, ∀ u i, |eval x (L u).poly i - center u i -
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))| ≤ ε u)
    (herr : ∀ x ∈ Ω, ∀ j, |eval x E j| ≤ δ) :
    ∀ x ∈ Ω, ∀ j,
      |eval x P j - MvPolynomial.eval x
          (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)) -
        (c j + ∑ u, coordinateCopySum (L u).label (center u) j)| ≤
          (∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ := by
  intro x hx j
  let r : ∀ u, (L u).Coord → ℝ := fun u i => eval x (L u).poly i - center u i -
    MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))
  have heq : eval x P j - MvPolynomial.eval x
      (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)) -
      (c j + ∑ u, coordinateCopySum (L u).label (center u) j) =
      (∑ u, coordinateCopySum (L u).label (r u) j) + eval x E j := by
    rw [hP, map_add, map_add, map_add, polynomial_eval, integerCoordinates_eval_real,
      integerRemainder_eval]
    simp only [Pi.add_apply, eval_tmul, map_one, one_smul]
    have hr (u) : r u = eval x (L u).poly - center u -
        (fun i => MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))) := rfl
    simp only [hr, map_sub, Pi.sub_apply, Finset.sum_sub_distrib, value,
      RankPreparationLayer.value, Finset.sum_apply]
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  apply add_le_add _ (herr x hx j)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro u _
  exact coordinateCopySum_abs_le (L u).label (hε u) (hsmall x hx u) j

theorem integerRemainder_oscillation
    (P E : VectorPolynomial X ℝ (J → ℝ)) (ip : J → MvPolynomial X ℤ) (c : J → ℝ)
    (hP : P = L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + E)
    (β : ∀ u, (L u).Coord → MvPolynomial X ℤ) (center : ∀ u, (L u).Coord → ℝ)
    (ε : Fin m → ℝ) (hε : ∀ u, 0 ≤ ε u) {δ : ℝ} (hδ : 0 ≤ δ) (Ω : Set (X → ℝ))
    (hsmall : ∀ x ∈ Ω, ∀ u i, |eval x (L u).poly i - center u i -
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ) (β u i))| ≤ ε u)
    (herr : ∀ x ∈ Ω, ∀ j, |eval x E j| ≤ δ) (x₀ : X → ℝ) (hx₀ : x₀ ∈ Ω) :
    ∀ x ∈ Ω,
      ‖(eval x P - fun j => MvPolynomial.eval x
          (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j))) -
        (eval x₀ P - fun j => MvPolynomial.eval x₀
          (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)))‖ ≤
            2 * ((∑ u, (Fintype.card (L u).Coord : ℝ) * ε u) + δ) := by
  intro x hx
  have hsum : 0 ≤ ∑ u, (Fintype.card (L u).Coord : ℝ) * ε u :=
    Finset.sum_nonneg (fun u _ => mul_nonneg (Nat.cast_nonneg _) (hε u))
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  rw [Real.norm_eq_abs]
  let a := c j + ∑ u, coordinateCopySum (L u).label (center u) j
  have hxBound := L.integerRemainder_bound P E ip c hP β center ε hε Ω hsmall herr x hx j
  have h₀Bound := L.integerRemainder_bound P E ip c hP β center ε hε Ω hsmall herr x₀ hx₀ j
  have heq : ((eval x P - fun j => MvPolynomial.eval x
      (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j))) -
      (eval x₀ P - fun j => MvPolynomial.eval x₀
      (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)))) j =
      (eval x P j - MvPolynomial.eval x
      (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)) - a) -
      (eval x₀ P j - MvPolynomial.eval x₀
      (MvPolynomial.map (Int.castRingHom ℝ) (L.integerRemainder ip β j)) - a) := by
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

end Erdos3.RankPreparationFamily

end

end OAI

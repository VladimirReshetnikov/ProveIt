/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry

namespace OAI

section

namespace Erdos3
open scoped BigOperators

private theorem widthBudget_le_exp (x : ℝ) : x ≤ Real.exp x :=
  (by linarith : x ≤ x + 1).trans (Real.add_one_le_exp x)

private theorem widthBudget_residue_bounds {n : ℕ} (P : Fin n → ℕ)
    [∀ i, NeZero (P i)] {t : ℝ} (ht : 0 ≤ t)
    (hP : ∀ i, (P i : ℝ) ≤ Real.exp t) :
    1 + unconditionedResidueSiteBound P ≤ Real.exp ((n : ℝ) + 1 + t) ∧
    (Fintype.card (∀ i, ZMod (P i)) : ℝ) ≤ Real.exp ((n : ℝ) * t) := by
  have hsum : unconditionedResidueSiteBound P ≤ (n : ℝ) * Real.exp t := by
    calc
      _ ≤ ∑ _i : Fin n, Real.exp t := Finset.sum_le_sum (fun i _ => hP i)
      _ = _ := by simp
  have hone : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  constructor
  · calc
      1 + unconditionedResidueSiteBound P ≤ ((n : ℝ) + 1) * Real.exp t := by nlinarith
      _ ≤ Real.exp ((n : ℝ) + 1) * Real.exp t :=
        mul_le_mul_of_nonneg_right (widthBudget_le_exp _) (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  · calc
      (Fintype.card (∀ i, ZMod (P i)) : ℝ) = ∏ i, (P i : ℝ) := by
        simp [Fintype.card_pi]
      _ ≤ ∏ _i : Fin n, Real.exp t :=
        Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hP i)
      _ = Real.exp ((n : ℝ) * t) := by simp [Real.exp_nat_mul]

theorem unconditionedSpatialTrimFraction_inv_exp_bound {p : ℝ} {d : ℕ}
    (hd : (d : ℝ) ≤ p) :
    (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ ≤ Real.exp (2 * p + 33) := by
  have h32 : (32 : ℝ) ≤ Real.exp 32 := widthBudget_le_exp _
  have hdexp : (d : ℝ) + 1 ≤ Real.exp (p + 1) :=
    (by linarith : (d : ℝ) + 1 ≤ p + 1).trans (widthBudget_le_exp _)
  calc
    (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ =
        32 * ((d : ℝ) + 1) * Real.exp p := by
      simp [unconditionedSpatialTrimFraction, Real.exp_neg]
    _ ≤ Real.exp 32 * Real.exp (p + 1) * Real.exp p := by gcongr
    _ = Real.exp (2 * p + 33) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

private theorem widthBudget_collision {n : ℕ} (P : Fin n → ℕ)
    [∀ i, NeZero (P i)] {t p : ℝ}
    (hcard : (Fintype.card (∀ i, ZMod (P i)) : ℝ) ≤ Real.exp ((n : ℝ) * t)) :
    unconditionedCollisionWidth P (Real.exp (-p)) ≤
      Real.exp (32 + 2 * (n : ℝ) * t + p) := by
  calc
    _ = 32 * (Fintype.card (∀ i, ZMod (P i)) : ℝ)^2 * Real.exp p := by
      simp [unconditionedCollisionWidth, div_eq_mul_inv, Real.exp_neg]
    _ ≤ Real.exp 32 * (Real.exp ((n : ℝ) * t))^2 * Real.exp p := by
      gcongr
      exact widthBudget_le_exp _
    _ = Real.exp (32 + 2 * (n : ℝ) * t + p) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring

private theorem widthBudget_cutoff {n : ℕ} (c : ℕ)
    (hc : 8 * (probabilityProfileLipschitz : ℝ) ≤ c)
    {p : ℝ} (hp : 0 ≤ p) (d : ℕ) (hd : (d : ℝ) ≤ p)
    (P : Fin n → ℕ) [∀ i, NeZero (P i)]
    (hP : ∀ i, (P i : ℝ) ≤ Real.exp (p + n + 2)) :
    unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction d (Real.exp (-p)))
      (unconditionedCollisionWidth P (Real.exp (-p))) ≤
      Real.exp ((c : ℝ) + 80 + n + (p + n + 2) + 2 * n * (p + n + 2) + 4 * p) := by
  let t : ℝ := p + n + 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hcn : 0 ≤ (c : ℝ) := Nat.cast_nonneg _
  obtain ⟨hsite, hcard⟩ := widthBudget_residue_bounds P ht hP
  have hinv := unconditionedSpatialTrimFraction_inv_exp_bound hd
  have hcollision := widthBudget_collision P (p := p) hcard
  have hmax : max (8 * (probabilityProfileLipschitz : ℝ))
      (unconditionedCollisionWidth P (Real.exp (-p))) ≤
      Real.exp ((c : ℝ) + 32 + 2 * n * t + p) := by
    apply max_le
    · exact (hc.trans (widthBudget_le_exp _)).trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hn ht]))
    · exact hcollision.trans (Real.exp_le_exp.mpr (by linarith))
  have hsite0 : 0 ≤ 1 + unconditionedResidueSiteBound P := by
    have : 0 ≤ unconditionedResidueSiteBound P :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    linarith
  have hmax0 : 0 ≤ max (8 * (probabilityProfileLipschitz : ℝ))
      (unconditionedCollisionWidth P (Real.exp (-p))) :=
    (by positivity : (0 : ℝ) ≤ 8 * (probabilityProfileLipschitz : ℝ)).trans (le_max_left _ _)
  have hinv0 : 0 ≤ (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ := by
    unfold unconditionedSpatialTrimFraction
    positivity
  unfold unconditionedSpatialWidthCutoff
  apply max_le
  · calc
      _ = 4 * (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp 4 * Real.exp (2 * p + 33) :=
        mul_le_mul (widthBudget_le_exp _) hinv hinv0 (Real.exp_pos _).le
      _ = Real.exp (4 + (2 * p + 33)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [t] at *; nlinarith [mul_nonneg hn ht])
  · calc
      _ = 8 * (1 + unconditionedResidueSiteBound P) *
          max (8 * (probabilityProfileLipschitz : ℝ))
            (unconditionedCollisionWidth P (Real.exp (-p))) *
          (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp 8 * Real.exp ((n : ℝ) + 1 + t) *
          Real.exp ((c : ℝ) + 32 + 2 * n * t + p) * Real.exp (2 * p + 33) := by
        apply mul_le_mul _ hinv hinv0 (by positivity)
        apply mul_le_mul _ hmax hmax0 (by positivity)
        exact mul_le_mul (widthBudget_le_exp _) hsite hsite0 (Real.exp_pos _).le
      _ = Real.exp (8 + ((n : ℝ) + 1 + t) +
          ((c : ℝ) + 32 + 2 * n * t + p) + (2 * p + 33)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [t]; linarith)

theorem exists_unconditionedSpatialWidthCutoff_exp_budget (n₀ : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ (p : ℝ), 2 ≤ p → ∀ (d : ℕ), (d : ℝ) ≤ p →
    ∀ (P : Fin n₀ → ℕ) [∀ i, NeZero (P i)],
    (∀ i, (P i : ℝ) ≤ Real.exp (p + n₀ + 2)) →
    unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction d (Real.exp (-p)))
      (unconditionedCollisionWidth P (Real.exp (-p))) ≤ Real.exp ((p + 2)^E) := by
  obtain ⟨c, hc⟩ := exists_nat_ge (8 * (probabilityProfileLipschitz : ℝ))
  let T : Polynomial ℕ := Polynomial.X + Polynomial.C n₀ + 2
  let Q : Polynomial ℕ := Polynomial.C c + 80 + Polynomial.C n₀ + T +
    2 * Polynomial.C n₀ * T + 4 * Polynomial.X
  obtain ⟨E, hE, hbudget⟩ := exists_natPolynomial_fixed_power_budget Q
  refine ⟨E, hE, ?_⟩
  intro p hp d hd P hne hP
  have hp0 : 0 ≤ p := by linarith
  apply (widthBudget_cutoff c hc hp0 d hd P hP).trans
  apply Real.exp_le_exp.mpr
  simpa [Q, T] using hbudget p hp0

end Erdos3

end

end OAI

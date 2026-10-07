import OAI.Combinatorics.Progressions.Estimates.NativeOrbitFreezing

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct BigOperators NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d N : ℕ} [NeZero N]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

noncomputable def frozenCyclicOrbitValue (D : RationalFilteredNilmanifold L s d)
    (Φ : D.Space → ℂ) (ε b γ : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (y x : ZMod N) : ℂ :=
  Φ (QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) ε *
     D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) b *
     D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) γ))

theorem exists_partition_orbit_freezing (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d N M : ℕ} [NeZero N] (D : RationalFilteredNilmanifold L s d)
      {p ρ : ℝ}, 1 ≤ p → D.GeometryComplexityLE p → 0 < ρ →
      ∀ (A : I → ZMod N → ℝ), (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
      (∀ j x y, x ∉ cyclicWrapExceptional 0 ρ → y ∉ cyclicWrapExceptional 0 ρ →
        0 < A j x → 0 < A j y →
        |(x.val : ℝ) - y.val| ≤ N * ρ ∧ (M : ℤ) ∣ (x.val : ℤ) - y.val) →
      ∀ (Φ : D.Space → ℂ) (K : ℝ≥0), (∀ x, ‖Φ x‖ ≤ 1) →
      (letI := D.metricSpace; LipschitzWith K Φ) → (K : ℝ) ≤ Real.exp p →
      ∀ ε b γ g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      ε * b * γ = g →
      CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((p + 2) ^ a)) ε.log →
      (∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
        (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x γ) : D.Space) =
          QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y γ)) →
      ∃ y : I → ZMod N,
        (∀ j x, ‖D.frozenCyclicOrbitValue Φ ε b γ (y j) x‖ ≤ 1) ∧
        (𝔼 x, ‖Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) g)) -
          ∑ j, (A j x : ℂ) * D.frozenCyclicOrbitValue Φ ε b γ (y j) x‖) ≤
            Real.exp ((p + C) ^ C) * ρ + 12 * ρ + 6 / N := by
  obtain ⟨C, hC, hfreeze⟩ := exists_orbit_factor_freezing s a
  refine ⟨C, hC, ?_⟩
  intro I L _ _ _ _ _ _ _ d N M _ D p ρ hp hD hρ A hA hsum hcells Φ K hΦ hLip hK ε b γ g hprod hε hperiod
  classical
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hchoose (j : I) : ∃ y : ZMod N, ∀ x, x ∉ E → 0 < A j x → y ∉ E ∧ 0 < A j y := by
    by_cases h : ∃ y, y ∉ E ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun _ _ => hΦ _, ?_⟩
  have hpoint (j : I) (x : ZMod N) (hx : x ∉ E) (hAx : 0 < A j x) :
      ‖Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) g)) -
        D.frozenCyclicOrbitValue Φ ε b γ (y j) x‖ ≤ Real.exp ((p + C) ^ C) * ρ := by
    obtain ⟨hyE, hAy⟩ := hy j x hx hAx
    obtain ⟨hnear, hres⟩ := hcells j x (y j) hx hyE hAx hAy
    apply hfreeze D (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) p (by linarith) hD
      (by simpa only [Fintype.card_unit, Nat.cast_one] using hp)
      Φ K hΦ hLip hK ε b γ g hprod (fun _ : Unit => (N : ℝ))
      (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) hε
      (fun _ => (x.val : ℤ)) (fun _ => ((y j).val : ℤ)) ρ hρ.le
      (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (hperiod _ _ (fun _ => hres))
    · simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ x.val from Nat.cast_nonneg _)] using
        (Nat.cast_le.mpr x.val_lt.le : (x.val : ℝ) ≤ N)
    · simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ (y j).val from Nat.cast_nonneg _)] using
        (Nat.cast_le.mpr (y j).val_lt.le : ((y j).val : ℝ) ≤ N)
    · simpa only [Int.cast_natCast] using hnear
  have hm := complex_partition_approximation_mean_error E A
    (fun j x => D.frozenCyclicOrbitValue Φ ε b γ (y j) x)
    (fun x : ZMod N => Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) g)))
    (mul_nonneg (Real.exp_pos _).le hρ.le) hA hsum (fun _ _ => hΦ _) (fun _ => hΦ _) hpoint
  apply hm.trans
  have hE := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
  rw [ZMod.card]
  calc
    _ = Real.exp ((p + C) ^ C) * ρ + 2 * ((E.card : ℝ) / N) := by ring
    _ ≤ Real.exp ((p + C) ^ C) * ρ + 2 * (6 * ρ + 3 / N) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := by ring

end Erdos3.RationalFilteredNilmanifold

end

end OAI

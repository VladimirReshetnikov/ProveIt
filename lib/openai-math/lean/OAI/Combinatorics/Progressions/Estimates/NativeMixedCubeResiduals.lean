import OAI.Combinatorics.Progressions.Polynomial.CubicResidualPhase

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem nativeMixedResidual_norm_le_one {s N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (h : ZMod N) (i : Fin M.outputDim) (x : ZMod N) :
    ‖nativeMixedResidual f M h i x‖ ≤ 1 := by
  rw [nativeMixedResidual, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (multiplicativeDerivative_norm_le_one f hf h x)).trans (M.norm_eval _ _)

noncomputable def nativeMixedCubeResidual {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (d + 2)) p)
    (i : Fin M.outputDim) (u : Fin (d + 1) → ZMod N) : ZMod N → ℂ :=
  cubeProduct (nativeMixedResidual f M (u 0) i) (List.ofFn (Fin.tail u))

theorem nativeMixedCubeResidual_norm_le_one {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (d + 2)) p)
    (i : Fin M.outputDim) (u : Fin (d + 1) → ZMod N) (x : ZMod N) :
    ‖nativeMixedCubeResidual f M i u x‖ ≤ 1 :=
  cubeProduct_norm_le_one _ (nativeMixedResidual_norm_le_one f hf M (u 0) i) _ x

theorem nativeMixedCubeResidual_eq {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (d + 2)) p)
    (i : Fin M.outputDim) (u : Fin (d + 1) → ZMod N) (x : ZMod N) :
    nativeMixedCubeResidual f M i u x =
      cubeProduct f (List.ofFn u) x *
        star (cubeProduct (fun y => M.evalCyclic N i (correlationInput (u 0) y))
          (List.ofFn (Fin.tail u)) x) := by
  change cubeProduct (fun y => multiplicativeDerivative f (u 0) y *
    star (M.evalCyclic N i (correlationInput (u 0) y))) (List.ofFn (Fin.tail u)) x = _
  rw [cubeProduct_mul, cubeProduct_star, List.ofFn_succ, cubeProduct_cons_eq_derivative]
  rfl

namespace NativeMixedCorrelation

theorem exists_degree_one_cube_residuals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ i : Fin M.mixed.outputDim, ∃ Q : Finset (Fin (d + 1) → ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 1) ≤ (Q.card : ℝ) ∧
        ∀ u ∈ Q, u 0 ∈ M.shifts ∧
          Nonempty (NativeVectorCorrelation 1 N ((p + C) ^ C)
            (fun _ : Unit => nativeMixedCubeResidual f M.mixed i u)) := by
  obtain ⟨a, _, hiter⟩ := exists_iterated_native_derivative_correlations 1 d (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * X + P)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  classical
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsum : 2 * p + q ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨i, H, hsub, hH, hHdense, hHcorr⟩ := M.exists_fixed_residual_coordinate
  have hdata (h : H) := hiter hp ((Real.exp_le_exp.mpr hqC).trans hN)
    (nativeMixedResidual f M.mixed h.val i)
    (nativeMixedResidual_norm_le_one f hf M.mixed h.val i)
    (by simpa only [show d + 2 - 1 = 1 + d by omega] using hHcorr h.val h.property)
  choose K _hK hKdense hKcorr using hdata
  obtain ⟨Q, hQdense, hQmem⟩ := dense_tuple_fibers d H K (Real.exp_nonneg (-q))
    (by simpa only [ZMod.card] using hHdense)
    (fun h => by simpa only [ZMod.card] using hKdense h)
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast lt_of_lt_of_le
      (by positivity : 0 < Real.exp (-(2 * p)) * Real.exp (-q) *
        (Fintype.card (ZMod N) : ℝ) ^ (d + 1)) hQdense
  refine ⟨i, Q, hQ, ?_, ?_⟩
  · have heq : Real.exp (-(2 * p + q)) = Real.exp (-(2 * p)) * Real.exp (-q) := by
      rw [neg_add, Real.exp_add]
    have hsmall := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hsum))
      (pow_nonneg (Nat.cast_nonneg N) (d + 1))
    rw [heq] at hsmall
    exact hsmall.trans (by simpa only [ZMod.card] using hQdense)
  · intro u hu
    obtain ⟨h, hh, htail⟩ := (hQmem u).mp hu
    refine ⟨hsub (hh ▸ h.property), ?_⟩
    obtain ⟨V⟩ := hKcorr h (Fin.tail u) htail
    change Nonempty (NativeVectorCorrelation 1 N ((p + C) ^ C)
      (fun _ : Unit => cubeProduct (nativeMixedResidual f M.mixed (u 0) i)
        (List.ofFn (Fin.tail u))))
    rw [← hh]
    exact ⟨V.mono hqC⟩

end NativeMixedCorrelation
end Erdos3

end

end OAI

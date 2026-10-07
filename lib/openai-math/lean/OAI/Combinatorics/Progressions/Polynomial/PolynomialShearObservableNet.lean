import OAI.Combinatorics.Progressions.Estimates.BoundedCoefficientEvaluation
import OAI.Combinatorics.Progressions.Estimates.UniformParameterNet
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbitConverse

namespace OAI

section

namespace Erdos3

open MvPolynomial

abbrev PatchTopCoefficientIndex (d s : ℕ) := Fin d × BoundedIntegerExponent (Fin d) s

theorem patchTopCoefficientIndex_card (d s : ℕ) :
    Fintype.card (PatchTopCoefficientIndex d s) ≤ d * (d + 1) ^ s := by
  simpa only [PatchTopCoefficientIndex, Fintype.card_prod, Fintype.card_fin] using
    Nat.mul_le_mul_left d (boundedIntegerExponent_card_le (Fin d) s)

theorem patchTopCoefficientCode_card (d s N : ℕ) :
    Fintype.card (PatchTopCoefficientIndex d s → Fin (N + 1)) ≤
      (N + 1) ^ (d * (d + 1) ^ s) := by
  simp only [Fintype.card_fun, Fintype.card_fin]
  exact Nat.pow_le_pow_right (by omega) (patchTopCoefficientIndex_card d s)

noncomputable def patchTopNetError (d s N : ℕ) (M : ℝ) : ℝ :=
  ((s + 1) * (d + 1) ^ s : ℕ) * (4 * (1 + M) / N) * ((1 + M) ^ (s * d)) ^ s

theorem patchTopNetError_nonneg (d s N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ patchTopNetError d s N M := by unfold patchTopNetError; positivity

namespace PolynomialSlots

theorem exists_shear_observable_net {X Ω : Type*} [Nonempty Ω] {d s N : ℕ} {w : Fin d → ℕ}
    (A : Ω → PolynomialSlots X d w) (hw : Monotone w)
    (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s) (Φ : PatchKernel d)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ a i, realPolynomialMass ((A a).center i) ≤ M)
    (hN : 0 < N) (hsmall : patchTopNetError d s N M < 1 / 4) :
    ∃ (code : Ω → PatchTopCoefficientIndex d s → Fin (N + 1))
      (rep : (PatchTopCoefficientIndex d s → Fin (N + 1)) → Ω),
      ∀ a e, dist (((A a).shearTransformedSlots hw e).patchValue Φ)
        (((A (rep (code a))).shearTransformedSlots hw e).patchValue Φ) ≤
        Φ.lip * patchTopNetError d s N M := by
  let coordinates : Ω → PatchTopCoefficientIndex d s → ℝ :=
    fun a j => ((A a).topResidualEquiv (MvPolynomial.X j.1)).coeff j.2.val
  have hbound (a) (j : PatchTopCoefficientIndex d s) : |coordinates a j| ≤ 1 + M :=
    (realPolynomialMass_coeff_le _ _).trans ((A a).topResidualEquiv_X_mass (hA a) j.1)
  obtain ⟨code, rep, hnet⟩ := exists_uniform_parameter_net coordinates (by linarith : 0 < 1 + M) hbound hN
  refine ⟨code, rep, fun a e => ?_⟩
  apply (A a).shearPatchValue_dist (A (rep (code a))) hw hpos s hs Φ hM
    (patchTopNetError_nonneg d s N hM) hsmall (hA a) (hA _) _ e
  intro x hx
  apply (dist_pi_le_iff (patchTopNetError_nonneg d s N hM)).mpr
  intro i
  have hdegree (a : Ω) : ((A a).topResidualEquiv (MvPolynomial.X i)).totalDegree ≤ s :=
    (totalDegree_le_of_positive_weightedSupport w hpos
      ((A a).topResidualEquiv_degree (weightedSupportLE_X w i))).trans (hs i)
  have hcoeff (m : BoundedIntegerExponent (Fin d) s) :
      |((A a).topResidualEquiv (MvPolynomial.X i)).coeff m.val -
        ((A (rep (code a))).topResidualEquiv (MvPolynomial.X i)).coeff m.val| ≤ 4 * (1 + M) / N := by
    exact (dist_le_pi_dist (coordinates a) (coordinates (rep (code a))) (i,m)).trans (hnet a)
  have h := bounded_coefficients_evaluation_error _ _ (hdegree a) (hdegree _)
    (by positivity : 0 ≤ 4 * (1 + M) / N)
    (one_le_pow₀ (by linarith : 1 ≤ 1 + M) : 1 ≤ (1 + M) ^ (s * d)) hcoeff x hx
  change |aeval x ((A a).topResidualEquiv (MvPolynomial.X i)) -
    aeval x ((A (rep (code a))).topResidualEquiv (MvPolynomial.X i))| ≤ patchTopNetError d s N M
  simpa only [Fintype.card_fin, patchTopNetError] using h

end PolynomialSlots
end Erdos3

end

end OAI

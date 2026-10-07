import OAI.Combinatorics.Progressions.Polynomial.JointPolynomialDilationGrid

namespace OAI

section

namespace Erdos3

open MvPolynomial

noncomputable def realAxisAffinePolynomial {σ : Type*} (h r : σ → ℝ) (i : σ) : MvPolynomial σ ℝ :=
  C (h i) + C (r i) * X i

noncomputable def realAxisAffinePullback {σ : Type*} (h r : σ → ℝ) :
    MvPolynomial σ ℝ →+* MvPolynomial σ ℝ :=
  eval₂Hom C (realAxisAffinePolynomial h r)

theorem realAxisAffinePullback_eval {σ : Type*} (h r x : σ → ℝ) (P : MvPolynomial σ ℝ) :
    eval x (realAxisAffinePullback h r P) = eval (fun i => h i + r i * x i) P := by
  have heq : (eval x).comp (realAxisAffinePullback h r) = eval (fun i => h i + r i * x i) := by
    ext <;> simp [realAxisAffinePullback, realAxisAffinePolynomial]
  exact RingHom.congr_fun heq P

theorem realAxisAffinePullback_totalDegree_le {σ : Type*} (h r : σ → ℝ)
    (P : MvPolynomial σ ℝ) :
    (realAxisAffinePullback h r P).totalDegree ≤ P.totalDegree := by
  have hf (i : σ) : (realAxisAffinePolynomial h r i).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · apply (totalDegree_mul _ _).trans
      simp
  simpa only [realAxisAffinePullback, mul_one] using polynomial_substitution_totalDegree_le P
    (realAxisAffinePolynomial h r) hf le_rfl

theorem realAxisAffinePolynomial_mass_le {σ : Type*} (h r : σ → ℝ) (i : σ) :
    realPolynomialMass (realAxisAffinePolynomial h r i) ≤ |h i| + |r i| := by
  apply (realPolynomialMass_add_le _ _).trans
  apply add_le_add
  · exact (realPolynomialMass_C _).le
  · simpa only [realPolynomialMass_X, mul_one] using realPolynomialMass_C_mul_le (r i) (X i)

theorem scaleMvPolynomialAxes_affine {σ : Type*} (T A h r : σ → ℝ)
    (hT : ∀ i, T i ≠ 0) (P : MvPolynomial σ ℝ) :
    scaleMvPolynomialAxes A (realAxisAffinePullback h r P) =
      realAxisAffinePullback (fun i => h i / T i) (fun i => r i * A i / T i)
        (scaleMvPolynomialAxes T P) := by
  apply MvPolynomial.funext
  intro x
  rw [scaleMvPolynomialAxes_eval, realAxisAffinePullback_eval,
    realAxisAffinePullback_eval, scaleMvPolynomialAxes_eval]
  apply congrArg (fun y : σ → ℝ => eval y P)
  funext i
  field_simp [hT i]

theorem realAxisAffinePullback_coeff_bound {σ : Type*}
    (T A h r : σ → ℝ) (hT : ∀ i, 0 < T i) (hA : ∀ i, 0 < A i)
    (P : MvPolynomial σ ℝ) {M B : ℝ} {s : ℕ} (hB : 1 ≤ B)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale T α)
    (hphysical : ∀ i, |h i| + |r i| * A i ≤ B * T i)
    (hdegree : P.totalDegree ≤ s) (α : σ →₀ ℕ) :
    |(realAxisAffinePullback h r P).coeff α| ≤
      (P.support.card * M * B ^ s) / monomialScale A α := by
  have hf (i : σ) : realPolynomialMass
      (realAxisAffinePolynomial (fun j => h j / T j) (fun j => r j * A j / T j) i) ≤ B := by
    apply (realAxisAffinePolynomial_mass_le _ _ i).trans
    calc
      _ = (|h i| + |r i| * A i) / T i := by
        rw [abs_div, abs_div, abs_mul, abs_of_pos (hT i), abs_of_pos (hA i)]
        ring
      _ ≤ B := (div_le_iff₀ (hT i)).mpr (hphysical i)
  have hmass : realPolynomialMass (scaleMvPolynomialAxes A (realAxisAffinePullback h r P)) ≤
      P.support.card * M * B ^ s := by
    rw [scaleMvPolynomialAxes_affine T A h r (fun i => (hT i).ne')]
    apply (realPolynomialMass_substitution_le (scaleMvPolynomialAxes T P) _ hB hf
      ((scaleMvPolynomialAxes_totalDegree_le T P).trans hdegree)).trans
    exact mul_le_mul_of_nonneg_right (scaleMvPolynomialAxes_mass_le T hT P hcoeff)
      (pow_nonneg (zero_le_one.trans hB) _)
  have hc := (realPolynomialMass_coeff_le (scaleMvPolynomialAxes A (realAxisAffinePullback h r P)) α).trans hmass
  rw [scaleMvPolynomialAxes_coeff, abs_mul, abs_of_pos (monomialScale_pos A hA α)] at hc
  exact (le_div_iff₀ (monomialScale_pos A hA α)).mpr hc

end Erdos3

end

end OAI

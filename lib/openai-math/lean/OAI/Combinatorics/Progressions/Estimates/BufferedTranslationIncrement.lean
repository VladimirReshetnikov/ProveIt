import OAI.Combinatorics.Progressions.Polynomial.TranslationPhasePointBounds
import OAI.Combinatorics.Progressions.Polynomial.TwistedBufferedTranslationPhase

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {m : ℕ}

theorem translation_cutoff_increment_bound (Ψ : PatchKernel m)
    (z g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ)
    {ε : ℝ} (hε : 0 ≤ ε) (hbase : ∀ i, |z.base i| ≤ ε) :
    |Ψ.value (fun i => (z * g).base i - (β i : ℝ)) -
      Ψ.value (fun i => g.base i - (β i : ℝ))| ≤ Ψ.lip * ε := by
  have hdist : dist (fun i => (z * g).base i - (β i : ℝ))
      (fun i => g.base i - (β i : ℝ)) ≤ ε := by
    apply (dist_pi_le_iff hε).mpr
    intro i
    simp only [Real.dist_eq, PolynomialTranslationGroupOver.base_mul, Pi.add_apply]
    rw [show z.base i + g.base i - (β i : ℝ) - (g.base i - (β i : ℝ)) = z.base i by ring]
    exact hbase i
  exact (Ψ.lipschitz.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left hdist Ψ.lip.coe_nonneg)

theorem bufferedTranslationTerm_increment_bound (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (z g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ)
    {d : ℕ} {M ε : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 4)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (heval : ∀ x : Fin m → ℝ, (∀ i, |x i| ≤ 1) → |eval x z.polynomial| ≤ ε) :
    ‖bufferedTranslationTerm Ψ D₀ (z * g) β - bufferedTranslationTerm Ψ D₀ g β‖ ≤
      (Ψ.lip + (2 * Real.pi) * (1 + M * m * d)) * ε := by
  let a := Ψ.value (fun i => (z * g).base i - (β i : ℝ))
  let b := Ψ.value (fun i => g.base i - (β i : ℝ))
  let v : ℂ := Real.fourierChar (translationPhaseArgument D₀ (z * g) (fun i => (β i : ℝ)))
  let u : ℂ := Real.fourierChar (translationPhaseArgument D₀ g (fun i => (β i : ℝ)))
  have hv : ‖v‖ = 1 := Circle.norm_coe _
  have hdiff : |a - b| ≤ Ψ.lip * ε := translation_cutoff_increment_bound Ψ z g β hε hbase
  have hM : 0 ≤ M := (realPolynomialMass_nonneg D₀).trans hD
  change ‖(a : ℂ) * v - (b : ℂ) * u‖ ≤ _
  by_cases hb : b = 0
  · rw [hb, Complex.ofReal_zero, zero_mul, sub_zero, norm_mul, hv, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    have ha : |a| ≤ Ψ.lip * ε := by simpa only [hb, sub_zero] using hdiff
    apply ha.trans
    have hn : 0 ≤ (2 * Real.pi) * (1 + M * m * d) := by positivity
    nlinarith
  · have hres (i : Fin m) : |(β i : ℝ) - g.base i| ≤ 1 / 4 := by
      rw [abs_sub_comm]
      exact Ψ.support _ hb i
    have he : |eval ((fun i => (β i : ℝ)) - g.base) z.polynomial| ≤ ε :=
      heval _ (fun i => (hres i).trans (by norm_num))
    have hc : ‖v - u‖ ≤ (2 * Real.pi) * (1 + M * m * d) * ε := by
      simpa only [Fintype.card_fin] using
        translationPhaseCharacter_left_increment_quarter_point_bound D₀ z g
          (fun i => (β i : ℝ)) hε hεsmall hdegree hD hres hbase he
    have hid : (a : ℂ) * v - (b : ℂ) * u = ((a - b : ℝ) : ℂ) * v + (b : ℂ) * (v - u) := by
      push_cast
      ring
    rw [hid]
    have h1 : ‖((a - b : ℝ) : ℂ) * v‖ ≤ Ψ.lip * ε := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hv, mul_one] using hdiff
    have h2 : ‖(b : ℂ) * (v - u)‖ ≤ (2 * Real.pi) * (1 + M * m * d) * ε := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
      exact (mul_le_mul_of_nonneg_right (Ψ.le_one _) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hc)
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end Erdos3

end

end OAI

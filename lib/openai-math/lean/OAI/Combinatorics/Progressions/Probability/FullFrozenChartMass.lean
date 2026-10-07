import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
import OAI.Combinatorics.Progressions.Polynomial.NormalizedFrozenPolynomialMass

namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial VectorPolynomial

theorem aeval_frozen_integer_chart {σ K : Type*}
    (β : σ → MvPolynomial K ℤ)
    (keep : K → Prop) (fixed : {i // ¬keep i} → ℤ)
    (p : MvPolynomial σ ℝ) :
    aeval (integerSampledRealChart (fun z => freezePolynomial keep fixed (β z))) p =
      freezePolynomial keep (fun i => (fixed i : ℝ))
        (aeval (integerSampledRealChart β) p) := by
  have hchart : integerSampledRealChart (fun z => freezePolynomial keep fixed (β z)) =
      fun z => freezePolynomial keep (fun i => (fixed i : ℝ)) (integerSampledRealChart β z) := by
    funext z
    exact integerSampledRealChart_freeze β keep fixed z
  rw [hchart]
  exact (comp_aeval_apply (integerSampledRealChart β)
    (freezePolynomial keep (fun i => (fixed i : ℝ))) p).symm

theorem normalizedMass_aeval_frozen_integer_chart_le {σ K : Type*}
    (β : σ → MvPolynomial K ℤ)
    (keep : K → Prop) (T : K → ℝ) (hT : ∀ i, 0 < T i)
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, |(fixed i : ℝ)| ≤ T i.val)
    (p : MvPolynomial σ ℝ) :
    realPolynomialMass
      (scaleMvPolynomialAxes (fun i : {i // keep i} => T i.val)
        (aeval (integerSampledRealChart (fun z => freezePolynomial keep fixed (β z))) p)) ≤
      realPolynomialMass
        (scaleMvPolynomialAxes T (aeval (integerSampledRealChart β) p)) := by
  rw [aeval_frozen_integer_chart]
  exact normalizedMass_freezePolynomial_le keep T hT
    (fun i => (fixed i : ℝ)) hfixed _

end Erdos3

end

end OAI

/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_native_approximation
    {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {periodCap coverCap : ℝ} {lip : ℝ≥0}
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : FiniteProbabilityWeights Ω)
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (w : X → ℕ) (degree : ℕ) (complexity : ℝ)
    {K C cap beta tau εtail : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hcap : 0 < cap)
    (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      (tau / cap ^ 2) / max 1 (K * (2 * C) / tau) ≤
        sampledSliceSeminorm μ site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree complexity
          (fun u : integerBox N => u.val) G) ∧
        beta ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass (μ.siteLaw physical) C ≤ εtail)
    (input : integerBox N → ℂ) (hinput : ∀ u, ‖input u‖ ≤ cap) :
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (Q : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions w degree complexity
        (fun u : integerBox N => u.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
          (u : integerBox N) => W.eval N poly u.val)) ∧
      input = (∑ i, coeff i • Q i) + err ∧
      (∑ i, |coeff i|) ≤ 2 / beta ∧
      sampledSliceSeminorm μ physical slices tests err ≤
        2 * tau + 2 * K * (cap + 2 / beta) * εtail ∧
      (nterms : ℝ) ≤ 1 + 4 * (K * (2 * C)) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let : Nonempty (integerBox N) := (integerBox_nonempty N).to_subtype
  have htwist (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
      (u : integerBox N) : ‖W.eval N poly u.val‖ ≤ 1 := W.norm_eval_le N poly u.val
  have hdetector (g : integerBox N → ℂ) (hg : ∀ u, ‖g u‖ ≤ 1)
      (hlarge : (tau / cap ^ 2) / max 1 (K * (2 * C) / tau) ≤
        sampledSliceSeminorm μ physical slices tests g) :
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree complexity
          (fun u : integerBox N => u.val) G) ∧
        beta ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation g
          (fun u => star (W.eval N poly u.val) * G u)‖ := by
    let ext := finiteSiteExtension (Subtype.val : integerBox N → X → ℤ) g
    let signal := zeroExtendFinset (integerBox N) ext
    have hsignal (u) : ‖signal u‖ ≤ 1 :=
      zeroExtendFinset_norm_le_one (integerBox N) ext
        (fun u _ => finiteSiteExtension_norm_le _ g hg u) u
    have hzero (u) (hu : u ∉ integerBox N) : signal u = 0 := by
      simp only [signal, zeroExtendFinset, ite_eq_right hu]
    have hvalue (u : integerBox N) : signal u.val = g u := by
      simpa only [signal, zeroExtendFinset, ite_eq_left u.property, ext] using
        finiteSiteExtension_apply Subtype.val Subtype.val_injective g u
    have hseminorm := sampledSliceSeminorm_congr_values μ site physical slices tests
      hsize htests signal g (fun z t => by rw [← hphysical z t]; exact hvalue _)
    obtain ⟨W, G, hG, hc⟩ := hdetect signal hsignal hzero
      (hseminorm.symm ▸ hlarge)
    exact ⟨W, G, hG, by simpa only [hvalue] using hc⟩
  have hr (u : integerBox N) : 0 <
      (FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).weight u := by
    change 0 < (Fintype.card (integerBox N) : ℝ)⁻¹
    positivity
  exact exists_sampled_native_model μ physical slices tests
    (FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)) hr
    w degree complexity (fun u : integerBox N => u.val)
    (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
      (u : integerBox N) => W.eval N poly u.val)
    htwist hK hC hcap hbeta htau hsize htests hdetector hexcess input hinput

end Erdos3.VectorPolynomial

end

end OAI

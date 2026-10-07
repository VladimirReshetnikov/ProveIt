import OAI.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer

namespace OAI

section

namespace Erdos3
open scoped NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable def NativeSampleModel.weaken {σ X : Type*} {w : σ → ℕ}
    {degree : ℕ} {p q : ℝ} {sample : X → σ → ℤ} {f : X → ℂ}
    (F : NativeSampleModel w degree p sample f) (hpq : p ≤ q) :
    NativeSampleModel w degree q sample f :=
  { F with complexity := F.complexity.mono hpq }

namespace VectorPolynomial

theorem normalized_native_detection_mono
    {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {Y : Type*} [Fintype Y] (sample : Y → X → ℤ) (r : FiniteProbabilityWeights Y)
    (signal : Y → ℂ) (s : ℕ)
    {periodCap coverCap periodCap' coverCap' C C' : ℝ} {L L' : ℝ≥0}
    (hperiod : periodCap ≤ periodCap') (hcover : coverCap ≤ coverCap')
    (hL : L ≤ L') (hC : C ≤ C')
    (hdetect : ∃ W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L,
      ∃ f : Y → ℂ,
        Nonempty (NativeSampleModel (fun _ : X => 1) s C sample f) ∧
        Real.exp (-C) ≤ ‖r.correlation signal (fun u => star (W.eval N p (sample u)) * f u)‖) :
    ∃ W : NormalizedPolynomialTwist X (Σ j, J j) periodCap' coverCap' L',
      ∃ f : Y → ℂ,
        Nonempty (NativeSampleModel (fun _ : X => 1) s C' sample f) ∧
        Real.exp (-C') ≤ ‖r.correlation signal (fun u => star (W.eval N p (sample u)) * f u)‖ := by
  obtain ⟨W, f, ⟨F⟩, hc⟩ := hdetect
  exact ⟨W.mono hperiod hcover hL, f, ⟨F.weaken hC⟩,
    (Real.exp_le_exp.mpr (neg_le_neg hC)).trans hc⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem exists_normalizedNative_uniform_budget (m Anorm Anative : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {B P E analytic gain mass spatial volume coverLog : ℝ} {nX : ℕ},
      0 ≤ B → P ∈ Set.Icc 0 B → E ∈ Set.Icc 0 B → analytic ∈ Set.Icc 0 B →
      gain ∈ Set.Icc 0 B → mass ∈ Set.Icc 0 B → spatial ∈ Set.Icc 0 B →
      volume ∈ Set.Icc 0 B → coverLog ≤ B → (nX : ℝ) ≤ B →
      let budget := (B + A) ^ A
      (((m + 1 : ℕ) : ℝ) * P + nX * P ≤ budget) ∧
      coverLog ≤ budget ∧
      (P + E + analytic + Anorm) ^ Anorm ≤ budget ∧
      (gain + 8 + mass + spatial + volume + 2) ^ Anative ≤ budget := by
  let X : Polynomial ℕ := Polynomial.X
  let poly : Polynomial ℕ := (m + 1 : ℕ) * X + X ^ 2 + X +
    (3 * X + Polynomial.C Anorm) ^ Anorm + (4 * X + 10) ^ Anative
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro B P E analytic gain mass spatial volume coverLog nX hB hP hE ha hg hm hs hv hc hn budget
  have hsum : ((m + 1 : ℕ) : ℝ) * B + B ^ 2 + B +
      (3 * B + Anorm) ^ Anorm + (4 * B + 10) ^ Anative ≤ budget := by
    simpa [poly, X, Polynomial.eval₂_pow] using hbound B hB
  have hnorm0 : 0 ≤ (3 * B + Anorm) ^ Anorm := by positivity
  have hnative0 : 0 ≤ (4 * B + 10) ^ Anative := by positivity
  have hperiod0 : 0 ≤ ((m + 1 : ℕ) : ℝ) * B := by positivity
  have hperiod : ((m + 1 : ℕ) : ℝ) * P + nX * P ≤ ((m + 1 : ℕ) : ℝ) * B + B ^ 2 := by
    rw [pow_two]
    exact add_le_add (mul_le_mul_of_nonneg_left hP.2 (Nat.cast_nonneg _))
      (mul_le_mul hn hP.2 hP.1 hB)
  have hnorm : (P + E + analytic + Anorm) ^ Anorm ≤ (3 * B + Anorm) ^ Anorm := by
    apply pow_le_pow_left₀ (add_nonneg (add_nonneg (add_nonneg hP.1 hE.1) ha.1) (Nat.cast_nonneg _))
    linarith only [hP.2, hE.2, ha.2]
  have hnative : (gain + 8 + mass + spatial + volume + 2) ^ Anative ≤ (4 * B + 10) ^ Anative := by
    apply pow_le_pow_left₀ (add_nonneg
      (add_nonneg (add_nonneg (add_nonneg (add_nonneg hg.1 (by norm_num)) hm.1) hs.1) hv.1) (by norm_num))
    linarith only [hg.2, hm.2, hs.2, hv.2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith only [hsum, hperiod, hB, hnorm0, hnative0]
  · linarith only [hsum, hc, hperiod0, sq_nonneg B, hnorm0, hnative0]
  · linarith only [hsum, hnorm, hperiod0, sq_nonneg B, hB, hnative0]
  · linarith only [hsum, hnative, hperiod0, sq_nonneg B, hB, hnorm0]

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct BigOperators

variable {σ L Ω : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 0 d) {w : σ → ℕ}

theorem norm_correlation_step_zero_sample (T : D.Niltest w)
    (Q : Finset Ω) (x : Ω → (σ → ℤ)) (f : Ω → ℂ) :
    ‖finiteCorrelation Q f (fun a => T.eval (x a))‖ ≤
      (T.normBound : ℝ) * ‖𝔼 a ∈ Q, f a‖ := by
  calc
    _ = ‖𝔼 a ∈ Q, f a‖ * ‖T.observable (QuotientGroup.mk (1 : D.RealGroup))‖ := by
      simp only [finiteCorrelation, eval_step_zero D, ← Finset.expect_mul, norm_mul, norm_star]
    _ ≤ _ := by
      rw [mul_comm (T.normBound : ℝ)]
      exact mul_le_mul_of_nonneg_left (T.norm_le _) (norm_nonneg _)

theorem detection_step_zero_sample (T : D.Niltest w) {p ρ : ℝ}
    (hT : T.ComplexityLE p) (Q : Finset Ω) (x : Ω → (σ → ℤ)) (f : Ω → ℂ)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f (fun a => T.eval (x a))‖) :
    ρ / Real.exp p ≤ ‖𝔼 a ∈ Q, f a‖ := by
  apply (div_le_iff₀ (Real.exp_pos p)).mpr
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    have hh := T.observable_budget hT
    linarith [T.lipBound.coe_nonneg]
  have hc := hcorr.trans (norm_correlation_step_zero_sample D T Q x f)
  exact hc.trans (by nlinarith [norm_nonneg (𝔼 a ∈ Q, f a)])

theorem detection_step_zero_box [Fintype σ] [DecidableEq σ]
    (T : D.Niltest w) {p ρ : ℝ} (hT : T.ComplexityLE p)
    (lengths : σ → ℕ) [∀ i, NeZero (lengths i)] (f : (σ → ℤ) → ℂ)
    (hcorr : ρ ≤ ‖finiteCorrelation (integerBox lengths) f T.eval‖) :
    ρ / Real.exp p ≤ integerBoxGowersNorm lengths 1 f := by
  rw [integerBoxGowersNorm_degree_one]
  exact detection_step_zero_sample D T hT (integerBox lengths) id f hcorr

theorem detection_step_zero_cyclic [Fintype σ] [DecidableEq σ] (T : D.Niltest w)
    {p ρ : ℝ} (hT : T.ComplexityLE p) (N : ℕ) [NeZero N]
    (f : (σ → ZMod N) → ℂ)
    (hcorr : ρ ≤ ‖finiteCorrelation Finset.univ f (T.evalCyclic N)‖) :
    ρ / Real.exp p ≤ gowersNorm 1 f := by
  rw [gowersNorm_one]
  let points : (σ → ZMod N) → (σ → ℤ) := fun x i => ((x i).val : ℤ)
  have hc : ρ ≤ ‖finiteCorrelation Finset.univ f (fun x => T.eval (points x))‖ := hcorr
  exact detection_step_zero_sample D T hT Finset.univ points f hc

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open scoped TensorProduct

def BoxNiltestDetection.{u,v} (s : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ {σ : Type v} [Fintype σ] [DecidableEq σ] {L : Type u} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (p : ℝ),
    0 ≤ p → (Fintype.card σ : ℝ) ≤ p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
    ∀ (T : D.Niltest w), T.ComplexityLE p →
    ∀ (a : σ → ℤ) (lengths : σ → ℕ) [∀ i, NeZero (lengths i)] (f : (σ → ℤ) → ℂ),
    (∀ x ∈ translatedIntegerBox a lengths, ‖f x‖ ≤ 1) →
    Real.exp (-p) ≤ ‖finiteCorrelation (translatedIntegerBox a lengths) f T.eval‖ →
    Real.exp (-F p) ≤ finiteSupportGowersNorm (s + 1) (translatedIntegerBox a lengths) f

theorem BoxNiltestDetection.mono.{u,v} {s : ℕ} {F G : ℝ → ℝ}
    (hF : BoxNiltestDetection.{u,v} s F) (hFG : ∀ p, 0 ≤ p → F p ≤ G p) :
    BoxNiltestDetection.{u,v} s G := by
  intro σ _ _ L _ _ d _ _ _ _ D p hp hσ w hw T hT a lengths _ f hf hc
  exact (Real.exp_le_exp.mpr (neg_le_neg (hFG p hp))).trans
    (hF D p hp hσ w hw T hT a lengths f hf hc)

theorem boxNiltestDetection_zero.{u,v} : BoxNiltestDetection.{u,v} 0 (fun p => 2 * p) := by
  intro σ _ _ L _ _ d _ _ _ _ D p hp hσ w hw T hT a lengths _ f hf hc
  have hb := RationalFilteredNilmanifold.Niltest.detection_step_zero_sample
    D T hT (translatedIntegerBox a lengths) id f hc
  have he : Real.exp (-p) / Real.exp p = Real.exp (-(2 * p)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [he] at hb
  rw [translatedIntegerBox_norm_degree_one]
  exact hb

end Erdos3

end

end OAI

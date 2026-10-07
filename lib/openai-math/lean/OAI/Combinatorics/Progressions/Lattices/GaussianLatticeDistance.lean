/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import OAI.Combinatorics.Progressions.Fourier.LatticeGaussianMeanFourier

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeGaussianMass_quarter_temperature {t : ℝ} (ht : 0 < t) :
    latticeGaussianMass Λ (t / 4) 0 ≤
      (2 : ℝ) ^ Module.finrank ℝ E * latticeGaussianMass Λ t 0 := by
  have hmono := normalizedLatticeGaussian_origin_mono Λ (show 0 < t / 4 by positivity)
    (show t / 4 ≤ t by linarith)
  have hsqrt : Real.sqrt (t / 4) = Real.sqrt t / 2 := by
    rw [Real.sqrt_div ht.le]
    norm_num
  have hn := latticeGaussianNormalizer_pos Λ ht
  have htwo : (0 : ℝ) < 2 ^ Module.finrank ℝ E := by positivity
  have hnorm : latticeGaussianNormalizer Λ (t / 4) =
      latticeGaussianNormalizer Λ t / (2 : ℝ) ^ Module.finrank ℝ E := by
    unfold latticeGaussianNormalizer
    rw [hsqrt, div_pow]
    ring
  change latticeGaussianNormalizer Λ (t / 4) * latticeGaussianMass Λ (t / 4) 0 ≤
    latticeGaussianNormalizer Λ t * latticeGaussianMass Λ t 0 at hmono
  rw [hnorm, div_mul_eq_mul_div] at hmono
  have h := (div_le_iff₀ htwo).mp hmono
  nlinarith

noncomputable def latticeGaussianTail (t R : ℝ) : ℝ :=
  ∑' m : Λ, if R < ‖(m : E)‖ then Real.exp (-Real.pi * t * ‖(m : E)‖ ^ 2) else 0

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ Λ] in
theorem latticeGaussianTail_summable {t : ℝ} (ht : 0 < t) (R : ℝ) :
    Summable (fun m : Λ => if R < ‖(m : E)‖ then Real.exp (-Real.pi * t * ‖(m : E)‖ ^ 2) else 0) := by
  classical
  convert! (lattice_gaussian_summable Λ ht 0).indicator {m : Λ | R < ‖(m : E)‖} using 1
  funext m
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, zero_sub, norm_neg]

theorem latticeGaussianTail_bound {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R) :
    latticeGaussianTail Λ t R ≤ Real.exp (-Real.pi * t * R ^ 2 / 2) *
      (2 : ℝ) ^ Module.finrank ℝ E * latticeGaussianMass Λ t 0 := by
  classical
  have hpoint (m : Λ) :
      (if R < ‖(m : E)‖ then Real.exp (-Real.pi * t * ‖(m : E)‖ ^ 2) else 0) ≤
        Real.exp (-Real.pi * t * R ^ 2 / 2) * Real.exp (-Real.pi * (t / 4) * ‖(m : E)‖ ^ 2) := by
    split_ifs with hm
    · rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hsq : R ^ 2 ≤ ‖(m : E)‖ ^ 2 := pow_le_pow_left₀ hR hm.le 2
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le ht.le) (sub_nonneg.mpr hsq),
        mul_nonneg (mul_nonneg Real.pi_pos.le ht.le) (sq_nonneg ‖(m : E)‖)]
    · positivity
  have hs := (lattice_gaussian_summable Λ (show 0 < t / 4 by positivity) 0).mul_left
    (Real.exp (-Real.pi * t * R ^ 2 / 2))
  simp only [zero_sub, norm_neg] at hs
  have h := (latticeGaussianTail_summable Λ ht R).tsum_le_tsum hpoint hs
  rw [tsum_mul_left] at h
  have h' : latticeGaussianTail Λ t R ≤ Real.exp (-Real.pi * t * R ^ 2 / 2) *
      latticeGaussianMass Λ (t / 4) 0 := by
    simpa only [latticeGaussianTail, latticeGaussianMass, zero_sub, norm_neg] using h
  exact h'.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (latticeGaussianMass_quarter_temperature Λ ht) (Real.exp_pos _).le)

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeGaussianMass_le_origin {t : ℝ} (ht : 0 < t) (x : E) :
    latticeGaussianMass Λ t x ≤ latticeGaussianMass Λ t 0 := by
  have h := normalizedLatticeGaussian_le_origin Λ ht x
  exact (mul_le_mul_iff_right₀ (latticeGaussianNormalizer_pos Λ ht)).mp h

theorem normalizedLatticeGaussian_le_of_far {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R)
    (x : E) (hfar : ∀ m : Λ, R ≤ ‖x - (m : E)‖) :
    normalizedLatticeGaussian Λ t x ≤ Real.exp (-Real.pi * t * R ^ 2 / 2) *
      (2 : ℝ) ^ Module.finrank ℝ E * normalizedLatticeGaussian Λ t 0 := by
  have hpoint (m : Λ) : Real.exp (-Real.pi * t * ‖x - (m : E)‖ ^ 2) ≤
      Real.exp (-Real.pi * t * R ^ 2 / 2) * Real.exp (-Real.pi * (t / 4) * ‖x - (m : E)‖ ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq := pow_le_pow_left₀ hR (hfar m) 2
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le ht.le) (sub_nonneg.mpr hsq),
      mul_nonneg (mul_nonneg Real.pi_pos.le ht.le) (sq_nonneg ‖x - (m : E)‖)]
  have hs := (lattice_gaussian_summable Λ (show 0 < t / 4 by positivity) x).mul_left
    (Real.exp (-Real.pi * t * R ^ 2 / 2))
  have hsum := (lattice_gaussian_summable Λ ht x).tsum_le_tsum hpoint hs
  rw [tsum_mul_left] at hsum
  have hmass : latticeGaussianMass Λ t x ≤ Real.exp (-Real.pi * t * R ^ 2 / 2) *
      ((2 : ℝ) ^ Module.finrank ℝ E * latticeGaussianMass Λ t 0) := by
    exact hsum.trans (mul_le_mul_of_nonneg_left
      ((latticeGaussianMass_le_origin Λ (by positivity : 0 < t / 4) x).trans
        (latticeGaussianMass_quarter_temperature Λ ht)) (Real.exp_pos _).le)
  have hnorm := mul_le_mul_of_nonneg_left hmass (latticeGaussianNormalizer_pos Λ ht).le
  change latticeGaussianNormalizer Λ t * latticeGaussianMass Λ t x ≤ _
  calc
    _ ≤ latticeGaussianNormalizer Λ t * (Real.exp (-Real.pi * t * R ^ 2 / 2) *
        ((2 : ℝ) ^ Module.finrank ℝ E * latticeGaussianMass Λ t 0)) := hnorm
    _ = _ := by change _ = _ * _ * (latticeGaussianNormalizer Λ t * latticeGaussianMass Λ t 0); ring

end Erdos3

end

end OAI

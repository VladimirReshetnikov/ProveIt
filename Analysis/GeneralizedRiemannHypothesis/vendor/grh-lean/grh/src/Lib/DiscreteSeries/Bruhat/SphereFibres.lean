import Lib.DiscreteSeries.Bruhat.ComplexPlace
import Lib.DiscreteSeries.Bruhat.QuadricBlocks
import Mathlib.Probability.Kernel.WithDensity

/-!
# The spheres of ℂ^κ as fibres of the standard form

* `New.Floors.exists_isDisintegration_le_sphereDensity`: in rank at least two, the volume of ℂ^κ
  disintegrates along y ↦ y* y into a measurable family of measures on the spheres, whose mass on a
  box is bounded.

Notions from other files:
* `New.Floors.Place.IsDisintegration`: a family of measures, indexed by the skew scalars, whose
  integrals of compactly supported continuous functions are finite and continuous in the index and
  which integrates over the index to a given measure, the index recording the value of a form.
* `New.Floors.lintegral_eq_polar`: polar coordinates on ℂ^κ by the unitary group. The squared norm
  r has density `sphereDensity k r / 2`, where `sphereDensity k r` = 2 π^k r^(k-1) / (k-1)!.

## Relation to the literature
Elementary: polar coordinates.
-/

namespace New.Floors

open MeasureTheory Measure ProbabilityTheory Matrix Real Fintype Set RealPlace

/-- Substitution of `r = 2 t` in a Lebesgue integral over the real line. -/
lemma lintegral_eq_lintegral_two_mul {G : ℝ → ENNReal} (hG : Measurable G) :
    ∫⁻ r : ℝ, G r = ∫⁻ t : ℝ, 2 * G (2 * t) := by
  conv_lhs => rw [← smul_map_volume_mul_left two_ne_zero, lintegral_smul_measure,
    lintegral_map hG (by fun_prop)]
  rw [lintegral_const_mul _ (by fun_prop)]
  simp

/-- If the entries of a vector of ℂ^κ have modulus at most R, then its squared norm is at most
|κ| R². -/
lemma re_star_dotProduct_self_le {κ : Type} [Fintype κ] {y : κ → ℂ} {R : ℝ}
    (h_le : ∀ i : κ, ‖y i‖ ≤ R) : (star y ⬝ᵥ y).re ≤ card κ * R ^ 2 :=
  calc (star y ⬝ᵥ y).re = ∑ i : κ, ‖y i‖ ^ 2 := by
        simp [dotProduct, Complex.conj_mul', ← Complex.ofReal_pow]
    _ ≤ ∑ _ : κ, R ^ 2 := by
        gcongr with i
        exact h_le i
    _ = card κ * R ^ 2 := by simp

/-- Let κ have k ≥ 2 elements. Over the complex place the volume of ℂ^κ disintegrates along the
standard form y ↦ y* y into an s-finite kernel l from the skew (purely imaginary) numbers β to ℂ^κ:
the integral of f (y* y, y) over the volume is the iterated integral of f (-2 i β, y) against l β
and then β, and for continuous compactly supported g ≥ 0 the integral of g against l β is finite
and continuous in β. Moreover the mass that l β gives to the vectors with entries of modulus at
most R is at most `sphereDensity k (k R²)`, where `sphereDensity k r` = 2 π^k r^(k-1) / (k-1)!. -/
theorem exists_isDisintegration_le_sphereDensity {κ : Type} [Fintype κ] [DecidableEq κ]
    (hκ : 1 < card κ) :
    ∃ l : Kernel (skewAdjoint ℂ) (κ → ℂ), IsSFiniteKernel l ∧
      complexPlace.IsDisintegration volume (1 : Matrix κ κ ℂ) l ∧
      ∀ (β : skewAdjoint ℂ) (R : ℝ), l β {y : κ → ℂ | ∀ i : κ, ‖y i‖ ≤ R} ≤
        ENNReal.ofReal (sphereDensity (card κ) (card κ * R ^ 2)) := by
  -- For `β = t i` the sphere of squared radius `r = 2 t ≥ 0` is the orbit of `√r` times a basis
  -- vector. It gets the invariant measure of mass `sphereDensity (card κ) r`, the mass being zero
  -- for `r < 0`, and by polar coordinates these measures integrate to the volume.
  have h_card_pos : 0 < card κ := by lia
  obtain ⟨i₀⟩ : Nonempty κ := card_pos_iff.1 h_card_pos
  let point (r : ℝ) (h : U (1 : Matrix κ κ ℂ)) : κ → ℂ := h.val.val *ᵥ √r • Pi.single i₀ 1
  let mass (r : ℝ) : ENNReal := .ofReal (sphereDensity (card κ) r⁺)
  have h_form {r : ℝ} (hr : 0 ≤ r) (h : U (1 : Matrix κ κ ℂ)) :
      star (point r h) ⬝ᵥ (1 : Matrix κ κ ℂ) *ᵥ point r h = r := by
    rw [U.form_mulVec_mulVec]
    simp [star_trivial √r, ← Complex.ofReal_mul, mul_self_sqrt hr]
  have h_zero {r : ℝ} (hr : r ≤ 0) : mass r = 0 := by
    simp [mass, sphereDensity, posPart_eq_zero.2 hr, Nat.sub_ne_zero_of_lt hκ]
  obtain ⟨l, _, hl⟩ : ∃ l : Kernel (skewAdjoint ℂ) (κ → ℂ), IsSFiniteKernel l ∧
      ∀ β : skewAdjoint ℂ, l β = volume.map (point (2 * β.val.im)) :=
    exists_kernel_eq_map volume
      (K := fun p : skewAdjoint ℂ × U 1 ↦ point (2 * p.1.val.im) p.2) (by fun_prop)
  have h_lintegral (β : skewAdjoint ℂ) {F : (κ → ℂ) → ENNReal} (hF : Measurable F) :
      ∫⁻ x : κ → ℂ, F x ∂l.withDensity (fun β _ ↦ mass (2 * β.val.im)) β =
        mass (2 * β.val.im) * ∫⁻ h : U (1 : Matrix κ κ ℂ), F (point (2 * β.val.im) h) := by
    rw [Kernel.withDensity_apply _ (by fun_prop), withDensity_const, hl, lintegral_smul_measure,
      lintegral_map hF (by fun_prop), smul_eq_mul]
  refine ⟨l.withDensity fun β _ ↦ mass (2 * β.val.im),
    Kernel.IsSFiniteKernel.withDensity l fun _ _ ↦ ENNReal.ofReal_ne_top,
    ⟨fun {g} hg _ ↦ ?_, fun f hf ↦ ?_⟩, fun β R ↦ ?_⟩
  · -- the integrands are continuous on the compact unitary group
    let integrand (β : skewAdjoint ℂ) (h : U (1 : Matrix κ κ ℂ)) : NNReal :=
      (sphereDensity (card κ) (2 * β.val.im)⁺).toNNReal * g (point (2 * β.val.im) h)
    have h_integral (β : skewAdjoint ℂ) :
        ∫⁻ x : κ → ℂ, g x ∂l.withDensity (fun β _ ↦ mass (2 * β.val.im)) β =
          ∫⁻ h : U (1 : Matrix κ κ ℂ), integrand β h := by
      rw [h_lintegral β (by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
      rfl
    simp only [h_integral]
    exact continuous_lintegral_and_lt_top isCompact_univ (F := integrand) (by fun_prop)
      fun β h _ ↦ mem_univ h
  · -- polar coordinates, then the substitution `r = 2 t`
    simp (disch := fun_prop) only [h_lintegral]
    rw [lintegral_eq_polar i₀ (by fun_prop), ← lintegral_indicator measurableSet_Ioi,
      lintegral_eq_lintegral_two_mul (.indicator (by fun_prop) measurableSet_Ioi),
      complexPlace_skewMeasure, lintegral_map (by fun_prop) (by fun_prop)]
    refine lintegral_congr fun t ↦ ?_
    have h_im : ((t : ℂ) * Complex.I).im = t := by simp
    obtain ht | ht := le_or_gt (2 * t) 0
    · rw [indicator_of_notMem (notMem_Ioi.2 ht), h_im, h_zero ht, mul_zero, zero_mul]
    · have h_level : complexPlace.skewUnit⁻¹.val * (t * Complex.I) = (2 * t : ℝ) := by
        simp [field]
      have h_point (h : U (1 : Matrix κ κ ℂ)) :
          f (star (point (2 * t) h) ⬝ᵥ (1 : Matrix κ κ ℂ) *ᵥ point (2 * t) h, point (2 * t) h) =
            f (((2 * t : ℝ) : ℂ), point (2 * t) h) := by
        rw [h_form ht.le h]
      rw [indicator_of_mem (mem_Ioi.2 ht), ← mul_assoc, h_level, ENNReal.ofReal_div_of_pos two_pos,
        ENNReal.ofReal_ofNat, ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]
      simp only [h_im, mass, posPart_eq_self.2 ht.le]
      rw [← lintegral_congr h_point]
  · -- if the box meets the sphere of squared radius `2 * β.val.im`, that is at most `card κ * R²`
    rw [Kernel.withDensity_apply _ (by fun_prop), withDensity_const, hl, Measure.smul_apply,
      smul_eq_mul, Measure.map_apply (by fun_prop) (by measurability)]
    obtain h_empty | ⟨h, hh⟩ :=
      (point (2 * β.val.im) ⁻¹' {y : κ → ℂ | ∀ i : κ, ‖y i‖ ≤ R}).eq_empty_or_nonempty
    · simp [h_empty]
    obtain hr | hr := le_total (2 * β.val.im) 0
    · simp [h_zero hr]
    have h_le : 2 * β.val.im ≤ card κ * R ^ 2 := by
      have h_norm : star (point (2 * β.val.im) h) ⬝ᵥ point (2 * β.val.im) h =
          (2 * β.val.im : ℝ) := by
        rw [← h_form hr h, one_mulVec]
      simpa [h_norm] using re_star_dotProduct_self_le hh
    grw [prob_le_one, mul_one]
    simp only [mass, sphereDensity, posPart_eq_self.2 hr]
    gcongr

end New.Floors

import Surreal.HahnSeries.Modulus
import Surreal.HahnSeries.StandardPart
import Mathlib.Analysis.Complex.Norm

/-!
# Hahn order and standard part of the complex modulus

The real-Hahn-valued modulus has exactly the order of its complex argument.
For nonnegative-order series, its constant coefficient is the ordinary complex
norm of the constant coefficient. These are algebraic consequences of the
square identity and the lexicographic order, with no topological hypothesis.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

@[simp] theorem coeff_complexHahnLexEquiv_re (z : ℂ⟦Γ⟧) (g : Γ) :
    (ofLex (complexHahnLexEquiv z).re).coeff g = (z.coeff g).re := rfl

@[simp] theorem coeff_complexHahnLexEquiv_im (z : ℂ⟦Γ⟧) (g : Γ) :
    (ofLex (complexHahnLexEquiv z).im).coeff g = (z.coeff g).im := rfl

/-- The ordered quadratic identification respects the real Hahn embedding. -/
@[simp] theorem complexHahnLexEquiv_complexRealEmbedding (x : ℝ⟦Γ⟧) :
    complexHahnLexEquiv (complexRealEmbedding x) =
      algebraMap (Lex ℝ⟦Γ⟧) (Complexify (Lex ℝ⟦Γ⟧)) (toLex x) := by
  apply QuadraticAlgebra.ext
  · apply congrArg toLex
    apply _root_.HahnSeries.ext
    funext g
    rfl
  · apply congrArg toLex
    apply _root_.HahnSeries.ext
    funext g
    rfl

/-- Embedding real coefficients into complex coefficients preserves order. -/
@[simp] theorem orderTop_complexRealEmbedding (x : ℝ⟦Γ⟧) :
    (complexRealEmbedding x).orderTop = x.orderTop := by
  apply le_antisymm <;> apply le_orderTop_iff_forall.mpr
  · intro g hg
    have h := coeff_eq_zero_of_lt_orderTop hg
    simpa using h
  · intro g hg
    simp only [coeff_complexRealEmbedding, coeff_eq_zero_of_lt_orderTop hg, Complex.ofReal_zero]

@[simp] theorem complexHahnLexEquiv_single_zero (c : ℂ) :
    complexHahnLexEquiv (single (0 : Γ) c) =
      ⟨toLex (single 0 c.re), toLex (single 0 c.im)⟩ := by
  apply QuadraticAlgebra.ext
  · apply congrArg toLex
    apply _root_.HahnSeries.ext
    funext g
    change ((single (0 : Γ) c).coeff g).re = (single (0 : Γ) c.re).coeff g
    by_cases hg : g = 0 <;> simp [hg]
  · apply congrArg toLex
    apply _root_.HahnSeries.ext
    funext g
    change ((single (0 : Γ) c).coeff g).im = (single (0 : Γ) c.im).coeff g
    by_cases hg : g = 0 <;> simp [hg]

variable [DivisibleBy Γ ℕ]

@[simp] theorem complexModulus_complexRealEmbedding (x : ℝ⟦Γ⟧) :
    complexModulus (complexRealEmbedding x) = |toLex x| := by
  simp only [complexModulus, complexHahnLexEquiv_complexRealEmbedding,
    Complexify.modulus_algebraMap]

/-- The modulus of an ordinary complex constant is its ordinary norm,
embedded as a real Hahn constant. -/
@[simp] theorem complexModulus_single_zero (c : ℂ) :
    complexModulus (single (0 : Γ) c) = toLex (single 0 ‖c‖) := by
  apply Complexify.modulus_eq_of_nonneg_sq
  · rw [← leadingCoeff_nonneg_iff]
    simp
  · rw [complexHahnLexEquiv_single_zero]
    change toLex ((single (0 : Γ) ‖c‖) ^ 2) =
      toLex ((single (0 : Γ) c.re) ^ 2 + (single (0 : Γ) c.im) ^ 2)
    apply congrArg toLex
    simp only [single_pow, nsmul_zero]
    rw [← single_add]
    congr 1
    simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm c

/-- The square of the modulus, embedded in the complex Hahn field, is `z * conj z`. -/
theorem complexRealEmbedding_complexModulus_sq (z : ℂ⟦Γ⟧) :
    complexRealEmbedding ((ofLex (complexModulus z)) ^ 2) = z * complexConjugation z := by
  apply complexHahnLexEquiv.injective
  rw [complexHahnLexEquiv_complexRealEmbedding, map_mul,
    complexHahnLexEquiv_conjugation, Complexify.mul_conj]
  change algebraMap (Lex ℝ⟦Γ⟧) (Complexify (Lex ℝ⟦Γ⟧)) (complexModulus z ^ 2) = _
  rw [complexModulus_sq]

/-- Taking complex modulus preserves Hahn order, including infinity at zero. -/
@[simp] theorem orderTop_complexModulus (z : ℂ⟦Γ⟧) :
    (ofLex (complexModulus z)).orderTop = z.orderTop := by
  have h := congrArg (fun w : ℂ⟦Γ⟧ => w.orderTop)
    (complexRealEmbedding_complexModulus_sq z)
  rw [orderTop_complexRealEmbedding, pow_two, orderTop_mul, orderTop_mul,
    orderTop_complexConjugation] at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (WithTop.add_lt_add hlt hlt).ne h
  · exact (WithTop.add_lt_add hgt hgt).ne h.symm

omit [IsOrderedAddMonoid Γ] [DivisibleBy Γ ℕ] in
/-- A nonnegative real Hahn series of nonnegative order has nonnegative
constant coefficient. -/
theorem coeff_zero_nonneg_of_lex_nonneg (x : ℝ⟦Γ⟧)
    (hx : 0 ≤ x.orderTop) (hpos : 0 ≤ toLex x) : 0 ≤ x.coeff 0 := by
  by_cases hc : x.coeff 0 = 0
  · simp [hc]
  have ho : x.order = 0 := le_antisymm (order_le_of_coeff_ne_zero hc)
    (zero_le_orderTop_iff.mp hx)
  simpa only [ofLex_toLex, leadingCoeff_eq, ho] using (leadingCoeff_nonneg_iff.mpr hpos)

/-- Standard part commutes with the complex Hahn modulus on finite series. -/
theorem coeff_zero_complexModulus (z : ℂ⟦Γ⟧) (hz : 0 ≤ z.orderTop) :
    (ofLex (complexModulus z)).coeff 0 = ‖z.coeff 0‖ := by
  have hm : 0 ≤ (ofLex (complexModulus z)).orderTop := by
    simpa only [orderTop_complexModulus] using hz
  apply (sq_eq_sq₀ (coeff_zero_nonneg_of_lex_nonneg _ hm (complexModulus_nonneg z))
    (norm_nonneg _)).mp
  have h := congrArg (fun w : ℂ⟦Γ⟧ => (w.coeff 0).re)
    (complexRealEmbedding_complexModulus_sq z)
  rw [coeff_complexRealEmbedding, Complex.ofReal_re, pow_two,
    coeff_zero_mul_of_nonnegative _ _ hm hm,
    coeff_zero_mul_of_nonnegative _ _ hz (by simpa using hz),
    coeff_complexConjugation] at h
  simpa only [pow_two, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq] using h

theorem orderTop_eq_zero_of_complexModulus_eq_one (z : ℂ⟦Γ⟧)
    (hz : complexModulus z = 1) : z.orderTop = 0 := by
  rw [← orderTop_complexModulus, hz]
  exact orderTop_one

/-- Standard part of a modulus-one Hahn series lies on the ordinary unit circle. -/
theorem norm_coeff_zero_eq_one_of_complexModulus_eq_one (z : ℂ⟦Γ⟧)
    (hz : complexModulus z = 1) : ‖z.coeff 0‖ = 1 := by
  rw [← coeff_zero_complexModulus z (orderTop_eq_zero_of_complexModulus_eq_one z hz).ge,
    hz]
  simp

/-- Each ordered real coordinate is bounded in absolute value by the modulus. -/
theorem abs_complexHahnLexEquiv_re_le_modulus (z : ℂ⟦Γ⟧) :
    |(complexHahnLexEquiv z).re| ≤ complexModulus z :=
  Complexify.abs_re_le_modulus _

theorem abs_complexHahnLexEquiv_im_le_modulus (z : ℂ⟦Γ⟧) :
    |(complexHahnLexEquiv z).im| ≤ complexModulus z :=
  Complexify.abs_im_le_modulus _

end
end Surreal.HahnSeries

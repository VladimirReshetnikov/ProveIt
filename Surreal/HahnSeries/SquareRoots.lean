import Surreal.HahnSeries.BinomialOrder
import Surreal.Algebra.OrderedSquareRoots
import Mathlib.GroupTheory.Divisible

/-!
# Nonnegative square roots in ordered Hahn fields

Normalize a nonzero Hahn series by its leading monomial and coefficient.
The normalized series is one plus a positive-order error, so the already
constructed binomial half-power supplies its square root. A square root of
the leading coefficient and half of the leading exponent then reconstruct
a square root of the original series.

The coefficient field need only have nonnegative square roots. In particular,
real-closed coefficients and a divisible ordered abelian exponent group give
existence and uniqueness of nonnegative roots in the lexicographic Hahn
field, without assuming real closedness of that Hahn field.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- Remove a series's leading exponent and leading coefficient. -/
def leadingNormalized (x : K⟦Γ⟧) : K⟦Γ⟧ :=
  single (-x.order) x.leadingCoeff⁻¹ * x

theorem orderTop_leadingNormalized (x : K⟦Γ⟧) (hx : x ≠ 0) :
    (leadingNormalized x).orderTop = 0 := by
  have hc : x.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hx
  rw [leadingNormalized, orderTop_mul, orderTop_single (inv_ne_zero hc),
    ← order_eq_orderTop_of_ne_zero hx, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero]

theorem leadingCoeff_leadingNormalized (x : K⟦Γ⟧) (hx : x ≠ 0) :
    (leadingNormalized x).leadingCoeff = 1 := by
  rw [leadingNormalized, leadingCoeff_mul, leadingCoeff_of_single,
    inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hx)]

/-- The normalized remainder is genuinely of positive order, including zero. -/
theorem orderTop_leadingNormalized_sub_one_pos (x : K⟦Γ⟧) (hx : x ≠ 0) :
    0 < (leadingNormalized x - 1).orderTop :=
  (orderTop_self_sub_one_pos_iff _).mpr
    ⟨orderTop_leadingNormalized x hx, leadingCoeff_leadingNormalized x hx⟩

/-- Exact reconstruction from the leading monomial and normalized unit. -/
theorem leadingMonomial_mul_leadingNormalized (x : K⟦Γ⟧) (hx : x ≠ 0) :
    single x.order x.leadingCoeff * leadingNormalized x = x := by
  rw [leadingNormalized, ← mul_assoc, single_mul_single, add_neg_cancel,
    mul_inv_cancel₀ (leadingCoeff_ne_zero.mpr hx), single_zero_one, one_mul]

variable [LinearOrder K] [IsStrictOrderedRing K] [DivisibleBy Γ ℕ]

/-- Positive square roots are constructed from coefficient-field square roots,
halved exponents, and the strong binomial sum near one. -/
theorem exists_pos_square_root_of_coefficients
    (hK : ∀ a : K, 0 ≤ a → ∃ b : K, 0 ≤ b ∧ b ^ 2 = a)
    (x : K⟦Γ⟧) (hx : 0 < toLex x) :
    ∃ y : K⟦Γ⟧, 0 < toLex y ∧ y ^ 2 = x := by
  have hx0 : x ≠ 0 := by
    intro h
    simp only [h, toLex_zero, lt_self_iff_false] at hx
  have hc : 0 < x.leadingCoeff := leadingCoeff_pos_iff.mpr hx
  obtain ⟨b, hb, hbsq⟩ := hK x.leadingCoeff hc.le
  have hbpos : 0 < b := by
    refine lt_of_le_of_ne hb ?_
    intro h
    have : x.leadingCoeff = 0 := by rw [← hbsq, ← h, zero_pow (by decide)]
    exact hc.ne' this
  let a : Γ := DivisibleBy.div x.order (2 : ℕ)
  have ha : (2 : ℕ) • a = x.order := DivisibleBy.div_cancel _ (by decide)
  let ε := leadingNormalized x - 1
  have hε : 0 < ε.orderTop := orderTop_leadingNormalized_sub_one_pos x hx0
  let u := binomialPower ε hε (1 / 2 : ℚ)
  have hu : u ^ 2 = 1 + ε := binomialPower_half_sq ε hε
  have hmpos : 0 < toLex (single a b : K⟦Γ⟧) := by
    apply leadingCoeff_pos_iff.mp
    change 0 < (single a b : K⟦Γ⟧).leadingCoeff
    rw [leadingCoeff_of_single]
    exact hbpos
  refine ⟨single a b * u, ?_, ?_⟩
  · change 0 < toLex (single a b : K⟦Γ⟧) * toLex u
    exact mul_pos hmpos (binomialPower_lex_pos ε hε (1 / 2 : ℚ))
  · rw [mul_pow, single_pow, ha, hbsq, hu]
    simp only [ε, add_sub_cancel]
    exact leadingMonomial_mul_leadingNormalized x hx0

/-- Every nonnegative lexicographic Hahn series has a unique nonnegative
square root whenever the coefficient field has this property. -/
theorem existsUnique_nonneg_square_root_of_coefficients
    (hK : ∀ a : K, 0 ≤ a → ∃ b : K, 0 ≤ b ∧ b ^ 2 = a)
    (x : K⟦Γ⟧) (hx : 0 ≤ toLex x) :
    ∃! y : K⟦Γ⟧, 0 ≤ toLex y ∧ y ^ 2 = x := by
  have hex : ∃ y : K⟦Γ⟧, 0 ≤ toLex y ∧ y ^ 2 = x := by
    by_cases hx0 : x = 0
    · exact ⟨0, by simp, by simp [hx0]⟩
    · have hxpos : 0 < toLex x := lt_of_le_of_ne hx (by
        intro h
        exact hx0 (congrArg ofLex h.symm))
      obtain ⟨y, hy, hsq⟩ := exists_pos_square_root_of_coefficients hK x hxpos
      exact ⟨y, hy.le, hsq⟩
  obtain ⟨y, hy, hsq⟩ := hex
  refine ⟨y, ⟨hy, hsq⟩, ?_⟩
  intro z hz
  have heq : (toLex z) ^ 2 = (toLex y) ^ 2 :=
    congrArg (toLex : K⟦Γ⟧ → Lex K⟦Γ⟧) (hz.2.trans hsq.symm)
  exact congrArg ofLex ((sq_eq_sq₀ hz.1 hy).mp heq)

variable [HasNonnegSquareRoots K]

/-- Coefficient-field square roots supply the only field input to the global
Hahn construction. Real-closed coefficient fields satisfy this weaker hypothesis. -/
theorem existsUnique_nonneg_square_root (x : K⟦Γ⟧) (hx : 0 ≤ toLex x) :
    ∃! y : K⟦Γ⟧, 0 ≤ toLex y ∧ y ^ 2 = x :=
  existsUnique_nonneg_square_root_of_coefficients
    (fun _ ha => HasNonnegSquareRoots.exists_nonneg_sq ha) x hx

/-- The constructed square roots instantiate the existing ordered-square-root
interface on the actual lexicographic Hahn field. -/
instance hahnLexHasNonnegSquareRoots : HasNonnegSquareRoots (Lex K⟦Γ⟧) where
  exists_nonneg_sq {x} hx := by
    obtain ⟨y, ⟨hy, hsq⟩, _⟩ := existsUnique_nonneg_square_root (ofLex x) hx
    exact ⟨toLex y, hy, congrArg (toLex : K⟦Γ⟧ → Lex K⟦Γ⟧) hsq⟩

/-- The square-root hypothesis required by `IsRealClosed.of_linearOrderedField`
for the actual lexicographic Hahn field. Odd-degree root existence remains a
separate obligation. -/
theorem isSquare_of_nonneg_lex {x : Lex K⟦Γ⟧} (hx : 0 ≤ x) : IsSquare x := by
  obtain ⟨y, _, hsq⟩ := HasNonnegSquareRoots.exists_nonneg_sq hx
  exact ⟨y, by simpa only [pow_two] using hsq.symm⟩

end

end Surreal.HahnSeries

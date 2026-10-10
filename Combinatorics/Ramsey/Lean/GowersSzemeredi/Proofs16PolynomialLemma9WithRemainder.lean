import GowersSzemeredi.Proofs16PolynomialAllScaleLemma9
import GowersSzemeredi.Proofs16Lemma9WithRemainder

/-! The polynomial all-scale Lemma 16.9 with arbitrary remainder controls.

`Proofs16Lemma9WithRemainder` proves Lemma 16.9 with remainder controls
`(Qr, Er)` from the all-scale Lemma 16.6 for any width that transfers along
cell refinements. Here that width is `section16PolynomialLinearityWidth`,
and Lemma 16.6 is `exists_all_scale_polynomial_lemma_16_6`.
`AllScalePolynomialLemma166At k C p` is definitionally
`AllScaleLemma166WidthAt k (section16PolynomialLinearityWidth · k C p)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The polynomial linearity width transfers along cell refinements. -/
theorem section16PolynomialLinearityWidth_transfer (k C p : Nat) :
    Section16WidthTransfer (fun m q a zeta => section16PolynomialLinearityWidth m k C p q a zeta) := by
  intro m n q a c zeta hz ha _ hcell
  exact section16PolynomialLinearityWidth_le_cell_width hz ha hcell

/-- Lemma 16.9 with a polynomial spectrum-count width and arbitrary
remainder controls, at every input scale. -/
theorem exists_all_scale_polynomial_lemma_16_9_with (k : Nat) :
    ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
      AllScaleLemma169WithAt k
        (fun m q a zeta => section16PolynomialLinearityWidth m k C p q a zeta) := by
  obtain ⟨C, p, hC, hp, hlemma6⟩ := exists_all_scale_polynomial_lemma_16_6 k
  exact ⟨C, p, hC, hp,
    allScaleLemma169WithAt_of k (section16PolynomialLinearityWidth_transfer k C p) hlemma6⟩

end LeanProofs.GowersSzemeredi

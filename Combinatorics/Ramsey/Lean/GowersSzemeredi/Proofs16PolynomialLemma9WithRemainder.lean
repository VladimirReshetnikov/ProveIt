import GowersSzemeredi.Proofs16PolynomialAllScaleLemma9
import GowersSzemeredi.Proofs16Lemma9WithRemainder
import GowersSzemeredi.Proofs16PieceCoverWithRemainder
import GowersSzemeredi.Proofs16FamilyLemma6

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

/-- The polynomial width is a power width, with prefactor `4·C·(q+1)` and
exponent divisor `4·2p(q+1)^(2^(k+2))`. -/
def section16PolynomialWidthPrefactor (C : Nat) (q : Nat) : Real :=
  4 * ((C * (q + 1) : Nat) : Real)

def section16PolynomialWidthDivisor (k p : Nat) (q : Nat) : Real :=
  4 * ((2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) : Nat) : Real)

theorem allScaleLemma166WidthAt_power_of_polynomial (k : Nat) {C p : Nat}
    (h : AllScalePolynomialLemma166At k C p) :
    AllScaleLemma166WidthAt k (section16PowerWidth (section16PolynomialWidthPrefactor C)
      (section16PolynomialWidthDivisor k p)) := h

/-- The polynomial all-scale Lemma 16.6 in the form used by
`section16_piece_cover_with`: a power width with positive prefactor and
divisor. -/
theorem exists_all_scale_power_lemma_16_6 (k : Nat) :
    ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
      AllScaleLemma166WidthAt k (section16PowerWidth (section16PolynomialWidthPrefactor C)
        (section16PolynomialWidthDivisor k p)) := by
  obtain ⟨C, p, hC, hp, hlemma6⟩ := exists_all_scale_polynomial_lemma_16_6 k
  exact ⟨C, p, hC, hp, allScaleLemma166WidthAt_power_of_polynomial k hlemma6⟩

/-- The polynomial recurrence profile is the abstract profile at the shapes
`familyRecThr`, `familyRecExp` (definitional). -/
theorem section16RecurrenceProfileWith_of_polynomial (k K p : Nat)
    (h : PolynomialSection16RecurrenceProfileAt k K p) :
    Section16RecurrenceProfileWith k (familyRecThr k K p) (familyRecExp k p) := h

/-- **Lemma 16.6 for a family of pieces on one partition**, with the
polynomial recurrence. -/
theorem exists_all_scale_family_lemma_16_6 (k : Nat) :
    ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
      AllScaleFamilyLemma166At k
        (section16PowerWidth (familyWidthPrefactor C) (familyWidthDivisor k p)) := by
  obtain ⟨K, p, hK, hp, hrec⟩ := exists_polynomial_section16_recurrence_profile k
  exact ⟨K, p, hK, hp, allScaleFamilyLemma166At_of k hK hp hrec⟩

end LeanProofs.GowersSzemeredi

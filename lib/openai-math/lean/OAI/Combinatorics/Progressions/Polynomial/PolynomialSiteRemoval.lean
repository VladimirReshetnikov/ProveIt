import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace

namespace OAI

section

namespace Erdos3

open MvPolynomial CircleFourier
open scoped BigOperators Classical

theorem finiteSitePhaseRemoval_polynomial {h : ℕ} {S K J X : Type*}
    [Fintype S] [Fintype K] [Fintype X]
    (site : S → K → ℤ) (rows : Fin h → K → ℤ)
    (hremove : FiniteSitePhaseRemoval (X := X) (V := J → ℝ) site rows)
    (base : K → J → ℝ) (shift : X → J → ℝ)
    (P : MvPolynomial (K × J) ℝ) (hP : P.totalDegree ≤ h)
    (test : S → (J → ℝ) → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character ((eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) P : ℝ) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u : Fin h → X, 𝔼 v : Fin h → X, character ((polynomialTopSymbol h P
        (fun i z => (rows i z.1 : ℝ) * (shift (u i) z.2 - shift (v i) z.2)) : ℝ) : CircleFourier.Circle)‖ := by
  have hc := hremove base shift (fun tuple => eval (fun z => tuple z.1 z.2) P) test htest
  simpa only [row_shift_difference_eq_topSymbol base rows shift P hP] using hc

theorem row_polynomial_site_cauchySchwarz {h : ℕ} {S K J X : Type*}
    [Fintype S] [Fintype K] [Fintype X] [Nonempty X] (hh : 0 < h)
    (site : S → K → ℤ) (rows : Fin h → K → ℤ)
    (hzero : ∀ s, ∃ i, (∑ k, rows i k * site s k) = 0)
    (base : K → J → ℝ) (shift : X → J → ℝ)
    (P : MvPolynomial (K × J) ℝ) (hP : P.totalDegree ≤ h)
    (test : S → (J → ℝ) → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1) :
    ‖𝔼 x, character ((eval (fun z => rowShiftedTuple base rows shift x z.1 z.2) P : ℝ) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) (rowShiftedTuple base rows shift x))‖ ^ (2 ^ h) ≤
      ‖𝔼 u : Fin h → X, 𝔼 v : Fin h → X, character ((polynomialTopSymbol h P
        (fun i z => (rows i z.1 : ℝ) * (shift (u i) z.2 - shift (v i) z.2)) : ℝ) : CircleFourier.Circle)‖ :=
  finiteSitePhaseRemoval_polynomial site rows
    (finiteSitePhaseRemoval_of_annihilates hh site rows hzero) base shift P hP test htest

end Erdos3

end

end OAI

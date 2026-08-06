import PolynomialFormulas.GaussianPolynomialApproximationNormalization
import PolynomialFormulas.GaussianPolynomialApproximationCertificateExistence
import PolynomialFormulas.GaussianPolynomialApproximationCorrectness

/-!
# Fully executable Gaussian-rational approximations to quartic roots

`approximations` accepts all five Gaussian-rational coefficients, including
leading zeros, a proof that they are not all zero, and a positive rational
tolerance.  It returns one literal Gaussian rational per complex root,
counted with multiplicity.  The vector length is the actual degree computed
from the input coefficient array.

The program normalizes the input over the Gaussian rationals and exhaustively
searches a decidable certificate predicate.  A certificate consists of exact
rational factor coefficients and rational contraction disks.  Its existence
theorem is used only as the erased termination proof for `Nat.find`; the data
path contains only finite arrays, natural numbers, Booleans, and exact
Gaussian-rational arithmetic.

`approximations_correct` pairs the output, position for position, with the
complete complex root multiset and proves the requested Manhattan error.
-/

namespace LeanProofs.PolynomialFormulas

namespace GaussianPolynomialApproximation

open GaussianPolynomialSolver
open GaussianPolynomialApproximationCore
open GaussianPolynomialApproximationCore.QPoly
open GaussianPolynomialApproximationNormalization
open GaussianPolynomialApproximationSearch
open GaussianPolynomialApproximationCertificateExistence
open GaussianPolynomialApproximationCorrectness

/-- The first valid finite rational certificate found by exhaustive search. -/
def certificate (c : Coefficients) (ε : ℚ) (hc : Nonzero c) (hε : 0 < ε) :
    RawCertificate :=
  search (monic c) ε (exists_valid_certificate (monic c) (monic_is_monic hc) hε)

theorem certificate_isValid (c : Coefficients) (ε : ℚ)
    (hc : Nonzero c) (hε : 0 < ε) :
    IsValid (monic c) ε (certificate c ε hc hε) :=
  search_isValid _ _ _

/-- Fully executable Gaussian-rational approximations to all roots, with
multiplicity.  A nonzero constant returns the empty vector. -/
def approximations (c : Coefficients) (ε : ℚ) (hc : Nonzero c) (hε : 0 < ε) :
    List.Vector GaussianRat (degree (toQPoly c)) :=
  ⟨centersList (certificate c ε hc hε), by
    rw [centersList_length, (certificate_isValid c ε hc hε).degreeSum]
    exact degree_monic hc⟩

/-- The output is position-for-position within rational tolerance `ε` of a
list containing exactly the input polynomial's complex roots, including all
multiplicities. -/
theorem approximations_correct (c : Coefficients) (ε : ℚ)
    (hc : Nonzero c) (hε : 0 < ε) :
    ∃ roots : List ℂ,
      (roots : Multiset ℂ) = (toComplexPolynomial (toQPoly c)).roots ∧
      List.Forall₂
        (fun center root =>
          GaussianRat.complexManhattan root (GaussianRat.toComplex center) ≤ (ε : ℝ))
        (approximations c ε hc hε).toList roots := by
  let raw := certificate c ε hc hε
  have hvalid : IsValid (monic c) ε raw := certificate_isValid c ε hc hε
  refine ⟨exactRootsList raw hvalid, ?_, ?_⟩
  · rw [exactRootsList_multiset hvalid]
    exact roots_monic_eq hc
  · simpa [approximations, raw] using centersList_forall₂_exactRootsList hvalid

/-! ## Native execution smoke test -/

private def linearExample : Coefficients where
  a4 := 0
  a3 := 0
  a2 := 0
  a1 := 1
  a0 := -2

private theorem linearExample_nonzero : Nonzero linearExample := by
  unfold Nonzero
  native_decide

example :
    (approximations linearExample 1 linearExample_nonzero (by norm_num)).toList =
      [(2 : GaussianRat)] := by
  native_decide

private def constantExample : Coefficients where
  a4 := 0
  a3 := 0
  a2 := 0
  a1 := 0
  a0 := 7

private theorem constantExample_nonzero : Nonzero constantExample := by
  unfold Nonzero
  native_decide

example :
    (approximations constantExample (1 / 10) constantExample_nonzero
      (by norm_num)).toList = [] := by
  native_decide

private def quadraticExample : Coefficients where
  a4 := 0
  a3 := 0
  a2 := 1
  a1 := 0
  a0 := -1

private theorem quadraticExample_nonzero : Nonzero quadraticExample := by
  unfold Nonzero
  native_decide

example :
    (approximations quadraticExample (1 / 10) quadraticExample_nonzero
      (by norm_num)).toList = [(1 : GaussianRat), -1] := by
  native_decide

private def quarticExample : Coefficients where
  a4 := 1
  a3 := 0
  a2 := -5
  a1 := 0
  a0 := 4

private theorem quarticExample_nonzero : Nonzero quarticExample := by
  unfold Nonzero
  native_decide

example :
    (approximations quarticExample (1 / 10) quarticExample_nonzero
      (by norm_num)).toList = [(1 : GaussianRat), -1, 2, -2] := by
  native_decide

end GaussianPolynomialApproximation

end LeanProofs.PolynomialFormulas

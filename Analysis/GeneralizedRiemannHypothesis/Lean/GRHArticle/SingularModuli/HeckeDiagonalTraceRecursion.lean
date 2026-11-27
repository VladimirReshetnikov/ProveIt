import GRHArticle.SingularModuli.HeckeDiagonalFiniteCertificate
import GRHArticle.SingularModuli.HeckeTraceCoefficientFormula
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# A rational trace recurrence for prime Hecke diagonals

Newton's identities recover the elementary symmetric series from the traces
in the ordinary `q` variable. This keeps the certificate in rational series
arithmetic and limits the number of coefficients that need to be compared.
-/

namespace GRHArticle.SingularModuli

open PowerSeries
open scoped PowerSeries
local notation "mapIntQ" => PowerSeries.map (Int.castRingHom ℚ)
local notation "mapIntC" => PowerSeries.map (Int.castRingHom ℂ)
local notation "mapQC" => PowerSeries.map (Rat.castHom ℂ)
local notation "χ" => ZMod.stdAddChar

/-- The elementary symmetric functions of the shifted series, computed
recursively by Newton's identities. -/
noncomputable def heckeElementarySeries (p : ℕ) (F : ℤ⟦X⟧) : ℕ → ℚ⟦X⟧
  | 0 => 1
  | n + 1 => C ((↑(n + 1) : ℚ)⁻¹) * (-1) ^ (n + 2) *
    ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) * heckeElementarySeries p F i *
      mapIntQ (heckeTraceSeries p (n + 1 - i) F)
termination_by n => n
decreasing_by exact i.isLt

private noncomputable def heckeShiftSeries {p : ℕ} [NeZero p]
    (F : ℤ⟦X⟧) (t : ZMod p) : ℂ⟦X⟧ :=
  C (χ (-t)) * X ^ (p - 1) * rescale (χ t) (mapIntC F)

private theorem mapQC_mapIntQ (F : ℤ⟦X⟧) : mapQC (mapIntQ F) = mapIntC F := by
  ext n
  simp only [coeff_map, Rat.coe_castHom, Int.coe_castRingHom, Rat.cast_intCast]

private theorem nat_mul_esymm_eq_sum {R α : Type*} [CommRing R] [Fintype α]
    (f : α → R) (n : ℕ) :
    (↑(n + 1) : R) * ((Finset.univ : Finset α).val.map f).esymm (n + 1) =
      (-1) ^ (n + 2) * ∑ i : Fin (n + 1),
        (-1) ^ (i : ℕ) * ((Finset.univ : Finset α).val.map f).esymm i *
          (∑ t : α, f t ^ (n + 1 - i)) := by
  classical
  have H := congrArg (MvPolynomial.aeval (R := R) f)
    (MvPolynomial.mul_esymm_eq_sum α R (n + 1))
  simp only [map_mul, map_pow, map_natCast, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X] at H
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range] at H
  simp only [lt_irrefl, if_false, add_zero, Fin.isLt, if_true] at H
  exact H

private theorem expand_heckeElementarySeries_eq_esymm (p : ℕ) [hp : Fact (Nat.Prime p)]
    (F : ℤ⟦X⟧) (k : ℕ) :
    expand p hp.out.ne_zero (mapQC (heckeElementarySeries p F k)) =
      ((Finset.univ : Finset (ZMod p)).val.map (heckeShiftSeries F)).esymm k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [heckeElementarySeries, Multiset.esymm]
    | succ n =>
      have h (i : Fin (n + 1)) := ih i i.isLt
      have htrace (i : Fin (n + 1)) :
          expand p hp.out.ne_zero (mapIntC (heckeTraceSeries p (n + 1 - i) F)) =
            ∑ t : ZMod p, (heckeShiftSeries F t) ^ (n + 1 - i) := by
        symm
        simpa only [heckeShiftSeries] using sum_heckeShift_powers_eq_expand_trace p (n + 1 - i) F
      simp only [heckeElementarySeries, map_mul, map_pow, map_neg, map_one, map_sum,
        map_C, expand_C, Rat.coe_castHom, Rat.cast_inv, Rat.cast_natCast,
        mapQC_mapIntQ, h, htrace]
      have hRec := nat_mul_esymm_eq_sum (heckeShiftSeries (p := p) F) n
      rw [mul_assoc, ← hRec, ← mul_assoc]
      have hn : (↑(n + 1) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
      rw [← map_natCast (C : ℂ →+* ℂ⟦X⟧) (n + 1), ← map_mul, inv_mul_cancel₀ hn,
        map_one, one_mul]


private theorem prod_sub_eq_sum_esymm {α R : Type*} [Fintype α] [CommRing R]
    (a : R) (f : α → R) :
    (∏ t : α, (a - f t)) = ∑ k ∈ Finset.range (Fintype.card α + 1),
      (-1) ^ k * ((Finset.univ : Finset α).val.map f).esymm k * a ^ (Fintype.card α - k) := by
  let s := (Finset.univ : Finset α).val.map f
  have h := congrArg (Polynomial.eval a) (Multiset.prod_X_sub_X_eq_sum_esymm s)
  change (Polynomial.eval a) _ = (Polynomial.eval a) _ at h
  rw [Polynomial.eval_multiset_prod, Polynomial.eval_finsetSum] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub, Multiset.map_map,
    Function.comp_def] at h
  have hcard : Multiset.card s = Fintype.card α := by simp [s]
  rw [hcard] at h
  simpa only [s, Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod, mul_assoc] using h

/-- The cleared, signed diagonal series in the ordinary cusp variable
`q`. All operations have rational arguments and coefficients. -/
noncomputable def heckeDiagonalTraceSeries (p : ℕ+) (F : ℤ⟦X⟧) : ℚ⟦X⟧ :=
  let m : ℕ := p
  let G := mapIntQ F
  (expand m p.pos.ne' G - X ^ (m - 1) * G) *
    ∑ k ∈ Finset.range (m + 1), (-1) ^ k * heckeElementarySeries m F k * G ^ (m - k)

/-- Expanding the rational trace computation into the ramified cusp
variable gives the exact analytic diagonal series. -/
theorem expand_heckeDiagonalTraceSeries_eq_primeHeckeDiagonalSeries (p : ℕ+)
    [Fact (Nat.Prime (p : ℕ))] :
    expand (p : ℕ) p.pos.ne' (mapQC (heckeDiagonalTraceSeries p integralNormalizedJExpansion)) =
      primeHeckeDiagonalSeries p := by
  let m : ℕ := p
  let F := integralNormalizedJExpansion
  let A := expand m p.pos.ne' (mapIntC F)
  have hprod := prod_sub_eq_sum_esymm A (heckeShiftSeries (p := m) F)
  rw [ZMod.card] at hprod
  simp only [heckeDiagonalTraceSeries, map_mul, map_sub, map_pow, map_neg, map_one, map_X,
    map_sum, map_expand, expand_X, mapQC_mapIntQ, expand_heckeElementarySeries_eq_esymm]
  rw [← expand_mul, ← pow_mul, Nat.mul_sub_left_distrib, Nat.mul_one]
  change _ * (∑ k ∈ Finset.range (m + 1), (-1) ^ k *
    ((Finset.univ : Finset (ZMod m)).val.map (heckeShiftSeries F)).esymm k * A ^ (m - k)) = _
  rw [← hprod]
  rfl

/-- Clearing a proposed polynomial in the ordinary cusp variable uses
the same triangular recurrence over the rationals. -/
noncomputable def clearedRationalPolynomialEvaluation (P : Polynomial ℤ) (A : ℚ⟦X⟧) :
    ℕ → ℚ⟦X⟧
  | 0 => C (P.coeff 0 : ℚ)
  | n + 1 => X * clearedRationalPolynomialEvaluation P A n +
      C (P.coeff (n + 1) : ℚ) * A ^ (n + 1)

private theorem expand_clearedRationalPolynomialEvaluation (p : ℕ+) (P : Polynomial ℤ)
    (n : ℕ) (F : ℤ⟦X⟧) :
    expand (p : ℕ) p.pos.ne'
      (mapQC (clearedRationalPolynomialEvaluation P (mapIntQ F) n)) =
    clearedSeriesPolynomialEvaluation (P.map (Int.castRingHom ℂ)) (p : ℕ)
      (expand (p : ℕ) p.pos.ne' (mapIntC F)) n := by
  induction n with
  | zero =>
    simp [clearedRationalPolynomialEvaluation, clearedSeriesPolynomialEvaluation]
  | succ n ih =>
    simp [clearedRationalPolynomialEvaluation, clearedSeriesPolynomialEvaluation, ih, mapQC_mapIntQ]

/-- It suffices to compare `2*p+1` ordinary rational coefficients of the
recurrence and the proposed cleared diagonal. -/
theorem primeHeckeDiagonalEval_eq_of_rationalCertificate (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (P : Polynomial ℤ) (hP : P.natDegree ≤ 2 * (p : ℕ))
    (hcert : ∀ k ≤ 2 * (p : ℕ),
      (heckeDiagonalTraceSeries p integralNormalizedJExpansion).coeff k =
        (clearedRationalPolynomialEvaluation P (mapIntQ integralNormalizedJExpansion)
          (2 * (p : ℕ))).coeff k) :
    ∀ z : UpperHalfPlane, Polynomial.aeval (modularInvariant z) P =
      -analyticPrimeHeckeDiagonal p z := by
  apply primeHeckeDiagonalEval_eq_of_finiteCertificate p P hP
  intro k hk
  rw [← expand_heckeDiagonalTraceSeries_eq_primeHeckeDiagonalSeries p,
    ← expand_clearedRationalPolynomialEvaluation, coeff_expand_mul, coeff_expand_mul,
    coeff_map, coeff_map, hcert k hk]

end GRHArticle.SingularModuli

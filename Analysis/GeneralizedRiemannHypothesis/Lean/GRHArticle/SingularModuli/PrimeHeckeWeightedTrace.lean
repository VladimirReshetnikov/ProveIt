import GRHArticle.SingularModuli.HeckeTraceCoefficientFormula
import GRHArticle.SingularModuli.HeckePackedSeriesCertificate
import GRHArticle.SingularModuli.HeckeChunkedPrefixCertificate
import GRHArticle.SingularModuli.HeckeWeightedCoefficientBound

/-!
# Checking a normalized Hecke trace with dyadic packed coefficients

At trace index `k` only the coefficients at degrees `p*i - (p-1)*k`
of the normalized invariant power can contribute. Truncating the input
and using its dyadic bound keeps the integer arithmetic small.
-/

namespace GRHArticle.SingularModuli

open scoped PowerSeries

/-- Number of input coefficients needed for `M` output coefficients of trace `k`. -/
def heckeTraceInputLength (p k M : ℕ) : ℕ :=
  p*(M-1) - (p-1)*k + 1

/-- Compute a row using only the necessary input prefix. -/
def weightedHeckeTraceRow (p k M w : ℕ) (a : List ℕ) : List ℤ :=
  let N := heckeTraceInputLength p k M
  let Q := packedNaturalPolynomialPowerAtChunkWidth N
    (polynomialDigitChunks (a.take N)) k (w*k+N)
  List.ofFn fun i : Fin M ↦
    if (p-1)*k ≤ p*(i : ℕ) then
      (p : ℤ) * (packedNaturalPolynomialPowerCoeff Q (p*(i : ℕ)-(p-1)*k) : ℤ) else 0

private theorem map_coefficientListPolynomial {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (l : List R) :
    (coefficientListPolynomial l).map f = coefficientListPolynomial (l.map f) := by
  induction l with
  | nil => simp [coefficientListPolynomial]
  | cons a l ih =>
    simp [coefficientListPolynomial, Polynomial.map_add, Polynomial.map_mul, ih]

/-- The checked integer row agrees with the actual normalized Hecke trace. -/
theorem weightedHeckeTraceRow_spec (p k M w N : ℕ) (a : List ℕ) (F : ℤ⟦X⟧)
    (hN : p*(M-1)+1 ≤ N) (ha : SeriesPrefix N (a.map Int.ofNat) F)
    (hwidth : dyadicScaledEvaluation a ≤ 2^(a.length+w)) :
    SeriesPrefix M (weightedHeckeTraceRow p k M w a) (heckeTraceSeries p k F) := by
  let L := heckeTraceInputLength p k M
  have hL : L ≤ N := (Nat.add_le_add_right (Nat.sub_le _ _) 1).trans hN
  let b := a.take L
  have hB : SeriesPrefix L (b.map Int.ofNat) F := by
    intro i
    change (((a.take L).map Int.ofNat).getD i 0) = F.coeff i
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt i.isLt,
      ← List.getElem?_map, ← List.getD_eq_getElem?_getD]
    exact ha ⟨i, i.isLt.trans_le hL⟩
  have he := IntegerPolynomialExpression.pow_spec
    (IntegerPolynomialExpression.coefficients_spec hB) k
  intro i
  simp only [weightedHeckeTraceRow, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt,
    dif_pos, Option.getD_some, heckeTraceSeries, PowerSeries.coeff_mk]
  split_ifs
  · let d := p*(i : ℕ)-(p-1)*k
    have hi' : (i : ℕ) ≤ M-1 := by have := i.isLt; omega
    have hd : d < L := Nat.lt_succ_of_le
      (Nat.sub_le_sub_right (Nat.mul_le_mul_left p hi') _)
    rw [packedNaturalPolynomialPowerAtChunkWidth_eq, flatten_polynomialDigitChunks,
      packedNaturalPolynomialPowerCoeff_eq_of_dyadicBound _ _ _ _ _
        (dyadicScaledEvaluation_le_take a w L hwidth) hd]
    have hcast : ((coefficientListPolynomial b ^ k).coeff d : ℤ) =
        (coefficientListPolynomial (b.map Int.ofNat) ^ k).coeff d := by
      have hmap : (coefficientListPolynomial b ^ k).map (Nat.castRingHom ℤ) =
          coefficientListPolynomial (b.map Int.ofNat) ^ k := by
        rw [Polynomial.map_pow, map_coefficientListPolynomial]
        rfl
      have h := congrArg (fun P : Polynomial ℤ ↦ P.coeff d) hmap
      rw [Polynomial.coeff_map] at h
      exact h
    change (p : ℤ) * ((coefficientListPolynomial b ^ k).coeff d : ℤ) = _
    rw [hcast]
    exact congrArg ((p : ℤ) * ·) (he ⟨d, hd⟩)
  · rfl

end GRHArticle.SingularModuli

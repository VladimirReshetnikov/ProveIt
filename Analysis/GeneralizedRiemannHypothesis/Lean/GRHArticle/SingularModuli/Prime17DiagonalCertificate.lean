import GRHArticle.SingularModuli.Prime17DiagonalData
import GRHArticle.SingularModuli.HeckePackedSeriesCertificate
import GRHArticle.SingularModuli.HeckeComputedDiagonalCertificate

/-!
# Soundness of the staged level-17 diagonal certificate

Separate checks verify the discriminant and invariant prefixes, trace rows,
elementary rows, and the final cleared polynomial identity.
-/

namespace GRHArticle.SingularModuli
namespace Prime17Data

open scoped PowerSeries
open IntegerPolynomialExpression

set_option maxRecDepth 4000

local notation "cs" => IntegerPolynomialExpression.coefficients
local notation "Delta" => integralDiscriminantExpansion
local notation "D" => integralNormalizedDiscriminantExpansion
local notation "J" => integralNormalizedJExpansion

private theorem getD_zipWith {l r : List ℕ} (f : ℕ → ℕ → ℤ) {i : ℕ}
    (hl : i < l.length) (hr : i < r.length) :
    (List.zipWith f l r).getD i 0 = f (l.getD i 0) (r.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hr, Option.getD_some]

private theorem sigmaCoefficients_spec (N k : ℕ) (hN : N ≤ 580) (hk : k = 3 ∨ k = 5) :
    (cs (sigmaCoefficients N k)).AgreesWith N (divisorPowerSeries k) := by
  apply coefficients_spec
  intro i
  have hi := i.isLt.trans_le hN
  rcases hk with rfl | rfl
  · rw [sigmaCoefficients, if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_take_of_lt i.isLt,
      List.getElem?_eq_getElem (by simpa only [length_sigma3Prefix] using hi),
      Option.map_some, Option.getD_some, divisorPowerSeries, PowerSeries.coeff_mk]
    have e := getD_sigma3Prefix i hi
    have hlist : (i : ℕ) < sigma3Prefix.length := by simpa only [length_sigma3Prefix] using hi
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlist, Option.getD_some, Int.ofNat_eq_natCast] using
      congrArg (fun a : ℕ ↦ (a : ℤ)) e
  · rw [sigmaCoefficients, if_neg (by decide), List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_take_of_lt i.isLt,
      List.getElem?_eq_getElem (by simpa only [length_sigma5Prefix] using hi),
      Option.map_some, Option.getD_some, divisorPowerSeries, PowerSeries.coeff_mk]
    have e := getD_sigma5Prefix i hi
    have hlist : (i : ℕ) < sigma5Prefix.length := by simpa only [length_sigma5Prefix] using hi
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlist, Option.getD_some, Int.ofNat_eq_natCast] using
      congrArg (fun a : ℕ ↦ (a : ℤ)) e

private theorem expr_discriminant_spec : discriminantExpr.AgreesWith 580 Delta := by
  let σ := ArithmeticFunction.sigma
  let t (n : ℕ) := (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ)
  have hL : (cs linearDiscriminantCoefficients).AgreesWith 580 (PowerSeries.mk t) := by
    apply coefficients_spec
    intro i
    have h3 : (i : ℕ) < sigma3Prefix.length := by rw [length_sigma3Prefix]; exact i.isLt
    have h5 : (i : ℕ) < sigma5Prefix.length := by rw [length_sigma5Prefix]; exact i.isLt
    rw [linearDiscriminantCoefficients, getD_zipWith _ h3 h5,
      getD_sigma3Prefix i i.isLt, getD_sigma5Prefix i i.isLt, PowerSeries.coeff_mk]
  have h := sub_spec
    (add_spec (add_spec hL (mul_spec (constant_spec 100) (pow_spec (sigmaCoefficients_spec 580 3 (by decide) (Or.inl rfl)) 2)))
      (mul_spec (constant_spec 8000) (pow_spec (sigmaCoefficients_spec 580 3 (by decide) (Or.inl rfl)) 3)))
    (mul_spec (constant_spec 147) (pow_spec (sigmaCoefficients_spec 580 5 (by decide) (Or.inr rfl)) 2))
  unfold discriminantExpr
  change IntegerPolynomialExpression.AgreesWith _ 580
    (PowerSeries.mk t + 100 * divisorPowerSeries 3 ^ 2 +
      8000 * divisorPowerSeries 3 ^ 3 - 147 * divisorPowerSeries 5 ^ 2)
  simpa only [map_ofNat] using h

private theorem discriminant_spec_of_check (h : DiscriminantCheck) :
    SeriesPrefix 579 discriminant D := by
  let A : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ discriminant.getD n 0
  have hA : SeriesPrefix 580 discriminant A := by intro i; simp only [A, PowerSeries.coeff_mk]
  intro i
  let j : Fin 580 := ⟨(i:ℕ)+1, Nat.succ_lt_succ i.isLt⟩
  have hs := series_prefix_eq_of_check h (mul_spec X_spec (coefficients_spec hA))
    expr_discriminant_spec j
  change (PowerSeries.X * A).coeff ((i:ℕ)+1) = PowerSeries.coeff ((i:ℕ)+1) Delta at hs
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk] at hs
  simpa only [integralNormalizedDiscriminantExpansion, PowerSeries.coeff_mk] using hs

private theorem expr_eisensteinCubed_spec :
    eisensteinCubedExpr.AgreesWith 579 ((1 + 240 * divisorPowerSeries 3)^3) := by
  have h := pow_spec
    (add_spec (constant_spec 1) (mul_spec (constant_spec 240) (sigmaCoefficients_spec 579 3 (by decide) (Or.inl rfl)))) 3
  simpa only [eisensteinCubedExpr, map_one, map_ofNat] using h

private theorem invariant_spec_of_checks (hD : DiscriminantCheck) (hJ : InvariantCheck) :
    SeriesPrefix 579 invariant J := by
  let A : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ invariant.getD n 0
  let E : ℤ⟦X⟧ := (1 + 240 * divisorPowerSeries 3)^3
  have hA : SeriesPrefix 579 invariant A := by intro i; simp only [A, PowerSeries.coeff_mk]
  have hc : PowerSeries.X^579 ∣ D * A - E := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro i hi
    rw [map_sub, sub_eq_zero]
    exact series_prefix_eq_of_check hJ
      (mul_spec (coefficients_spec (discriminant_spec_of_check hD)) (coefficients_spec hA))
      expr_eisensteinCubed_spec ⟨i, hi⟩
  let I := PowerSeries.invOfUnit D 1
  have hI : I * D = 1 :=
    PowerSeries.invOfUnit_mul D 1 constantCoeff_integralNormalizedDiscriminantExpansion
  have hId : I * (D * A - E) = A - J := by
    change I * (D * A - E) = A - E * I
    rw [mul_sub, ← mul_assoc, hI, one_mul, mul_comm I E]
  have hd : PowerSeries.X^579 ∣ A - J := hId ▸ dvd_mul_of_dvd_right hc I
  intro i
  have hi := (PowerSeries.X_pow_dvd_iff.mp hd) i i.isLt
  rw [map_sub, sub_eq_zero] at hi
  exact (hA i).trans hi

private theorem map_coefficientListPolynomial {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (l : List R) :
    (coefficientListPolynomial l).map f = coefficientListPolynomial (l.map f) := by
  induction l with
  | nil => simp [coefficientListPolynomial]
  | cons a l ih =>
    simp [coefficientListPolynomial, Polynomial.map_add, Polynomial.map_mul, ih]

private theorem trace_spec_of_checks (hD : DiscriminantCheck) (hJ : InvariantCheck)
    (hNonneg : ∀ a ∈ invariant, 0 ≤ a) (k : ℕ) (h : TraceCheck k) :
    SeriesPrefix 35 traceTable[k]! (heckeTraceSeries 17 k J) := by
  intro i
  rw [← h]
  have ht : (invariant.map Int.toNat).map (Nat.castRingHom ℤ) = invariant := by
    rw [List.map_map]
    calc
      invariant.map (Nat.castRingHom ℤ ∘ Int.toNat) = invariant.map id :=
        List.map_congr_left (fun a ha ↦ Int.toNat_of_nonneg (hNonneg a ha))
      _ = invariant := List.map_id _
  have hPoly :
      (coefficientListPolynomial (invariant.map Int.toNat)).map (Nat.castRingHom ℤ) =
        coefficientListPolynomial invariant := by
    rw [map_coefficientListPolynomial, ht]
  have hFull := pow_spec (coefficients_spec (invariant_spec_of_checks hD hJ)) k
  simp only [packedTraceRow, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dif_pos,
    Option.getD_some, heckeTraceSeries, PowerSeries.coeff_mk]
  split_ifs
  · have hb : 17 * (i : ℕ) - 16*k < 579 := by have := i.isLt; omega
    rw [packedNaturalPolynomialPowerCoeff_eq _ _ _ _ hb]
    have hm := congrArg (fun P : Polynomial ℤ ↦ P.coeff (17*(i : ℕ)-16*k))
      (congrArg (fun P : Polynomial ℤ ↦ P^k) hPoly)
    change ((coefficientListPolynomial (invariant.map Int.toNat)).map
      (Nat.castRingHom ℤ) ^ k).coeff _ = _ at hm
    rw [← Polynomial.map_pow, Polynomial.coeff_map] at hm
    change (17 : ℤ) * (Nat.castRingHom ℤ) ((coefficientListPolynomial (invariant.map Int.toNat)^k).coeff _) =
      17 * _
    rw [hm]
    exact congrArg ((17 : ℤ) * ·) (hFull ⟨17*(i : ℕ)-16*k, hb⟩)
  · rfl

private theorem elementary_spec_of_checks
    (hTrace : ∀ k ≤ 17, SeriesPrefix 35 traceTable[k]! (heckeTraceSeries 17 k J))
    (hZero : ElementaryZeroCheck) (hRec : ∀ n < 17, ElementaryCheck n)
    (k : ℕ) (hk : k ≤ 17) :
    SeriesPrefix 35 elementaryTable[k]! (heckeScaledElementarySeries 17 J k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    let A : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ elementaryTable[k]!.getD n 0
    have hA : (cs elementaryTable[k]!).AgreesWith 35 A :=
      coefficients_spec (by intro i; simp only [A, PowerSeries.coeff_mk])
    cases k with
    | zero =>
      intro i
      have hs := series_prefix_eq_of_check hZero hA (constant_spec 1) i
      simpa only [A, PowerSeries.coeff_mk, heckeScaledElementarySeries, map_one] using hs
    | succ n =>
      have rhs (i : Fin (n+1)) :=
        mul_spec (constant_spec ((-1 : ℤ) ^ (n+2+(i : ℕ)) * ↑(n.factorial/(i : ℕ).factorial)))
          (mul_spec (coefficients_spec (ih i i.isLt (Nat.le_of_lt i.isLt |>.trans hk)))
            (coefficients_spec (hTrace (n+1-i) ((Nat.sub_le _ _).trans hk))))
      have hs := sum_spec _ _ rhs
      have hrhs : (elementaryRecurrenceExpr n).AgreesWith 35 (heckeScaledElementarySeries 17 J (n+1)) := by
        unfold elementaryRecurrenceExpr
        convert hs using 1
        rw [heckeScaledElementarySeries, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [map_mul, map_pow, map_neg, map_one, pow_add]
        ring
      intro i
      simpa only [A, PowerSeries.coeff_mk] using
        series_prefix_eq_of_check (hRec n (Nat.lt_of_succ_le hk)) hA hrhs i

private theorem scaledDiagonalExpr_spec
    (hJ : SeriesPrefix 579 invariant J)
    (hElem : ∀ k ≤ 17, SeriesPrefix 35 elementaryTable[k]! (heckeScaledElementarySeries 17 J k)) :
    scaledDiagonalExpr.AgreesWith 35 (heckeScaledDiagonalTraceSeries 17 J) := by
  have hshort : SeriesPrefix 35 invariantShort J := by
    intro i
    rw [invariantShort, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt,
      ← List.getD_eq_getElem?_getD]
    exact hJ ⟨i, i.isLt.trans_le (by decide)⟩
  have hJexpr := coefficients_spec hshort
  have hExp : (cs expandedInvariantCoefficients).AgreesWith 35
      (PowerSeries.expand 17 (by decide) J) :=
    coefficients_spec (SeriesPrefix.substitutePower_spec hshort 17 (by decide))
  have hfront := sub_spec hExp (mul_spec (pow_spec X_spec 16) hJexpr)
  have hterms (k : Fin 18) :=
    mul_spec (constant_spec ((-1 : ℤ) ^ (k : ℕ) * ↑((17 : ℕ).factorial / (k : ℕ).factorial)))
      (mul_spec (coefficients_spec (hElem k (Nat.lt_succ_iff.mp k.isLt))) (pow_spec hJexpr (17-k)))
  have h := mul_spec hfront (sum_spec _ _ hterms)
  unfold scaledDiagonalExpr heckeScaledDiagonalTraceSeries
  convert h using 1
  · simp only [xExpr, shortInvariantExpr]
  · change _ * (∑ k ∈ Finset.range 18, _) = _
    rw [← Fin.sum_univ_eq_sum_range]
    let A := PowerSeries.expand 17 (by decide) J - PowerSeries.X ^ 16 * J
    change A * _ = A * _
    refine congrArg (fun S : ℤ⟦X⟧ ↦ A * S) ?_
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    change (-1 : ℤ⟦X⟧) ^ (k : ℕ) *
        PowerSeries.C (((17 : ℕ).factorial / (k : ℕ).factorial : ℕ) : ℤ) *
        heckeScaledElementarySeries 17 J k * J ^ (17 - (k : ℕ)) = _
    rw [map_mul, map_pow, map_neg, map_one]
    ring

private theorem clearedDiagonalExpr_spec (hJ : SeriesPrefix 579 invariant J) (n : ℕ) :
    (clearedDiagonalExpr n).AgreesWith 35
      (clearedIntegerPolynomialEvaluation (coefficientListPolynomial diagonal) J n) := by
  have hshort : SeriesPrefix 35 invariantShort J := by
    intro i
    rw [invariantShort, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt,
      ← List.getD_eq_getElem?_getD]
    exact hJ ⟨i, i.isLt.trans_le (by decide)⟩
  have hJe := coefficients_spec hshort
  induction n with
  | zero =>
    simpa only [clearedDiagonalExpr, xExpr, shortInvariantExpr, clearedIntegerPolynomialEvaluation,
      coeff_coefficientListPolynomial]
      using (constant_spec (N := 35) (diagonal.getD 0 0))
  | succ n ih =>
    simpa only [clearedDiagonalExpr, xExpr, shortInvariantExpr, clearedIntegerPolynomialEvaluation,
      coeff_coefficientListPolynomial]
      using add_spec (mul_spec X_spec ih)
        (mul_spec (constant_spec (diagonal.getD (n+1) 0)) (pow_spec hJe (n+1)))

/-- The finite staged checks identify the entire analytic level-17 diagonal. -/
theorem diagonalEval_eq_of_packed_checks
    (hD : DiscriminantCheck) (hJ : InvariantCheck)
    (hNonneg : ∀ a ∈ invariant, 0 ≤ a) (hTrace : ∀ k ≤ 17, TraceCheck k)
    (hZero : ElementaryZeroCheck) (hElem : ∀ n < 17, ElementaryCheck n)
    (hDiag : DiagonalCheck) :
    ∀ z : UpperHalfPlane, Polynomial.aeval (modularInvariant z)
      (coefficientListPolynomial diagonal) = -analyticPrimeHeckeDiagonal 17 z := by
  letI : Fact (Nat.Prime ((17 : ℕ+) : ℕ)) := ⟨by decide⟩
  apply primeHeckeDiagonalEval_eq_of_integerCertificate 17 _
    (natDegree_coefficientListPolynomial_le (by decide))
  intro k hk
  have hI := invariant_spec_of_checks hD hJ
  have helem := elementary_spec_of_checks
    (fun i hi ↦ trace_spec_of_checks hD hJ hNonneg i (hTrace i hi)) hZero hElem
  have he := series_prefix_eq_of_check hDiag (scaledDiagonalExpr_spec hI helem)
    (mul_spec (constant_spec ((17 : ℕ).factorial : ℤ)) (clearedDiagonalExpr_spec hI 34))
    ⟨k, Nat.lt_succ_of_le hk⟩
  rw [PowerSeries.coeff_C_mul] at he
  exact he

end Prime17Data
end GRHArticle.SingularModuli

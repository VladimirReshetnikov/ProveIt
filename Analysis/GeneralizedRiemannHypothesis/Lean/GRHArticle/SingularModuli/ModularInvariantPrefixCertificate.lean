import GRHArticle.SingularModuli.ModularIntegralExpansions
import GRHArticle.SingularModuli.HeckePackedSeriesCertificate
import GRHArticle.SingularModuli.HeckeChunkedPrefixCertificate

/-!
# Finite certificates for the normalized modular invariant

Two finite products identify a discriminant prefix and then a prefix of
the invariant. The coefficients of the normalized discriminant start
with one, so the second product check determines the invariant uniquely.
-/

namespace GRHArticle.SingularModuli

open scoped PowerSeries
open IntegerPolynomialExpression

namespace ModularInvariantPrefixCertificate

local notation "cs" => IntegerPolynomialExpression.coefficients
local notation "Delta" => integralDiscriminantExpansion
local notation "D" => integralNormalizedDiscriminantExpansion
local notation "J" => integralNormalizedJExpansion

/-- The formula for the linear part of the discriminant. -/
def linearCoefficients (a b : List ℕ) : List ℤ :=
  List.zipWith (fun x y ↦ (((5*x + 7*y) / 12 : ℕ) : ℤ)) a b

/-- The integral discriminant formula in terms of the two divisor sums. -/
def discriminantExpr (a b : List ℕ) : IntegerPolynomialExpression :=
  let A := cs (a.map Int.ofNat)
  let B := cs (b.map Int.ofNat)
  sub (add (add (cs (linearCoefficients a b))
    (mul (cs [100]) (pow A 2))) (mul (cs [8000]) (pow A 3)))
    (mul (cs [147]) (pow B 2))

/-- The cube of the weight-four Eisenstein series. -/
def eisensteinCubeExpr (a : List ℕ) : IntegerPolynomialExpression :=
  pow (add (cs [1]) (mul (cs [240]) (cs (a.map Int.ofNat)))) 3

private theorem getD_zipWith {l r : List ℕ} (f : ℕ → ℕ → ℤ) {i : ℕ}
    (hl : i < l.length) (hr : i < r.length) :
    (List.zipWith f l r).getD i 0 = f (l.getD i 0) (r.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hr, Option.getD_some]

private theorem sigmaPrefix_spec (N k : ℕ) (a : List ℕ) (h : N ≤ a.length)
    (ha : ∀ i < N, a.getD i 0 = ArithmeticFunction.sigma k i) :
    (cs (a.map Int.ofNat)).AgreesWith N (divisorPowerSeries k) := by
  apply coefficients_spec
  intro i
  have hi := i.isLt.trans_le h
  have he := ha i i.isLt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at he
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some, he, divisorPowerSeries, PowerSeries.coeff_mk,
    Int.ofNat_eq_natCast]

private theorem discriminantExpr_spec (N : ℕ) (a b : List ℕ)
    (ha : N ≤ a.length) (hb : N ≤ b.length)
    (hA : ∀ i < N, a.getD i 0 = ArithmeticFunction.sigma 3 i)
    (hB : ∀ i < N, b.getD i 0 = ArithmeticFunction.sigma 5 i) :
    (discriminantExpr a b).AgreesWith N Delta := by
  let σ := ArithmeticFunction.sigma
  let t (n : ℕ) := (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ)
  have hL : (cs (linearCoefficients a b)).AgreesWith N (PowerSeries.mk t) := by
    apply coefficients_spec
    intro i
    rw [linearCoefficients, getD_zipWith _ (i.isLt.trans_le ha) (i.isLt.trans_le hb),
      hA i i.isLt, hB i i.isLt, PowerSeries.coeff_mk]
  have hA' := sigmaPrefix_spec N 3 a ha hA
  have hB' := sigmaPrefix_spec N 5 b hb hB
  have h := sub_spec
    (add_spec (add_spec hL (mul_spec (constant_spec 100) (pow_spec hA' 2)))
      (mul_spec (constant_spec 8000) (pow_spec hA' 3)))
    (mul_spec (constant_spec 147) (pow_spec hB' 2))
  unfold discriminantExpr
  change IntegerPolynomialExpression.AgreesWith _ N
    (PowerSeries.mk t + 100 * divisorPowerSeries 3 ^ 2 +
      8000 * divisorPowerSeries 3 ^ 3 - 147 * divisorPowerSeries 5 ^ 2)
  simpa only [map_ofNat] using h

/-- The residue check for the shifted discriminant. -/
abbrev DiscriminantCheck (N : ℕ) (a b : List ℕ) (d : List ℤ) :=
  (sub (mul (cs [0,1]) (cs d)) (discriminantExpr a b)).checkZeroPrefixChunked (N+1)

/-- The residue check for the normalized invariant times the discriminant. -/
abbrev InvariantCheck (N : ℕ) (a : List ℕ) (d j : List ℤ) :=
  (sub (mul (cs d) (cs j)) (eisensteinCubeExpr a)).checkZeroPrefixChunked N

theorem discriminantPrefix_of_checked (N : ℕ) (a b : List ℕ) (d : List ℤ)
    (ha : N+1 ≤ a.length) (hb : N+1 ≤ b.length)
    (hA : ∀ i < N+1, a.getD i 0 = ArithmeticFunction.sigma 3 i)
    (hB : ∀ i < N+1, b.getD i 0 = ArithmeticFunction.sigma 5 i)
    (h : DiscriminantCheck N a b d) : SeriesPrefix N d D := by
  let A : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ d.getD n 0
  have hA' : SeriesPrefix (N+1) d A := by intro i; simp only [A, PowerSeries.coeff_mk]
  intro i
  let x : Fin (N+1) := ⟨(i:ℕ)+1, Nat.succ_lt_succ i.isLt⟩
  have hs := series_prefix_eq_of_check ((checkZeroPrefixChunked_iff _ _).mp h)
    (mul_spec X_spec (coefficients_spec hA')) (discriminantExpr_spec _ _ _ ha hb hA hB) x
  change (PowerSeries.X * A).coeff ((i:ℕ)+1) = PowerSeries.coeff ((i:ℕ)+1) Delta at hs
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk] at hs
  simpa only [integralNormalizedDiscriminantExpansion, PowerSeries.coeff_mk] using hs

private theorem eisensteinCubeExpr_spec (N : ℕ) (a : List ℕ) (ha : N ≤ a.length)
    (hA : ∀ i < N, a.getD i 0 = ArithmeticFunction.sigma 3 i) :
    (eisensteinCubeExpr a).AgreesWith N ((1 + 240 * divisorPowerSeries 3)^3) := by
  have h := pow_spec
    (add_spec (constant_spec 1) (mul_spec (constant_spec 240) (sigmaPrefix_spec N 3 a ha hA))) 3
  simpa only [eisensteinCubeExpr, map_one, map_ofNat] using h

/-- Two checked integer prefixes give the actual coefficients of normalized `j`. -/
theorem invariantPrefix_of_checked (N : ℕ) (a : List ℕ) (d j : List ℤ)
    (ha : N ≤ a.length) (hA : ∀ i < N, a.getD i 0 = ArithmeticFunction.sigma 3 i)
    (hD : SeriesPrefix N d D) (h : InvariantCheck N a d j) :
    SeriesPrefix N j J := by
  let A : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ j.getD n 0
  let E : ℤ⟦X⟧ := (1 + 240 * divisorPowerSeries 3)^3
  have hA' : SeriesPrefix N j A := by intro i; simp only [A, PowerSeries.coeff_mk]
  have hc : PowerSeries.X^N ∣ D * A - E := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro i hi
    rw [map_sub, sub_eq_zero]
    exact series_prefix_eq_of_check ((checkZeroPrefixChunked_iff _ _).mp h)
      (mul_spec (coefficients_spec hD) (coefficients_spec hA'))
      (eisensteinCubeExpr_spec N a ha hA) ⟨i, hi⟩
  let I := PowerSeries.invOfUnit D 1
  have hI : I * D = 1 :=
    PowerSeries.invOfUnit_mul D 1 constantCoeff_integralNormalizedDiscriminantExpansion
  have hId : I * (D * A - E) = A - J := by
    change I * (D * A - E) = A - E * I
    rw [mul_sub, ← mul_assoc, hI, one_mul, mul_comm I E]
  have hd : PowerSeries.X^N ∣ A - J := hId ▸ dvd_mul_of_dvd_right hc I
  intro i
  have hi := (PowerSeries.X_pow_dvd_iff.mp hd) i i.isLt
  rw [map_sub, sub_eq_zero] at hi
  exact (hA' i).trans hi

end ModularInvariantPrefixCertificate

end GRHArticle.SingularModuli

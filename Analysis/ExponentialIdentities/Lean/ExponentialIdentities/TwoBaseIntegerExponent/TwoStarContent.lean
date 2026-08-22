import ExponentialIdentities.TwoBaseIntegerExponent.FormalPrimeDeterminant
import ExponentialIdentities.TwoBaseIntegerExponent.OutputNormalization
import Mathlib.Data.ZMod.Basic

/-!
# Coefficient content of the primitive two-star determinant

This file attaches an integral coefficient content to the existing
`formalPrimeDeterminant`.  For the simultaneous primitive-output normalization

`A = 2 ^ a * w ^ d`, `B = 3 ^ b * v ^ e`,

the determinant has three disjoint coefficient blocks: the mixed base coefficient
`b - a`, the `d`-scaled prime valuations of `w`, and the `e`-scaled prime valuations of
`v`.  The main theorem identifies its coefficient content with
`simultaneousCoordinateGCD a b d e`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open MvPolynomial

noncomputable section

/-- The nonnegative gcd of all nonzero integral coefficients of a multivariate polynomial. -/
def integerCoefficientContent {σ : Type*} (P : MvPolynomial σ ℤ) : ℕ :=
  P.support.gcd fun m ↦ (P.coeff m).natAbs

/-- The coefficient content divides the absolute value of every coefficient, including the
coefficients outside the support. -/
theorem integerCoefficientContent_dvd_coeff_natAbs {σ : Type*}
    (P : MvPolynomial σ ℤ) (m : σ →₀ ℕ) :
    integerCoefficientContent P ∣ (P.coeff m).natAbs := by
  by_cases hm : m ∈ P.support
  · exact Finset.gcd_dvd hm
  · rw [MvPolynomial.notMem_support_iff.mp hm]
    simp

/-- A natural number dividing every coefficient divides the coefficient content. -/
theorem dvd_integerCoefficientContent {σ : Type*} (P : MvPolynomial σ ℤ) (k : ℕ)
    (hk : ∀ m : σ →₀ ℕ, k ∣ (P.coeff m).natAbs) :
    k ∣ integerCoefficientContent P := by
  apply Finset.dvd_gcd
  intro m hm
  exact hk m

/-- The coefficient content divides every integral specialization of the polynomial. -/
theorem integerCoefficientContent_dvd_eval {σ : Type*}
    (P : MvPolynomial σ ℤ) (x : σ → ℤ) :
    (integerCoefficientContent P : ℤ) ∣ eval x P := by
  rw [MvPolynomial.eval_eq]
  apply Finset.dvd_sum
  intro m hm
  apply dvd_mul_of_dvd_left
  exact Int.natCast_dvd.mpr (integerCoefficientContent_dvd_coeff_natAbs P m)

/-- If a polynomial is an integral scalar multiple, that scalar divides its coefficient
content. -/
theorem dvd_integerCoefficientContent_of_eq_C_mul {σ : Type*}
    {P R : MvPolynomial σ ℤ} {k : ℕ} (hP : P = C (k : ℤ) * R) :
    k ∣ integerCoefficientContent P := by
  apply dvd_integerCoefficientContent
  intro m
  rw [hP, coeff_C_mul, Int.natAbs_mul, Int.natAbs_natCast]
  exact dvd_mul_right k _

/-- Formal prime-factor logarithms turn products of nonzero naturals into sums. -/
theorem primeFactorLinearForm_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    primeFactorLinearForm (m * n) =
      primeFactorLinearForm m + primeFactorLinearForm n := by
  classical
  simp only [primeFactorLinearForm, Nat.factorization_mul hm hn]
  rw [Finsupp.sum_add_index' (fun _ ↦ by simp)
    (fun _ x y ↦ by push_cast; simp [mul_add, mul_comm])]

/-- Formal prime-factor logarithms turn a positive power into scalar multiplication. -/
theorem primeFactorLinearForm_pow (m d : ℕ) :
    primeFactorLinearForm (m ^ d) = C (d : ℤ) * primeFactorLinearForm m := by
  classical
  simp only [primeFactorLinearForm, Nat.factorization_pow]
  rw [Finsupp.sum_smul_index']
  · simp [Finsupp.sum, Finset.mul_sum, mul_assoc]
  · intro p
    simp

/-- The formal prime-factor logarithm of a prime is its corresponding variable. -/
theorem primeFactorLinearForm_prime {p : ℕ} (hp : p.Prime) :
    primeFactorLinearForm p = X p := by
  classical
  rw [primeFactorLinearForm, hp.factorization]
  simp

/-- Expansion of a prime-power times a nonzero powered core. -/
theorem primeFactorLinearForm_primePow_mul_pow {p a w d : ℕ}
    (hp : p.Prime) (hw0 : w ≠ 0) :
    primeFactorLinearForm (p ^ a * w ^ d) =
      C (a : ℤ) * X p + C (d : ℤ) * primeFactorLinearForm w := by
  rw [primeFactorLinearForm_mul (pow_ne_zero _ hp.ne_zero)
      (pow_ne_zero _ hw0),
    primeFactorLinearForm_pow, primeFactorLinearForm_pow,
    primeFactorLinearForm_prime hp]

/-- The existing formal determinant expanded into its three normalized coefficient blocks. -/
theorem formalPrimeDeterminant_normalized {a b w v d e : ℕ}
    (hw0 : w ≠ 0) (hv0 : v ≠ 0) :
    formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e) =
      C ((b : ℤ) - (a : ℤ)) * X 2 * X 3 +
        C (e : ℤ) * X 2 * primeFactorLinearForm v -
          C (d : ℤ) * X 3 * primeFactorLinearForm w := by
  rw [formalPrimeDeterminant,
    primeFactorLinearForm_primePow_mul_pow (by norm_num : Nat.Prime 3) hv0,
    primeFactorLinearForm_primePow_mul_pow (by norm_num : Nat.Prime 2) hw0]
  rw [map_sub]
  ring

/-- Integral Kronecker assignment at one prime-coordinate. -/
def twoStarPrimeProbe (q p : ℕ) : ℤ :=
  if p = q then 1 else 0

private theorem factorization_sum_twoStarPrimeProbe (n q : ℕ) :
    n.factorization.sum (fun p e ↦ (e : ℤ) * twoStarPrimeProbe q p) =
      (n.factorization q : ℤ) := by
  classical
  by_cases hq : q ∈ n.factorization.support
  · rw [Finsupp.sum, Finset.sum_eq_single q]
    · simp [twoStarPrimeProbe]
    · intro p hp hpq
      simp [twoStarPrimeProbe, hpq]
    · exact fun h ↦ (h hq).elim
  · have hz : n.factorization q = 0 := Finsupp.notMem_support_iff.mp hq
    rw [hz, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro p hp
    have hpq : p ≠ q := fun hpq ↦ hq (hpq ▸ hp)
    simp [twoStarPrimeProbe, hpq]

/-- A prime-factor linear form evaluated at a coordinate probe returns that valuation. -/
theorem primeFactorLinearForm_eval_twoStarPrimeProbe (n q : ℕ) :
    eval (twoStarPrimeProbe q) (primeFactorLinearForm n) =
      (n.factorization q : ℤ) := by
  change eval₂ (RingHom.id ℤ) (twoStarPrimeProbe q) (primeFactorLinearForm n) = _
  rw [primeFactorLinearForm_eval₂]
  exact factorization_sum_twoStarPrimeProbe n q

/-- A prime-factor linear form evaluated at two added probes returns the sum of the two
valuations. -/
theorem primeFactorLinearForm_eval_add_twoStarPrimeProbe (n q r : ℕ) :
    eval (twoStarPrimeProbe q + twoStarPrimeProbe r) (primeFactorLinearForm n) =
      (n.factorization q : ℤ) + (n.factorization r : ℤ) := by
  change eval₂ (RingHom.id ℤ) (twoStarPrimeProbe q + twoStarPrimeProbe r)
    (primeFactorLinearForm n) = _
  rw [primeFactorLinearForm_eval₂]
  calc
    n.factorization.sum
          (fun p e ↦ (e : ℤ) * (twoStarPrimeProbe q + twoStarPrimeProbe r) p) =
        n.factorization.sum (fun p e ↦ (e : ℤ) * twoStarPrimeProbe q p) +
          n.factorization.sum (fun p e ↦ (e : ℤ) * twoStarPrimeProbe r p) := by
            simp [Finsupp.sum, mul_add, Finset.sum_add_distrib]
    _ = (n.factorization q : ℤ) + (n.factorization r : ℤ) := by
      rw [factorization_sum_twoStarPrimeProbe, factorization_sum_twoStarPrimeProbe]

/-- Any common divisor of the three normalized coefficient scales divides the actual
polynomial coefficient content. -/
theorem normalizedScales_dvd_formalPrimeDeterminant_content
    {a b w v d e k : ℕ} (hw0 : w ≠ 0) (hv0 : v ≠ 0)
    (hkdiff : k ∣ ((b : ℤ) - (a : ℤ)).natAbs)
    (hkd : k ∣ d) (hke : k ∣ e) :
    k ∣ integerCoefficientContent
      (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) := by
  obtain ⟨d₀, rfl⟩ := hkd
  obtain ⟨e₀, rfl⟩ := hke
  have hkdiffInt : (k : ℤ) ∣ (b : ℤ) - (a : ℤ) :=
    Int.natCast_dvd.mpr hkdiff
  obtain ⟨z, hz⟩ := hkdiffInt
  apply dvd_integerCoefficientContent_of_eq_C_mul
    (R := C z * X 2 * X 3 + C (e₀ : ℤ) * X 2 * primeFactorLinearForm v -
      C (d₀ : ℤ) * X 3 * primeFactorLinearForm w)
  rw [formalPrimeDeterminant_normalized hw0 hv0, hz]
  push_cast
  simp only [map_mul]
  ring

/-- The simultaneous coordinate gcd always divides the normalized determinant content. -/
theorem simultaneousCoordinateGCD_dvd_formalPrimeDeterminant_content
    {a b w v d e : ℕ} (hw0 : w ≠ 0) (hv0 : v ≠ 0) :
    simultaneousCoordinateGCD a b d e ∣
      integerCoefficientContent
        (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) := by
  apply normalizedScales_dvd_formalPrimeDeterminant_content hw0 hv0
  · exact Nat.gcd_dvd_right _ _
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)

/-- The coordinate-two probe extracts the `v`-block square coefficient. -/
theorem formalPrimeDeterminant_eval_probe_two {a b w v d e : ℕ}
    (hw0 : w ≠ 0) (hv0 : v ≠ 0) :
    eval (twoStarPrimeProbe 2)
        (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) =
      (e * v.factorization 2 : ℕ) := by
  rw [formalPrimeDeterminant_normalized hw0 hv0]
  simp [primeFactorLinearForm_eval_twoStarPrimeProbe, twoStarPrimeProbe]

/-- The coordinate-three probe extracts the negative `w`-block square coefficient. -/
theorem formalPrimeDeterminant_eval_probe_three {a b w v d e : ℕ}
    (hw0 : w ≠ 0) (hv0 : v ≠ 0) :
    eval (twoStarPrimeProbe 3)
        (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) =
      -((d * w.factorization 3 : ℕ) : ℤ) := by
  rw [formalPrimeDeterminant_normalized hw0 hv0]
  simp [primeFactorLinearForm_eval_twoStarPrimeProbe, twoStarPrimeProbe]

/-- Away from the two base coordinates, polarization with coordinate three extracts a
`w`-block coefficient. -/
theorem formalPrimeDeterminant_eval_three_add_probe_sub
    {a b w v d e p : ℕ} (hw0 : w ≠ 0) (hv0 : v ≠ 0)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    eval (twoStarPrimeProbe 3 + twoStarPrimeProbe p)
          (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) -
        eval (twoStarPrimeProbe 3)
          (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) =
      -((d * w.factorization p : ℕ) : ℤ) := by
  rw [formalPrimeDeterminant_normalized hw0 hv0]
  simp [primeFactorLinearForm_eval_twoStarPrimeProbe,
    primeFactorLinearForm_eval_add_twoStarPrimeProbe,
    twoStarPrimeProbe, Ne.symm hp2, Ne.symm hp3]
  ring

/-- Away from the two base coordinates, polarization with coordinate two extracts a
`v`-block coefficient. -/
theorem formalPrimeDeterminant_eval_two_add_probe_sub
    {a b w v d e p : ℕ} (hw0 : w ≠ 0) (hv0 : v ≠ 0)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    eval (twoStarPrimeProbe 2 + twoStarPrimeProbe p)
          (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) -
        eval (twoStarPrimeProbe 2)
          (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) =
      (e * v.factorization p : ℕ) := by
  rw [formalPrimeDeterminant_normalized hw0 hv0]
  simp [primeFactorLinearForm_eval_twoStarPrimeProbe,
    primeFactorLinearForm_eval_add_twoStarPrimeProbe,
    twoStarPrimeProbe, Ne.symm hp2, Ne.symm hp3]
  ring

/-- Polarization at the two base coordinates extracts the mixed coefficient `b - a`. -/
theorem formalPrimeDeterminant_eval_base_polarization
    {a b w v d e : ℕ} (hwodd : Odd w) (hvthree : ¬ 3 ∣ v)
    (hw0 : w ≠ 0) (hv0 : v ≠ 0) :
    eval (twoStarPrimeProbe 2 + twoStarPrimeProbe 3)
          (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) -
        eval (twoStarPrimeProbe 2)
          (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) -
        eval (twoStarPrimeProbe 3)
          (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) =
      (b : ℤ) - (a : ℤ) := by
  have hw2 : w.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hwodd.not_two_dvd_nat
  have hv3 : v.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hvthree
  rw [formalPrimeDeterminant_normalized hw0 hv0]
  simp [primeFactorLinearForm_eval_twoStarPrimeProbe,
    primeFactorLinearForm_eval_add_twoStarPrimeProbe,
    twoStarPrimeProbe, hw2, hv3]
  ring

/-- For primitive base-free cores, the determinant content divides the simultaneous
coordinate gcd. -/
theorem formalPrimeDeterminant_content_dvd_simultaneousCoordinateGCD
    {a b w v d e : ℕ}
    (hwodd : Odd w) (hw1 : 1 < w) (hwprimitive : NatPowerPrimitive w)
    (hvthree : ¬ 3 ∣ v) (hv1 : 1 < v) (hvprimitive : NatPowerPrimitive v) :
    integerCoefficientContent
        (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) ∣
      simultaneousCoordinateGCD a b d e := by
  let P := formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)
  let c := integerCoefficientContent P
  change c ∣ simultaneousCoordinateGCD a b d e
  have hw0 : w ≠ 0 := by omega
  have hv0 : v ≠ 0 := by omega
  have hceval (x : ℕ → ℤ) : (c : ℤ) ∣ eval x P :=
    integerCoefficientContent_dvd_eval P x

  have hpolar :
      eval (twoStarPrimeProbe 2 + twoStarPrimeProbe 3) P -
          eval (twoStarPrimeProbe 2) P - eval (twoStarPrimeProbe 3) P =
        (b : ℤ) - (a : ℤ) := by
    simpa [P] using
      (formalPrimeDeterminant_eval_base_polarization
        (a := a) (b := b) (d := d) (e := e) hwodd hvthree hw0 hv0)
  have hcdiffInt : (c : ℤ) ∣ (b : ℤ) - (a : ℤ) := by
    have h := ((hceval (twoStarPrimeProbe 2 + twoStarPrimeProbe 3)).sub
      (hceval (twoStarPrimeProbe 2))).sub (hceval (twoStarPrimeProbe 3))
    rwa [hpolar] at h
  have hcdiff : c ∣ ((b : ℤ) - (a : ℤ)).natAbs :=
    Int.natCast_dvd.mp hcdiffInt

  have hcwcoeff : ∀ p ∈ w.primeFactors, c ∣ d * w.factorization p := by
    intro p hp
    have hp2 : p ≠ 2 := by
      intro hp2
      subst p
      exact hwodd.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    by_cases hp3 : p = 3
    · subst p
      have h := hceval (twoStarPrimeProbe 3)
      have heval : eval (twoStarPrimeProbe 3) P =
          -(((d * w.factorization 3 : ℕ) : ℤ)) := by
        simpa [P] using
          (formalPrimeDeterminant_eval_probe_three
            (a := a) (b := b) (v := v) (e := e) hw0 hv0)
      rw [heval] at h
      simpa [Int.natAbs_mul] using (Int.natCast_dvd.mp h)
    · have h := (hceval (twoStarPrimeProbe 3 + twoStarPrimeProbe p)).sub
          (hceval (twoStarPrimeProbe 3))
      have heval :
          eval (twoStarPrimeProbe 3 + twoStarPrimeProbe p) P -
              eval (twoStarPrimeProbe 3) P =
            -(((d * w.factorization p : ℕ) : ℤ)) := by
        simpa [P] using
          (formalPrimeDeterminant_eval_three_add_probe_sub
            (a := a) (b := b) (v := v) (e := e) hw0 hv0 hp2 hp3)
      rw [heval] at h
      simpa [Int.natAbs_mul] using (Int.natCast_dvd.mp h)

  have hcvcoeff : ∀ p ∈ v.primeFactors, c ∣ e * v.factorization p := by
    intro p hp
    have hp3 : p ≠ 3 := by
      intro hp3
      subst p
      exact hvthree (Nat.dvd_of_mem_primeFactors hp)
    by_cases hp2 : p = 2
    · subst p
      have h := hceval (twoStarPrimeProbe 2)
      have heval : eval (twoStarPrimeProbe 2) P =
          ((e * v.factorization 2 : ℕ) : ℤ) := by
        simpa [P] using
          (formalPrimeDeterminant_eval_probe_two
            (a := a) (b := b) (w := w) (d := d) hw0 hv0)
      rw [heval] at h
      exact Int.natCast_dvd.mp h
    · have h := (hceval (twoStarPrimeProbe 2 + twoStarPrimeProbe p)).sub
          (hceval (twoStarPrimeProbe 2))
      have heval :
          eval (twoStarPrimeProbe 2 + twoStarPrimeProbe p) P -
              eval (twoStarPrimeProbe 2) P =
            ((e * v.factorization p : ℕ) : ℤ) := by
        simpa [P] using
          (formalPrimeDeterminant_eval_two_add_probe_sub
            (a := a) (b := b) (w := w) (d := d) hw0 hv0 hp2 hp3)
      rw [heval] at h
      exact Int.natCast_dvd.mp h

  have hcwGCD : c ∣ w.primeFactors.gcd (fun p ↦ d * w.factorization p) := by
    exact Finset.dvd_gcd hcwcoeff
  have hwvaluationGCD : oddPrimeValuationGCD w = 1 :=
    oddPrimeValuationGCD_eq_one_of_natPowerPrimitive hw1 hwprimitive
  have hwscaledGCD : w.primeFactors.gcd (fun p ↦ d * w.factorization p) = d := by
    calc
      w.primeFactors.gcd (fun p ↦ d * w.factorization p) =
          d * oddPrimeValuationGCD w := by
            simpa only [oddPrimeValuationGCD, normalize_eq] using
              (Finset.gcd_mul_left (β := ℕ) (α := ℕ)
                (s := w.primeFactors) (f := w.factorization) (a := d))
      _ = d := by simp [hwvaluationGCD]
  have hcd : c ∣ d := by simpa [hwscaledGCD] using hcwGCD

  have hcvGCD : c ∣ v.primeFactors.gcd (fun p ↦ e * v.factorization p) := by
    exact Finset.dvd_gcd hcvcoeff
  have hvvaluationGCD : oddPrimeValuationGCD v = 1 :=
    oddPrimeValuationGCD_eq_one_of_natPowerPrimitive hv1 hvprimitive
  have hvscaledGCD : v.primeFactors.gcd (fun p ↦ e * v.factorization p) = e := by
    calc
      v.primeFactors.gcd (fun p ↦ e * v.factorization p) =
          e * oddPrimeValuationGCD v := by
            simpa only [oddPrimeValuationGCD, normalize_eq] using
              (Finset.gcd_mul_left (β := ℕ) (α := ℕ)
                (s := v.primeFactors) (f := v.factorization) (a := e))
      _ = e := by simp [hvvaluationGCD]
  have hce : c ∣ e := by simpa [hvscaledGCD] using hcvGCD

  simpa only [simultaneousCoordinateGCD] using
    Nat.dvd_gcd (Nat.dvd_gcd hcd hce) hcdiff

/-- **Exact two-star content formula.**  For primitive complementary cores, the coefficient
content of the existing formal prime determinant is exactly the gcd of the two outer power
degrees and the base-depth difference. -/
theorem formalPrimeDeterminant_content_eq_simultaneousCoordinateGCD
    {a b w v d e : ℕ}
    (hwodd : Odd w) (hw1 : 1 < w) (hwprimitive : NatPowerPrimitive w)
    (hvthree : ¬ 3 ∣ v) (hv1 : 1 < v) (hvprimitive : NatPowerPrimitive v) :
    integerCoefficientContent
        (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) =
      simultaneousCoordinateGCD a b d e := by
  apply Nat.dvd_antisymm
  · exact formalPrimeDeterminant_content_dvd_simultaneousCoordinateGCD
      hwodd hw1 hwprimitive hvthree hv1 hvprimitive
  · exact simultaneousCoordinateGCD_dvd_formalPrimeDeterminant_content
      (by omega) (by omega)

/-- The least-output affine-primitivity theorem turns the exact content formula into
coefficient content one. -/
theorem IsLeastTwoBaseNonintegerSolution.formalPrimeDeterminant_content_eq_one
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β)
    {a b w v d e : ℕ}
    (hwodd : Odd w) (hw1 : 1 < w) (hwprimitive : NatPowerPrimitive w)
    (hvthree : ¬ 3 ∣ v) (hv1 : 1 < v) (hvprimitive : NatPowerPrimitive v)
    (hd : 0 < d)
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β)
    (hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β) :
    integerCoefficientContent
        (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) = 1 := by
  rw [formalPrimeDeterminant_content_eq_simultaneousCoordinateGCD
    hwodd hw1 hwprimitive hvthree hv1 hvprimitive]
  exact hβ.simultaneousCoordinateGCD_eq_one hd hM hB

/-- Content one prevents annihilation of the polynomial modulo every nontrivial modulus. -/
theorem map_ne_zero_of_integerCoefficientContent_eq_one {σ : Type*}
    (P : MvPolynomial σ ℤ) {q : ℕ} (hq : 1 < q)
    (hcontent : integerCoefficientContent P = 1) :
    MvPolynomial.map (Int.castRingHom (ZMod q)) P ≠ 0 := by
  intro hzero
  have hqcoeff : ∀ m : σ →₀ ℕ, q ∣ (P.coeff m).natAbs := by
    intro m
    have hcoeff := congrArg (fun Q : MvPolynomial σ (ZMod q) ↦ Q.coeff m) hzero
    have hcast : ((P.coeff m : ℤ) : ZMod q) = 0 := by
      simpa [MvPolynomial.coeff_map] using hcoeff
    exact Int.natCast_dvd.mp
      ((ZMod.intCast_zmod_eq_zero_iff_dvd (P.coeff m) q).mp hcast)
  have hqcontent : q ∣ integerCoefficientContent P :=
    dvd_integerCoefficientContent P q hqcoeff
  rw [hcontent] at hqcontent
  have hqle : q ≤ 1 := Nat.le_of_dvd (by norm_num) hqcontent
  omega

/-- A least primitive output determinant remains nonzero after reduction modulo every
nontrivial modulus (hence, in particular, modulo every prime). -/
theorem IsLeastTwoBaseNonintegerSolution.formalPrimeDeterminant_map_ne_zero
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β)
    {a b w v d e q : ℕ}
    (hwodd : Odd w) (hw1 : 1 < w) (hwprimitive : NatPowerPrimitive w)
    (hvthree : ¬ 3 ∣ v) (hv1 : 1 < v) (hvprimitive : NatPowerPrimitive v)
    (hd : 0 < d)
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β)
    (hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β)
    (hq : 1 < q) :
    MvPolynomial.map (Int.castRingHom (ZMod q))
        (formalPrimeDeterminant (2 ^ a * w ^ d) (3 ^ b * v ^ e)) ≠ 0 := by
  apply map_ne_zero_of_integerCoefficientContent_eq_one _ hq
  exact hβ.formalPrimeDeterminant_content_eq_one
    hwodd hw1 hwprimitive hvthree hv1 hvprimitive hd hM hB

end

end LeanProofs.TwoBaseIntegerExponent

import Surreal.Algebra.PolynomialCRT
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Explicit inverse jets and polynomial CRT representatives

This file constructs the local inverse used in `polynomial:eq:inversejet`
and proves that the products `Pᵢ Cᵢ` represent the idempotents in
`polynomial:thm:crt` of `docs/surcomplex/polynomial-algebra/article.tex`.

The inverse jet is defined explicitly by truncating the inverse of the
formal Taylor series at the node and translating back. The resulting finite
coefficient formula, degree bound, inverse congruence, and identification of
the CRT classes hold over every field, including positive characteristic.

The identification of these formal inverse coefficients with the ordinary
iterated derivatives of the rational function `1 / Pᵢ`, divided by
factorials, is a separate assertion and is not proved in this file.
-/

namespace Surreal.FinitePolynomial

noncomputable section

open Polynomial

variable {K ι : Type*} [Field K]

/-- The explicit truncated inverse of the formal Taylor series of `q` at
`a`, translated back to the original polynomial variable. -/
def inverseJet (q : K[X]) (a : K) (m : ℕ) : K[X] :=
  taylor (-a) (PowerSeries.trunc m ((taylor a q : PowerSeries K)⁻¹))

/-- The finite coefficient formula for the algebraic inverse jet. The
coefficients are those of the reciprocal formal Taylor series. -/
theorem inverseJet_eq_sum (q : K[X]) (a : K) (m : ℕ) :
    inverseJet q a m = ∑ j ∈ Finset.range m,
      C (PowerSeries.coeff j ((taylor a q : PowerSeries K)⁻¹)) * (X - C a) ^ j := by
  simp only [inverseJet, PowerSeries.trunc_apply, Nat.Ico_zero_eq_range,
    map_sum, taylor_monomial, C_neg, sub_eq_add_neg]

/-- The inverse jet has degree strictly below the local multiplicity,
including the zero jet at multiplicity zero. -/
theorem inverseJet_degree_lt (q : K[X]) (a : K) (m : ℕ) :
    (inverseJet q a m).degree < m := by
  rw [inverseJet, degree_taylor]
  exact PowerSeries.degree_trunc_lt _ _

/-- Translation to the node recovers the truncated formal inverse. -/
theorem taylor_inverseJet (q : K[X]) (a : K) (m : ℕ) :
    taylor a (inverseJet q a m) =
      PowerSeries.trunc m ((taylor a q : PowerSeries K)⁻¹) := by
  simp [inverseJet, taylor_taylor]

/-- A truncated formal inverse is an inverse modulo the corresponding
power of the variable. The nonzero constant coefficient is essential. -/
theorem X_pow_dvd_mul_trunc_inverse_sub_one (q : K[X]) (hq : q.coeff 0 ≠ 0) (m : ℕ) :
    X ^ m ∣ q * PowerSeries.trunc m ((q : PowerSeries K)⁻¹) - 1 := by
  have htr : PowerSeries.trunc m
      ((q : PowerSeries K) * (PowerSeries.trunc m ((q : PowerSeries K)⁻¹) : PowerSeries K)) =
      PowerSeries.trunc m (1 : PowerSeries K) := by
    rw [PowerSeries.trunc_mul_trunc, PowerSeries.mul_inv_cancel _ (by
      simpa only [Polynomial.constantCoeff_coe] using hq)]
  apply Polynomial.X_pow_dvd_iff.mpr
  intro j hj
  have hc := congrArg (fun p : K[X] => p.coeff j) htr
  simp only [PowerSeries.coeff_trunc, if_pos hj, ← Polynomial.coe_mul,
    Polynomial.coeff_coe, PowerSeries.coeff_one] at hc
  simp only [Polynomial.coeff_sub, Polynomial.coeff_one, hc, sub_self]

/-- The local inverse congruence from `polynomial:eq:inversejet`, obtained
from the actual reciprocal formal Taylor series. -/
theorem node_pow_dvd_mul_inverseJet_sub_one (q : K[X]) (a : K)
    (hq : q.eval a ≠ 0) (m : ℕ) : (X - C a) ^ m ∣ q * inverseJet q a m - 1 := by
  rw [← map_dvd_iff (taylorEquiv a)]
  change taylor a ((X - C a) ^ m) ∣ taylor a (q * inverseJet q a m - 1)
  have hlin : taylor a (X - C a : K[X]) = X := by simp [taylor_apply]
  rw [taylor_pow, hlin, map_sub, taylor_mul, taylor_inverseJet, taylor_one, C_1]
  exact X_pow_dvd_mul_trunc_inverse_sub_one (taylor a q) (by
    simpa only [taylor_coeff_zero] using hq) m

/-- The inverse-jet polynomial is an actual multiplicative inverse in the
local quotient. -/
theorem mk_mul_inverseJet_eq_one (q : K[X]) (a : K) (hq : q.eval a ≠ 0) (m : ℕ) :
    Ideal.Quotient.mk (nodeIdeal a m) q *
      Ideal.Quotient.mk (nodeIdeal a m) (inverseJet q a m) = 1 := by
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (nodeIdeal a m))]
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
    (node_pow_dvd_mul_inverseJet_sub_one q a hq m))

/-- The local class of a polynomial nonzero at the node is a unit. -/
theorem isUnit_mk_of_eval_ne_zero (q : K[X]) (a : K) (hq : q.eval a ≠ 0) (m : ℕ) :
    IsUnit (Ideal.Quotient.mk (nodeIdeal a m) q) :=
  isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk (nodeIdeal a m) (inverseJet q a m),
    mk_mul_inverseJet_eq_one q a hq m⟩

/-- The inverse jet is the unique polynomial below the local multiplicity
that inverts `q` modulo the corresponding linear-factor power. -/
theorem inverseJet_unique (q : K[X]) (a : K) (hq : q.eval a ≠ 0) (m : ℕ)
    (r : K[X]) (hr : r.degree < m) (hinv : (X - C a) ^ m ∣ q * r - 1) :
    r = inverseJet q a m := by
  have hclass : Ideal.Quotient.mk (nodeIdeal a m) r =
      Ideal.Quotient.mk (nodeIdeal a m) (inverseJet q a m) := by
    apply (isUnit_mk_of_eval_ne_zero q a hq m).mul_left_cancel
    rw [mk_mul_inverseJet_eq_one q a hq m, ← map_mul,
      ← map_one (Ideal.Quotient.mk (nodeIdeal a m))]
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr hinv)
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_dvd_of_degree_lt
  · exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hclass)
  · simpa only [degree_pow, degree_X_sub_C, nsmul_one] using
      (Polynomial.degree_sub_le r (inverseJet q a m)).trans_lt
        (max_lt hr (inverseJet_degree_lt q a m))

variable [Fintype ι]

local instance inverseJetIndexDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The product of all local factors except the selected one, the
polynomial `Pᵢ` preceding `polynomial:eq:inversejet`. -/
def interpolationCofactor (a : ι → K) (m : ι → ℕ) (i : ι) : K[X] :=
  ∏ j ∈ Finset.univ.erase i, (X - C (a j)) ^ m j

/-- Cofactors are monic, including an empty product. -/
theorem interpolationCofactor_monic (a : ι → K) (m : ι → ℕ) (i : ι) :
    (interpolationCofactor a m i).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun j _ => (monic_X_sub_C (a j)).pow (m j)

/-- The modulus factors as the selected local factor times its cofactor. -/
theorem interpolationModulus_eq_node_mul_cofactor (a : ι → K) (m : ι → ℕ) (i : ι) :
    interpolationModulus a m = (X - C (a i)) ^ m i * interpolationCofactor a m i :=
  (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm

/-- The product definition of the cofactor agrees with the quotient
`Pᵢ = P / Aᵢ` used in the manuscript. -/
theorem interpolationCofactor_eq_div (a : ι → K) (m : ι → ℕ) (i : ι) :
    interpolationCofactor a m i = interpolationModulus a m / (X - C (a i)) ^ m i := by
  rw [interpolationModulus_eq_node_mul_cofactor]
  exact (mul_div_cancel_left₀ _ ((monic_X_sub_C (a i)).pow (m i)).ne_zero).symm

/-- Distinct nodes guarantee that the cofactor is nonzero at its own node;
no Archimedean lower bound on separations is required. -/
theorem interpolationCofactor_eval_ne_zero (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (i : ι) : (interpolationCofactor a m i).eval (a i) ≠ 0 := by
  classical
  rw [interpolationCofactor, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [eval_pow, eval_sub, eval_X, eval_C]
  exact pow_ne_zero _ (sub_ne_zero.mpr (ha.ne (Finset.ne_of_mem_erase hj).symm))

/-- Every other node's local factor divides the cofactor. -/
theorem node_pow_dvd_interpolationCofactor (a : ι → K) (m : ι → ℕ)
    {i j : ι} (hji : j ≠ i) : (X - C (a j)) ^ m j ∣ interpolationCofactor a m i := by
  apply Finset.dvd_prod_of_mem
  exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩

/-- The concrete polynomial representative `Pᵢ Cᵢ` in `polynomial:thm:crt`. -/
def inverseJetIdempotentPolynomial (a : ι → K) (m : ι → ℕ) (i : ι) : K[X] :=
  interpolationCofactor a m i * inverseJet (interpolationCofactor a m i) (a i) (m i)

/-- The explicit `Pᵢ Cᵢ` representative already has degree below `deg P`;
no additional remainder operation is needed. This includes `m i = 0`,
when the inverse jet and representative are zero. -/
theorem inverseJetIdempotentPolynomial_degree_lt (a : ι → K) (m : ι → ℕ) (i : ι) :
    (inverseJetIdempotentPolynomial a m i).degree < (∑ j, m j : ℕ) := by
  rw [inverseJetIdempotentPolynomial, degree_mul]
  calc
    (interpolationCofactor a m i).degree +
        (inverseJet (interpolationCofactor a m i) (a i) (m i)).degree <
        (interpolationCofactor a m i).degree + (m i : WithBot ℕ) :=
      WithBot.add_lt_add_left (degree_ne_bot.mpr (interpolationCofactor_monic a m i).ne_zero)
        (inverseJet_degree_lt _ _ _)
    _ = (interpolationModulus a m).degree := by
      rw [interpolationModulus_eq_node_mul_cofactor a m i, degree_mul]
      simp [degree_pow, degree_X_sub_C, add_comm]
    _ = (∑ j, m j : ℕ) := interpolationModulus_degree a m

/-- The explicit representative is one at the selected local quotient and
zero at every other quotient, including zero multiplicities. -/
theorem inverseJetIdempotentPolynomial_local_congruences (a : ι → K)
    (ha : Function.Injective a) (m : ι → ℕ) (i j : ι) :
    (X - C (a j)) ^ m j ∣ inverseJetIdempotentPolynomial a m i -
      if j = i then 1 else 0 := by
  by_cases hji : j = i
  · subst j
    simpa only [if_true, inverseJetIdempotentPolynomial] using
      node_pow_dvd_mul_inverseJet_sub_one (interpolationCofactor a m i) (a i)
        (interpolationCofactor_eval_ne_zero a ha m i) (m i)
  · rw [if_neg hji, sub_zero]
    exact dvd_mul_of_dvd_left (node_pow_dvd_interpolationCofactor a m hji) _

/-- The concrete inverse-jet construction has exactly the coordinate
idempotent class from `polynomial:thm:crt`. Thus its idempotence,
orthogonality, and sum-to-one identities follow from the existing CRT API. -/
theorem mk_inverseJetIdempotentPolynomial (a : ι → K) (ha : Function.Injective a)
    (m : ι → ℕ) (i : ι) :
    Ideal.Quotient.mk (interpolationIdeal a m) (inverseJetIdempotentPolynomial a m i) =
      crtIdempotent a ha m i :=
  mk_eq_crtIdempotent_of_local_congruences a ha m i _
    (inverseJetIdempotentPolynomial_local_congruences a ha m i)

end

end Surreal.FinitePolynomial

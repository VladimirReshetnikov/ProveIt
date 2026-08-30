import FabiusFunction.SymmetricFunctionOrthogonality
import FabiusFunction.GeometricCompleteHomogeneous
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Generating series for finite symmetric-function alphabets

This module packages the elementary and complete homogeneous evaluations as
formal power series.  For a finite alphabet `a`, their two classical product
identities are proved over the weakest natural coefficient rings:

* over a commutative semiring,
  `E_a(X) = product_i (1 + a_i X)`;
* over a commutative ring, `E_{-a}(X) H_a(X) = 1`, and hence `H_a` is the
  canonical formal inverse of `E_{-a}`.

Specializing the alphabet to `1, q, ..., q^n` gives a denominator-free formal
reciprocal form of the finite q-binomial theorem.  All statements are total,
including the empty alphabet and `n = 0`, and require no regularity or
nonvanishing hypothesis on the alphabet or on `q`.

## Main results

* `elementarySymmetricGeneratingSeries_eq_prod` is the finite elementary
  product.
* `elementarySymmetricGeneratingSeries_neg_mul_completeHomogeneousGeneratingSeries`
  is elementary--complete reciprocity.
* `completeHomogeneousGeneratingSeries_eq_invOfUnit_elementarySymmetricGeneratingSeries_neg`
  identifies the complete homogeneous series with Mathlib's canonical formal
  inverse.
* `prod_one_sub_qPow_X_mul_gaussianBinomialGeneratingSeries` is the direct
  finite q-binomial reciprocal identity.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

noncomputable section

/-- The ordinary generating series of elementary symmetric evaluations on a
finite alphabet `a`. -/
def elementarySymmetricGeneratingSeries
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) : PowerSeries R :=
  PowerSeries.mk (elementarySymmetricEval a)

/-- The ordinary generating series of complete homogeneous evaluations on a
finite alphabet `a`. -/
def completeHomogeneousGeneratingSeries
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) : PowerSeries R :=
  PowerSeries.mk (completeHomogeneousEval a)

/-- The coefficient of the elementary generating series is the corresponding
elementary symmetric evaluation. -/
@[simp]
theorem coeff_elementarySymmetricGeneratingSeries
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) (n : ℕ) :
    PowerSeries.coeff n (elementarySymmetricGeneratingSeries a) =
      elementarySymmetricEval a n := by
  rw [elementarySymmetricGeneratingSeries, PowerSeries.coeff_mk]

/-- The coefficient of the complete homogeneous generating series is the
corresponding complete homogeneous evaluation. -/
@[simp]
theorem coeff_completeHomogeneousGeneratingSeries
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) (n : ℕ) :
    PowerSeries.coeff n (completeHomogeneousGeneratingSeries a) =
      completeHomogeneousEval a n := by
  rw [completeHomogeneousGeneratingSeries, PowerSeries.coeff_mk]

private theorem esymm_cons_succ
    {R : Type*} [CommSemiring R] (x : R) (s : Multiset R) (n : ℕ) :
    (x ::ₘ s).esymm (n + 1) =
      x * s.esymm n + s.esymm (n + 1) := by
  simp [Multiset.esymm, Multiset.powersetCard_cons,
    Multiset.sum_map_mul_left, add_comm]

private theorem mk_esymm_eq_multiset_prod
    {R : Type*} [CommSemiring R] (s : Multiset R) :
    PowerSeries.mk (fun n ↦ s.esymm n) =
      (s.map fun x ↦
        (1 : PowerSeries R) + PowerSeries.C x * PowerSeries.X).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      ext n
      cases n <;> simp [Multiset.esymm]
  | @cons x s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, ← ih]
      ext n
      cases n with
      | zero => simp [Multiset.esymm]
      | succ n =>
          rw [PowerSeries.coeff_mk, esymm_cons_succ]
          rw [add_mul, one_mul, mul_assoc]
          simp [add_comm]

/-- **Finite elementary generating product.**  For every finite alphabet over
a commutative semiring,

`E_a(X) = product_i (1 + a_i X)`.

The identity includes the empty alphabet and requires no subtraction,
cancellation, characteristic, or nonvanishing hypothesis. -/
theorem elementarySymmetricGeneratingSeries_eq_prod
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (a : ι → R) :
    elementarySymmetricGeneratingSeries a =
      ∏ i : ι,
        ((1 : PowerSeries R) + PowerSeries.C (a i) * PowerSeries.X) := by
  classical
  change PowerSeries.mk
      (fun n ↦ (Finset.univ.val.map a).esymm n) = _
  rw [Finset.prod_eq_multiset_prod]
  simpa only [Multiset.map_map, Function.comp_apply] using
    (mk_esymm_eq_multiset_prod (Finset.univ.val.map a))

private theorem elementarySymmetricEval_neg
    {R ι : Type*} [CommRing R] [Fintype ι]
    (a : ι → R) (n : ℕ) :
    elementarySymmetricEval (-a) n =
      (-1 : R) ^ n * elementarySymmetricEval a n := by
  classical
  have hmap :
      Finset.univ.val.map (-a) =
        (Finset.univ.val.map a).map Neg.neg := by
    rw [Multiset.map_map]
    apply congrArg (fun f : ι → R ↦ Finset.univ.val.map f)
    funext i
    rfl
  change (Finset.univ.val.map (-a)).esymm n =
    (-1 : R) ^ n * (Finset.univ.val.map a).esymm n
  rw [hmap, Multiset.esymm_neg]

/-- **Elementary--complete generating-series reciprocity.**  For every finite
alphabet over a commutative ring,

`E_{-a}(X) * H_a(X) = 1`.

This is a formal identity; it uses no convergence, division, cancellation,
or nonvanishing assumption. -/
theorem elementarySymmetricGeneratingSeries_neg_mul_completeHomogeneousGeneratingSeries
    {R ι : Type*} [CommRing R] [Fintype ι]
    (a : ι → R) :
    elementarySymmetricGeneratingSeries (-a) *
        completeHomogeneousGeneratingSeries a = 1 := by
  ext n
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_elementarySymmetricGeneratingSeries,
    coeff_completeHomogeneousGeneratingSeries,
    elementarySymmetricEval_neg]
  exact
    (sum_elementarySymmetricEval_mul_completeHomogeneousEval a n).trans
      (PowerSeries.coeff_one n).symm

/-- The complete homogeneous generating series is Mathlib's canonical formal
inverse of the negated elementary generating series.  The unit is exactly
`1`, because the elementary series has constant coefficient one. -/
theorem completeHomogeneousGeneratingSeries_eq_invOfUnit_elementarySymmetricGeneratingSeries_neg
    {R ι : Type*} [CommRing R] [Fintype ι]
    (a : ι → R) :
    completeHomogeneousGeneratingSeries a =
      PowerSeries.invOfUnit
        (elementarySymmetricGeneratingSeries (-a)) (1 : Rˣ) := by
  let E : PowerSeries R := elementarySymmetricGeneratingSeries (-a)
  let H : PowerSeries R := completeHomogeneousGeneratingSeries a
  have hconst : PowerSeries.constantCoeff E = ((1 : Rˣ) : R) := by
    change elementarySymmetricEval (-a) 0 = (1 : R)
    simp
  have hprod : E * H = 1 := by
    exact
      elementarySymmetricGeneratingSeries_neg_mul_completeHomogeneousGeneratingSeries a
  change H = PowerSeries.invOfUnit E (1 : Rˣ)
  calc
    H = 1 * H := (one_mul H).symm
    _ = (PowerSeries.invOfUnit E (1 : Rˣ) * E) * H := by
      rw [PowerSeries.invOfUnit_mul E (1 : Rˣ) hconst]
    _ = PowerSeries.invOfUnit E (1 : Rˣ) * (E * H) := by
      rw [mul_assoc]
    _ = PowerSeries.invOfUnit E (1 : Rˣ) := by
      rw [hprod, mul_one]

/-- **Formal reciprocal finite q-binomial theorem.**  Over every commutative
ring and for every `n ≥ 0`, the finite product on the geometric alphabet
`1, q, ..., q^n` is inverse to the Gaussian-coefficient series:

`product_(j=0)^n (1 - q^j X) * sum_(k≥0) [n+k choose k]_q X^k = 1`.

The recursive Gaussian coefficients make this denominator-free and total at
`q = 0`, roots of unity, zero divisors, positive characteristic, and the zero
ring. -/
theorem prod_one_sub_qPow_X_mul_gaussianBinomialGeneratingSeries
    {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    (∏ j : Fin (n + 1),
        ((1 : PowerSeries R) -
          PowerSeries.C (q ^ (j : ℕ)) * PowerSeries.X)) *
      PowerSeries.mk (fun k ↦ gaussianBinomial q (n + k) k) = 1 := by
  let a : Fin (n + 1) → R := fun j ↦ q ^ (j : ℕ)
  have hprod :
      (∏ j : Fin (n + 1),
          ((1 : PowerSeries R) -
            PowerSeries.C (q ^ (j : ℕ)) * PowerSeries.X)) =
        elementarySymmetricGeneratingSeries (-a) := by
    rw [elementarySymmetricGeneratingSeries_eq_prod]
    apply Finset.prod_congr rfl
    intro j _hj
    simp [a, sub_eq_add_neg]
  have hseries :
      PowerSeries.mk (fun k ↦ gaussianBinomial q (n + k) k) =
        completeHomogeneousGeneratingSeries a := by
    ext k
    rw [PowerSeries.coeff_mk,
      coeff_completeHomogeneousGeneratingSeries]
    change gaussianBinomial q (n + k) k =
      completeHomogeneousEval
        (fun j : Fin (n + 1) ↦ q ^ (j : ℕ)) k
    rw [completeHomogeneousEval_geometric]
    have hsymm := gaussianBinomial_symm q
      (show n ≤ k + n by omega)
    have hsub : k + n - n = k := by omega
    rw [hsub] at hsymm
    simpa only [Nat.add_comm] using hsymm
  rw [hprod, hseries]
  exact
    elementarySymmetricGeneratingSeries_neg_mul_completeHomogeneousGeneratingSeries a

end

end Fabius

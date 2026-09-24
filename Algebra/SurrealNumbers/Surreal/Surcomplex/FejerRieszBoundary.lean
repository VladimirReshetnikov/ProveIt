import Surreal.Algebra.CayleyBoundaryCoefficients
import Surreal.Surcomplex.FejerRieszCayley

/-!
# The missing point in the Fejér–Riesz Cayley chart

The value at `-1` is controlled by the coefficient at degree `2N` of the
cleared real polynomial. The same coefficient is the squared modulus of
the coefficient at degree `N` of its norm factor. This proves the missing
endpoint of `trigonometry:thm:fejer` by finite algebra.
-/

universe u
namespace Surreal.Surcomplex.FejerRiesz

open Foundations Polynomial

noncomputable section

/-- At the top degree, a Cayley frequency gives its value at the missing phase. -/
theorem coeff_frequency_I_top (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) :
    (LaurentCayley.frequency (I : Surcomplex.{u}) N k).coeff (2 * N) = (-1 : Surcomplex.{u}) ^ k := by
  rw [LaurentCayley.coeff_frequency_top I N k hk]
  have hi : (I : Surcomplex.{u}) ≠ 0 := by
    intro h
    have he := congrArg (fun z : Surcomplex.{u} => z.im) h
    simp at he
  have hinv : (-I : Surcomplex.{u}) = I⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ hi).mp
    rw [neg_mul, ← pow_two, I_sq, neg_neg]
  have hpow : (((N : ℤ) + k).toNat : ℤ) + -(((N : ℤ) - k).toNat : ℤ) = 2 * k := by omega
  rw [hinv, inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hi,
    hpow, zpow_mul]
  simp only [zpow_ofNat, I_sq]

/-- The top cleared coefficient is exactly the real part of the value at phase `-1`. -/
theorem numerator_coeff_top (p : LaurentPolynomial Surcomplex.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    (numerator p N).coeff (2 * N) = (p.smeval (-1 : Surcomplex.{u}ˣ)).re := by
  rw [numerator, Complexify.realPartPolynomial_coeff]
  congr 1
  simp only [LaurentCayley.numerator, Finsupp.sum, finsetSum_coeff, coeff_C_mul,
    LaurentPolynomial.smeval, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff_frequency_I_top N k (hN k hk)]
  simp

/-- Evaluation of the homogeneous spectral factor at the missing phase. -/
theorem factor_eval_neg_one (q : Polynomial Surcomplex.{u}) (N : ℕ) (hq : q.natDegree ≤ N) :
    (CayleySpectral.factor q N).eval (-1) = q.coeff N * I ^ N := by
  have hB : CayleySpectral.second.eval (-1 : Surcomplex.{u}) = 0 := by
    simp [CayleySpectral.second]
  have hA : CayleySpectral.first.eval (-1 : Surcomplex.{u}) = I := by
    simp only [CayleySpectral.first, eval_mul, eval_C, eval_sub, eval_X, eval_one]
    ring
  rw [CayleySpectral.factor,
    PolynomialHomogeneousTransform.eval_transform_of_second_zero q N hq _ _ _ hB, hA]

/-- The endpoint squared modulus is the squared modulus of the factor's top coefficient. -/
theorem modulus_sq_factor_neg_one (q : Polynomial Surcomplex.{u}) (N : ℕ) (hq : q.natDegree ≤ N) :
    modulus ((CayleySpectral.factor q N).eval (-1)) ^ 2 = modulus (q.coeff N) ^ 2 := by
  rw [factor_eval_neg_one q N hq, modulus_mul]
  have hi : modulus (I : Surcomplex.{u}) = 1 := by
    apply modulus_eq_of_nonneg_sq (by norm_num)
    simp [normSq_eq]
  have hp : modulus ((I : Surcomplex.{u}) ^ N) = 1 := by
    change modulusMonoidWithZeroHom (I ^ N) = 1
    rw [map_pow]
    change modulus I ^ N = 1
    rw [hi, one_pow]
  rw [hp, mul_one]

/-- The exact norm factorization identifies the coefficient at twice the degree bound. -/
theorem norm_factor_coeff_top (p : Polynomial SignSequence.{u}) (q : Polynomial Surcomplex.{u})
    (N : ℕ) (hq : q.natDegree ≤ N)
    (he : p.map ofReal = q * q.map conj.toRingHom) :
    p.coeff (2 * N) = modulus (q.coeff N) ^ 2 := by
  have hc := congrArg (fun P : Polynomial Surcomplex.{u} => P.coeff (N + N)) he
  have hqc : (q.map conj.toRingHom).natDegree ≤ N := by
    rwa [natDegree_map_eq_of_injective conj.injective]
  rw [coeff_map, coeff_mul_add_eq_of_natDegree_le hq hqc, coeff_map] at hc
  apply ofReal_injective
  rw [modulus_sq]
  change ofReal (p.coeff (N + N)) = q.coeff N * conj (q.coeff N) at hc
  simpa only [two_mul, mul_conj] using hc

/-- The same constructed factor agrees with the original Fourier polynomial at phase `-1`. -/
theorem factor_at_neg_one (p : LaurentPolynomial Surcomplex.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N)
    (q : Polynomial Surcomplex.{u}) (hq : q.natDegree ≤ N)
    (he : (numerator p N).map ofReal = q * q.map conj.toRingHom) :
    (p.smeval (-1 : Surcomplex.{u}ˣ)).re = modulus ((CayleySpectral.factor q N).eval (-1)) ^ 2 := by
  rw [modulus_sq_factor_neg_one q N hq, ← numerator_coeff_top p N hN]
  exact norm_factor_coeff_top (numerator p N) q N hq he

end
end Surreal.Surcomplex.FejerRiesz

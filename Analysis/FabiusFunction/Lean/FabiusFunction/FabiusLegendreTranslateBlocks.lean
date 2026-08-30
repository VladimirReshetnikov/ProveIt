import FabiusFunction.RvachevPolynomialSynthesis
import FabiusFunction.FabiusLegendreEnergy

/-!
# Finite Rvachev-translate realizations of the Legendre blocks

Polynomial deconvolution and exact dyadic comb synthesis turn every Legendre
polynomial into a finite sum of shifted copies of Rvachev's `up` function on
`[-1, 1]`.  For the even polynomial `P_(2n)`, the natural exact mesh is
`4^n = 2^(2n)`.

This module packages that specialization at three levels:

* the deconvolved Legendre polynomial and its finite synthesis formula;
* the atom coefficients and finite translate block realizing the existing
  Rvachev--Legendre block `u_n P_(2n)`;
* the literal finite atom-Gram expansion of the block orthogonality formula.

All sums here are finite.  Their common index set is the exact open integer
interval `(-2M, 2M)` supplied by support truncation at mesh `M = 4^n`.
-/

set_option autoImplicit false

open MeasureTheory Polynomial Set Finset
open scoped BigOperators Interval

namespace Fabius

noncomputable section

/-- The Rvachev deconvolution of the degree-`d` Legendre polynomial.  Its
smoothing against a translated copy of `rvachevUp` recovers `P_d`. -/
noncomputable def rvachevLegendreDeconvolutionPolynomial
    (d : ℕ) : ℝ[X] :=
  rvachevDeconvolvedPolynomial (legendrePolynomial d)

/-- **Finite dyadic synthesis of a Legendre polynomial.**  On `[-1,1]`, the
degree-`d` polynomial `P_d` is reconstructed exactly from shifted Rvachev
atoms at mesh `M = 2^d`.  The open interval of integer indices is precisely
`(-2M,2M) = (-2^(d+1),2^(d+1))`. -/
theorem eval_legendrePolynomial_eq_sum_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) (d : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (legendrePolynomial d).eval x =
      ((2 : ℝ) ^ d)⁻¹ *
        ∑ k ∈ Finset.Ioo (-(2 ^ (d + 1) : ℤ)) (2 ^ (d + 1) : ℤ),
          (rvachevLegendreDeconvolutionPolynomial d).eval
              ((k : ℝ) / (2 : ℝ) ^ d) *
            rvachevUp F (x - (k : ℝ) / (2 : ℝ) ^ d) := by
  have hM : (2 ^ d : ℕ) ≠ 0 := by positivity
  have hdeg : (legendrePolynomial d).natDegree ≤
      padicValNat 2 (2 ^ d) := by
    rw [natDegree_legendrePolynomial, padicValNat.prime_pow]
  have hsynth :=
    normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
      F hF hM hdeg hx
  have hendpoint : (2 ^ (d + 1) : ℤ) =
      2 * (((2 ^ d : ℕ) : ℤ)) := by
    push_cast
    rw [pow_succ]
    ring
  rw [hendpoint]
  simpa only [rvachevLegendreDeconvolutionPolynomial, Nat.cast_pow,
    Nat.cast_ofNat] using hsynth.symm

/-- **Even Legendre synthesis at the square-dyadic mesh.**  The degree
`2n` polynomial `P_(2n)` is reconstructed on `[-1,1]` at the exact mesh
`M = 4^n`, with every potentially nonzero atom indexed by `(-2M,2M)`. -/
theorem eval_legendrePolynomial_even_eq_sum_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (legendrePolynomial (2 * n)).eval x =
      ((4 : ℝ) ^ n)⁻¹ *
        ∑ k ∈ Finset.Ioo (-(2 * (4 ^ n : ℤ))) (2 * (4 ^ n : ℤ)),
          (rvachevLegendreDeconvolutionPolynomial (2 * n)).eval
              ((k : ℝ) / (4 : ℝ) ^ n) *
            rvachevUp F (x - (k : ℝ) / (4 : ℝ) ^ n) := by
  have hM : (4 ^ n : ℕ) ≠ 0 := by positivity
  have hfour : (4 ^ n : ℕ) = 2 ^ (2 * n) := by
    calc
      (4 ^ n : ℕ) = (2 ^ 2) ^ n := by norm_num
      _ = 2 ^ (2 * n) := by rw [pow_mul]
  have hdeg : (legendrePolynomial (2 * n)).natDegree ≤
      padicValNat 2 (4 ^ n) := by
    rw [natDegree_legendrePolynomial, hfour, padicValNat.prime_pow]
  have hsynth :=
    normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
      F hF hM hdeg hx
  simpa only [rvachevLegendreDeconvolutionPolynomial, Nat.cast_pow,
    Nat.cast_ofNat] using hsynth.symm

/-- The exact square-dyadic mesh used to synthesize the even Legendre block
of index `n`. -/
def rvachevLegendreScale (n : ℕ) : ℕ :=
  4 ^ n

/-- The finite integer index set of all Rvachev translates that can
contribute to the even Legendre synthesis on `[-1,1]`. -/
def rvachevLegendreIndexSet (n : ℕ) : Finset ℤ :=
  Finset.Ioo (-(2 * (rvachevLegendreScale n : ℤ)))
    (2 * (rvachevLegendreScale n : ℤ))

/-- The coefficient of the translate indexed by `k` in the finite
realization of the `n`-th Rvachev--Legendre block. -/
noncomputable def rvachevLegendreAtomCoefficient
    (F : BoundedFabius) (n : ℕ) (k : ℤ) : ℝ :=
  rvachevLegendreCoefficient F n / (rvachevLegendreScale n : ℝ) *
    (rvachevLegendreDeconvolutionPolynomial (2 * n)).eval
      ((k : ℝ) / (rvachevLegendreScale n : ℝ))

/-- The finite shifted-`up` realization of the `n`-th
Rvachev--Legendre block. -/
noncomputable def rvachevLegendreTranslateBlock
    (F : BoundedFabius) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ rvachevLegendreIndexSet n,
    rvachevLegendreAtomCoefficient F n k *
      rvachevUp F
        (x - (k : ℝ) / (rvachevLegendreScale n : ℝ))

/-- On `[-1,1]`, the finite shifted-`up` realization is exactly the existing
Legendre block `u_n P_(2n)`. -/
theorem rvachevLegendreTranslateBlock_eq_rvachevLegendreBlock
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    rvachevLegendreTranslateBlock F n x =
      rvachevLegendreBlock F n x := by
  have hsynth :
      (legendrePolynomial (2 * n)).eval x =
        ((rvachevLegendreScale n : ℕ) : ℝ)⁻¹ *
          ∑ k ∈ rvachevLegendreIndexSet n,
            (rvachevLegendreDeconvolutionPolynomial (2 * n)).eval
                ((k : ℝ) / (rvachevLegendreScale n : ℝ)) *
              rvachevUp F
                (x - (k : ℝ) / (rvachevLegendreScale n : ℝ)) := by
    simpa only [rvachevLegendreScale, rvachevLegendreIndexSet,
      Nat.cast_pow, Nat.cast_ofNat] using
        eval_legendrePolynomial_even_eq_sum_rvachevUp F hF n hx
  calc
    rvachevLegendreTranslateBlock F n x =
        (rvachevLegendreCoefficient F n /
            (rvachevLegendreScale n : ℝ)) *
          ∑ k ∈ rvachevLegendreIndexSet n,
            (rvachevLegendreDeconvolutionPolynomial (2 * n)).eval
                ((k : ℝ) / (rvachevLegendreScale n : ℝ)) *
              rvachevUp F
                (x - (k : ℝ) / (rvachevLegendreScale n : ℝ)) := by
      rw [rvachevLegendreTranslateBlock, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [rvachevLegendreAtomCoefficient]
      ring
    _ = rvachevLegendreCoefficient F n *
        (legendrePolynomial (2 * n)).eval x := by
      rw [hsynth]
      ring
    _ = rvachevLegendreBlock F n x := rfl

/-- Orthogonality of the finite translate realizations.  Their interval
inner product is the same diagonal/off-diagonal formula as for the existing
Rvachev--Legendre blocks. -/
theorem intervalIntegral_rvachevLegendreTranslateBlock_mul
    (F : BoundedFabius) (hF : IsFabius F) (m n : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      rvachevLegendreTranslateBlock F m x *
        rvachevLegendreTranslateBlock F n x) =
      if m = n then
        2 * (rvachevLegendreCoefficient F n) ^ 2 /
          (((4 * n + 1 : ℕ) : ℝ))
      else 0 := by
  calc
    (∫ x in (-1 : ℝ)..1,
      rvachevLegendreTranslateBlock F m x *
        rvachevLegendreTranslateBlock F n x) =
        ∫ x in (-1 : ℝ)..1,
          rvachevLegendreBlock F m x * rvachevLegendreBlock F n x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (-1 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
      change rvachevLegendreTranslateBlock F m x *
          rvachevLegendreTranslateBlock F n x =
        rvachevLegendreBlock F m x * rvachevLegendreBlock F n x
      rw [rvachevLegendreTranslateBlock_eq_rvachevLegendreBlock F hF m hx',
        rvachevLegendreTranslateBlock_eq_rvachevLegendreBlock F hF n hx']
    _ = _ := intervalIntegral_rvachevLegendreBlock_mul F m n

/-- The interval Gram entry of two shifted Rvachev atoms, where the first
atom lives on the `4^m` mesh and the second on the `4^n` mesh. -/
noncomputable def rvachevTranslateGram
    (F : BoundedFabius) (m n : ℕ) (k l : ℤ) : ℝ :=
  ∫ x in (-1 : ℝ)..1,
    rvachevUp F
        (x - (k : ℝ) / (rvachevLegendreScale m : ℝ)) *
      rvachevUp F
        (x - (l : ℝ) / (rvachevLegendreScale n : ℝ))

/-- **Literal finite atom-Gram form of Legendre orthogonality.**  Expanding
both finite translate blocks and integrating term by term gives the exact
double sum of atom coefficients against shifted-`up` Gram entries.  It equals
the usual diagonal energy and vanishes off the diagonal. -/
theorem sum_rvachevLegendreAtomCoefficient_mul_gram
    (F : BoundedFabius) (hF : IsFabius F) (m n : ℕ) :
    ∑ k ∈ rvachevLegendreIndexSet m,
      ∑ l ∈ rvachevLegendreIndexSet n,
        rvachevLegendreAtomCoefficient F m k *
          rvachevLegendreAtomCoefficient F n l *
            rvachevTranslateGram F m n k l =
      if m = n then
        2 * (rvachevLegendreCoefficient F n) ^ 2 /
          (((4 * n + 1 : ℕ) : ℝ))
      else 0 := by
  let term : ℤ → ℤ → ℝ → ℝ := fun k l x =>
    (rvachevLegendreAtomCoefficient F m k *
        rvachevUp F
          (x - (k : ℝ) / (rvachevLegendreScale m : ℝ))) *
      (rvachevLegendreAtomCoefficient F n l *
        rvachevUp F
          (x - (l : ℝ) / (rvachevLegendreScale n : ℝ)))
  have htermIntegrable (k l : ℤ) :
      IntervalIntegrable (term k l) volume (-1 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    exact
      (continuous_const.mul
        ((rvachev_contDiff F hF).continuous.comp
          (continuous_id.sub continuous_const))).mul
        (continuous_const.mul
          ((rvachev_contDiff F hF).continuous.comp
            (continuous_id.sub continuous_const)))
  have hrowIntegrable (k : ℤ) :
      IntervalIntegrable
        (fun x : ℝ => ∑ l ∈ rvachevLegendreIndexSet n, term k l x)
        volume (-1 : ℝ) 1 := by
    have h := IntervalIntegrable.sum (rvachevLegendreIndexSet n)
      (f := fun l => term k l) (fun l _hl => htermIntegrable k l)
    have heq :
        (fun x : ℝ => ∑ l ∈ rvachevLegendreIndexSet n, term k l x) =
          ∑ l ∈ rvachevLegendreIndexSet n, term k l := by
      funext x
      simp only [Finset.sum_apply]
    rw [heq]
    exact h
  have hswap :
      (∫ x in (-1 : ℝ)..1,
        ∑ k ∈ rvachevLegendreIndexSet m,
          ∑ l ∈ rvachevLegendreIndexSet n, term k l x) =
        ∑ k ∈ rvachevLegendreIndexSet m,
          ∑ l ∈ rvachevLegendreIndexSet n,
            ∫ x in (-1 : ℝ)..1, term k l x := by
    rw [intervalIntegral.integral_finsetSum
      (fun k _hk => hrowIntegrable k)]
    exact Finset.sum_congr rfl fun k _hk =>
      intervalIntegral.integral_finsetSum
        (fun l _hl => htermIntegrable k l)
  have hpoint (x : ℝ) :
      rvachevLegendreTranslateBlock F m x *
          rvachevLegendreTranslateBlock F n x =
        ∑ k ∈ rvachevLegendreIndexSet m,
          ∑ l ∈ rvachevLegendreIndexSet n, term k l x := by
    simp only [rvachevLegendreTranslateBlock, term]
    rw [Finset.sum_mul_sum]
  have hintegral (k l : ℤ) :
      (∫ x in (-1 : ℝ)..1, term k l x) =
        rvachevLegendreAtomCoefficient F m k *
          rvachevLegendreAtomCoefficient F n l *
            rvachevTranslateGram F m n k l := by
    calc
      (∫ x in (-1 : ℝ)..1, term k l x) =
          ∫ x in (-1 : ℝ)..1,
            (rvachevLegendreAtomCoefficient F m k *
              rvachevLegendreAtomCoefficient F n l) *
              (rvachevUp F
                  (x - (k : ℝ) / (rvachevLegendreScale m : ℝ)) *
                rvachevUp F
                  (x - (l : ℝ) / (rvachevLegendreScale n : ℝ))) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        simp only [term]
        ring
      _ = rvachevLegendreAtomCoefficient F m k *
          rvachevLegendreAtomCoefficient F n l *
            rvachevTranslateGram F m n k l := by
        rw [intervalIntegral.integral_const_mul]
        rfl
  calc
    (∑ k ∈ rvachevLegendreIndexSet m,
      ∑ l ∈ rvachevLegendreIndexSet n,
        rvachevLegendreAtomCoefficient F m k *
          rvachevLegendreAtomCoefficient F n l *
            rvachevTranslateGram F m n k l) =
        ∑ k ∈ rvachevLegendreIndexSet m,
          ∑ l ∈ rvachevLegendreIndexSet n,
            ∫ x in (-1 : ℝ)..1, term k l x := by
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro l _hl
      exact (hintegral k l).symm
    _ = ∫ x in (-1 : ℝ)..1,
        ∑ k ∈ rvachevLegendreIndexSet m,
          ∑ l ∈ rvachevLegendreIndexSet n, term k l x := hswap.symm
    _ = ∫ x in (-1 : ℝ)..1,
        rvachevLegendreTranslateBlock F m x *
          rvachevLegendreTranslateBlock F n x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      exact (hpoint x).symm
    _ = _ := intervalIntegral_rvachevLegendreTranslateBlock_mul F hF m n

end
end Fabius

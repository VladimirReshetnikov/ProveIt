import ExponentialIdentities.TwoBaseIntegerExponent.ExponentialPolynomialZeros
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# Sparse interpolation on an irrational power curve

This module formalizes the fewnomial lower bound used in the matrix-coefficient continuation
of the Alaoglu--Erdős report.  On the curve

`z ↦ (exp z, exp (β z))`,

a monomial with exponent pair `(r,s)` restricts to the exponential
`exp ((r + s β) z)`.  When `β` is irrational, distinct exponent pairs give distinct
frequencies.  The zero-count theorem from `ExponentialPolynomialZeros` therefore implies
that a nonzero `m`-term relation cannot vanish at `m` distinct real parameters.

The final theorem packages the corresponding nonsingularity of every square generalized
evaluation matrix.  It is the kernel-checked lower-bound half of the exact `R + 1` sparse
interpolation threshold in the report; ordinary univariate interpolation supplies the matching
paper-level upper bound.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- The frequency obtained by restricting the bivariate monomial `X^r Y^s` to
`(X,Y) = (exp z, exp (β z))`. -/
def powerCurveFrequency (β : ℝ) (rs : ℕ × ℕ) : ℝ :=
  (rs.1 : ℝ) + (rs.2 : ℝ) * β

@[simp] theorem powerCurveFrequency_mk (β : ℝ) (r s : ℕ) :
    powerCurveFrequency β (r, s) = (r : ℝ) + (s : ℝ) * β := rfl

/-- Irrationality of the power-curve exponent makes the monomial frequencies injective. -/
theorem powerCurveFrequency_injective {β : ℝ} (hβ : Irrational β) :
    Function.Injective (powerCurveFrequency β) :=
  IntegerExponent.Irrational.injective_nat_add_mul hβ

/-- A sparse relation with `n+1` distinct monomials on an irrational power curve cannot
vanish at `n+1` strictly increasing real parameters unless all coefficients vanish.  The
monomials may be supplied in arbitrary order; they are sorted internally by frequency. -/
theorem sparsePowerCurve_coeff_eq_zero_of_zeros {n : ℕ} {β : ℝ}
    (hβ : Irrational β) (rs : Fin (n + 1) → ℕ × ℕ) (hrs : Function.Injective rs)
    (c : Fin (n + 1) → ℝ) (z : Fin (n + 1) → ℝ) (hz : StrictMono z)
    (hzero : ∀ i,
      ∑ j, c j * Real.exp (powerCurveFrequency β (rs j) * z i) = 0) :
    ∀ j, c j = 0 := by
  let sigma : Equiv.Perm (Fin (n + 1)) :=
    Tuple.sort (fun j ↦ powerCurveFrequency β (rs j))
  let lam : Fin (n + 1) → ℝ :=
    fun j ↦ powerCurveFrequency β (rs (sigma j))
  let c' : Fin (n + 1) → ℝ := fun j ↦ c (sigma j)
  have hlamMonotone : Monotone lam := by
    exact Tuple.monotone_sort (fun j ↦ powerCurveFrequency β (rs j))
  have hlamInjective : Function.Injective lam := by
    exact ((powerCurveFrequency_injective hβ).comp hrs).comp sigma.injective
  have hlam : StrictMono lam := hlamMonotone.strictMono_of_injective hlamInjective
  have hzero' : ∀ i, expPoly lam c' (z i) = 0 := by
    intro i
    rw [expPoly_apply]
    calc
      (∑ j, c' j * Real.exp (lam j * z i)) =
          ∑ j, c j * Real.exp (powerCurveFrequency β (rs j) * z i) := by
            exact Equiv.sum_comp sigma
              (fun j ↦ c j * Real.exp (powerCurveFrequency β (rs j) * z i))
      _ = 0 := hzero i
  have hc' := expPoly_coeff_eq_zero_of_zeros lam c' hlam z hz hzero'
  intro j
  have h := hc' (sigma.symm j)
  simpa [c'] using h

/-- Finite-set zero-count form: a nonzero sparse relation with `n+1` distinct monomials has
at most `n` distinct zeros on an irrational power curve. -/
theorem card_le_of_sparsePowerCurve_eq_zero {n : ℕ} {β : ℝ}
    (hβ : Irrational β) (rs : Fin (n + 1) → ℕ × ℕ) (hrs : Function.Injective rs)
    (c : Fin (n + 1) → ℝ) (hc : ∃ j, c j ≠ 0) (S : Finset ℝ)
    (hzero : ∀ z ∈ S,
      ∑ j, c j * Real.exp (powerCurveFrequency β (rs j) * z) = 0) :
    S.card ≤ n := by
  let sigma : Equiv.Perm (Fin (n + 1)) :=
    Tuple.sort (fun j ↦ powerCurveFrequency β (rs j))
  let lam : Fin (n + 1) → ℝ :=
    fun j ↦ powerCurveFrequency β (rs (sigma j))
  let c' : Fin (n + 1) → ℝ := fun j ↦ c (sigma j)
  have hlamMonotone : Monotone lam := by
    exact Tuple.monotone_sort (fun j ↦ powerCurveFrequency β (rs j))
  have hlamInjective : Function.Injective lam := by
    exact ((powerCurveFrequency_injective hβ).comp hrs).comp sigma.injective
  have hlam : StrictMono lam := hlamMonotone.strictMono_of_injective hlamInjective
  have hc' : ∃ j, c' j ≠ 0 := by
    obtain ⟨j, hj⟩ := hc
    exact ⟨sigma.symm j, by simpa [c'] using hj⟩
  apply card_le_of_expPoly_eq_zero lam c' hlam hc' S
  intro z hzS
  rw [expPoly_apply]
  calc
    (∑ j, c' j * Real.exp (lam j * z)) =
        ∑ j, c j * Real.exp (powerCurveFrequency β (rs j) * z) := by
          exact Equiv.sum_comp sigma
            (fun j ↦ c j * Real.exp (powerCurveFrequency β (rs j) * z))
    _ = 0 := hzero z hzS

/-- The square generalized evaluation matrix attached to monomial exponent pairs and curve
parameters. -/
def sparsePowerCurveMatrix {m : ℕ} (β : ℝ) (rs : Fin m → ℕ × ℕ)
    (z : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j ↦ Real.exp (powerCurveFrequency β (rs j) * z i)

@[simp] theorem sparsePowerCurveMatrix_apply {m : ℕ} (β : ℝ)
    (rs : Fin m → ℕ × ℕ) (z : Fin m → ℝ) (i j : Fin m) :
    sparsePowerCurveMatrix β rs z i j =
      Real.exp (powerCurveFrequency β (rs j) * z i) := rfl

/-- Every square evaluation matrix formed from distinct monomials and distinct ordered
parameters on an irrational power curve is nonsingular. -/
theorem det_sparsePowerCurveMatrix_ne_zero {n : ℕ} {β : ℝ}
    (hβ : Irrational β) (rs : Fin (n + 1) → ℕ × ℕ) (hrs : Function.Injective rs)
    (z : Fin (n + 1) → ℝ) (hz : StrictMono z) :
    (sparsePowerCurveMatrix β rs z).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  funext j
  apply sparsePowerCurve_coeff_eq_zero_of_zeros hβ rs hrs v z hz
  intro i
  have h0 := congrFun hmul i
  rw [Matrix.mulVec_apply_eq_sum] at h0
  simp only [Pi.zero_apply, sparsePowerCurveMatrix_apply] at h0
  calc
    (∑ j, v j * Real.exp (powerCurveFrequency β (rs j) * z i)) =
        ∑ j, Real.exp (powerCurveFrequency β (rs j) * z i) * v j := by
          exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    _ = 0 := h0

/-! ## Integral evaluation determinants -/

/-- The integer evaluation matrix whose `(i,j)` entry is
`x_i ^ r_j * y_i ^ s_j`. -/
def natPowerCurveEvaluationMatrix {m : ℕ} (x y : Fin m → ℕ)
    (rs : Fin m → ℕ × ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun i j ↦ ((x i) ^ (rs j).1 * (y i) ^ (rs j).2 : ℕ)

/-- If `y_i = x_i ^ β`, an entry of the integral evaluation matrix is the corresponding
real power with frequency `r_j + s_j β`. -/
theorem cast_natPowerCurveEvaluationMatrix_apply {m : ℕ} {β : ℝ}
    (x y : Fin m → ℕ) (rs : Fin m → ℕ × ℕ)
    (hxpos : ∀ i, 0 < x i)
    (hy : ∀ i, (y i : ℝ) = (x i : ℝ) ^ β) (i j : Fin m) :
    (((natPowerCurveEvaluationMatrix x y rs i j : ℤ) : ℝ)) =
      (x i : ℝ) ^ powerCurveFrequency β (rs j) := by
  have hxR : (0 : ℝ) < x i := by exact_mod_cast hxpos i
  rw [natPowerCurveEvaluationMatrix]
  simp only [Matrix.of_apply]
  push_cast
  rw [hy i]
  rw [← Real.rpow_natCast (x i : ℝ) (rs j).1]
  rw [← Real.rpow_mul_natCast hxR.le β (rs j).2]
  rw [← Real.rpow_add hxR]
  simp only [powerCurveFrequency, mul_comm]

/-- **Generalized evaluation determinant.**  If the natural points satisfy
`y_i = x_i ^ β` for an irrational `β`, then every square evaluation matrix built from
distinct monomials has nonzero integer determinant.  Hence its absolute value is at least
one.  This is the finite arithmetic form of the sparse-support obstruction in the report. -/
theorem det_natPowerCurveEvaluationMatrix_ne_zero {n : ℕ} {β : ℝ}
    (hβ : Irrational β) (x y : Fin (n + 1) → ℕ) (rs : Fin (n + 1) → ℕ × ℕ)
    (hx : StrictMono x) (hx0 : 0 < x 0)
    (hy : ∀ i, (y i : ℝ) = (x i : ℝ) ^ β) (hrs : Function.Injective rs) :
    (natPowerCurveEvaluationMatrix x y rs).det ≠ 0 := by
  have hxpos : ∀ i, 0 < x i := fun i ↦ hx0.trans_le (hx.monotone (Fin.zero_le i))
  let z : Fin (n + 1) → ℝ := fun i ↦ Real.log (x i)
  have hz : StrictMono z := by
    intro i j hij
    have hxi : (0 : ℝ) < x i := by exact_mod_cast hxpos i
    apply Real.strictMonoOn_log
    · exact hxi
    · show (0 : ℝ) < x j
      exact_mod_cast hxpos j
    · exact_mod_cast hx hij
  have hmatrix : (Int.castRingHom ℝ).mapMatrix (natPowerCurveEvaluationMatrix x y rs) =
      sparsePowerCurveMatrix β rs z := by
    ext i j
    rw [RingHom.mapMatrix_apply]
    simp only [Matrix.map_apply, sparsePowerCurveMatrix_apply, z]
    change (((natPowerCurveEvaluationMatrix x y rs i j : ℤ) : ℝ)) = _
    rw [cast_natPowerCurveEvaluationMatrix_apply x y rs hxpos hy]
    rw [Real.rpow_def_of_pos (by exact_mod_cast hxpos i)]
    ring_nf
  intro hdet
  have hcast : (Int.castRingHom ℝ) (natPowerCurveEvaluationMatrix x y rs).det = 0 := by
    rw [hdet, map_zero]
  have hdetR : (sparsePowerCurveMatrix β rs z).det = 0 := by
    rw [← hmatrix, ← (Int.castRingHom ℝ).map_det]
    exact hcast
  exact det_sparsePowerCurveMatrix_ne_zero hβ rs hrs z hz hdetR

/-! ## The matching `R + 1`-term interpolant -/

open Polynomial

private theorem esymm_pos_of_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i, 0 < x i) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    0 < ((Finset.univ : Finset ι).val.map x).esymm k := by
  rw [Finset.esymm_map_val]
  apply Finset.sum_pos
  · intro t _ht
    apply Finset.prod_pos
    intro i _hi
    exact hx i
  · rw [← Finset.card_pos, Finset.card_powersetCard]
    exact Nat.choose_pos hk

/-- The ordinary univariate polynomial `∏ᵢ (X - xᵢ)` through a family of positive nodes. -/
def positiveNodeInterpolant {m : ℕ} (x : Fin m → ℝ) : ℝ[X] :=
  (((Finset.univ : Finset (Fin m)).val.map x).map fun t ↦ X - C t).prod

/-- Every coefficient of the positive-node interpolant, from degree zero through degree
`m`, is nonzero.  Positivity prevents cancellation in every elementary symmetric sum. -/
theorem positiveNodeInterpolant_coeff_ne_zero {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) {k : ℕ} (hk : k ≤ m) :
    (positiveNodeInterpolant x).coeff k ≠ 0 := by
  have hk' : k ≤ ((Finset.univ : Finset (Fin m)).val.map x).card := by simpa using hk
  rw [positiveNodeInterpolant, Multiset.prod_X_sub_C_coeff _ hk']
  apply mul_ne_zero
  · exact pow_ne_zero _ (by norm_num)
  · exact (esymm_pos_of_pos x hx
      (k := ((Finset.univ : Finset (Fin m)).val.map x).card - k) (by simp)).ne'

/-- The positive-node interpolant has exactly `m + 1` monomials.  Together with the sparse
zero bound above, this is the exact `R + 1` threshold for `R` positive nodes on an irrational
power curve. -/
theorem positiveNodeInterpolant_support_card {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) :
    (positiveNodeInterpolant x).support.card = m + 1 := by
  have hdeg : (positiveNodeInterpolant x).natDegree = m := by
    change ((((Finset.univ : Finset (Fin m)).val.map x).map
      fun t ↦ X - C t).prod).natDegree = m
    rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
    simp
  have hrange : Finset.range (m + 1) ⊆ (positiveNodeInterpolant x).support := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Polynomial.mem_support_iff]
    exact positiveNodeInterpolant_coeff_ne_zero x hx (by omega)
  apply le_antisymm
  · simpa [hdeg] using Polynomial.card_supp_le_succ_natDegree (positiveNodeInterpolant x)
  · simpa using Finset.card_le_card hrange

/-- Every supplied node is a zero of its positive-node interpolant. -/
theorem positiveNodeInterpolant_eval {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    (positiveNodeInterpolant x).eval (x i) = 0 := by
  rw [positiveNodeInterpolant, Polynomial.eval_multiset_prod]
  apply Multiset.prod_eq_zero
  rw [Multiset.mem_map]
  refine ⟨X - C (x i), ?_, by simp⟩
  rw [Multiset.mem_map]
  exact ⟨x i, by simp, rfl⟩

end

end LeanProofs.TwoBaseIntegerExponent

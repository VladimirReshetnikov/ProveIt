import GRHArticle.SingularModuli.Support
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith

/-!
# Matrices of powers at points of separated sizes

The separated conjugate sizes lemma in the GRH article (section "Sparse singular moduli")
follows from row diagonal dominance after positive column scaling. Consequently a nonzero
polynomial vanishing at all of the points has more terms than there are points.
-/

open scoped BigOperators

namespace GRHArticle.SingularModuli

private theorem det_ne_zero_of_scaled_row_dominance {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℝ)
    (h : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j * (c j : ℂ)‖ <
      ‖A i i * (c i : ℂ)‖) : A.det ≠ 0 := by
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j => (c j : ℂ)
  have hscaled : (A * D).det ≠ 0 := det_ne_zero_of_sum_row_lt_diag (by
    simpa only [D, Matrix.mul_diagonal] using h)
  intro hzero
  exact hscaled (by rw [Matrix.det_mul, hzero, zero_mul])

/-- A row growing by a factor of at least four towards its diagonal, and shrinking
at the same rate after it, is strictly diagonally dominant. Each side telescopes
to a bound of one third of the diagonal. -/
private theorem sum_off_diagonal_lt {n : ℕ} (i : Fin n) (w : ℕ → ℝ)
    (hw : ∀ j, 0 < w j)
    (hl : ∀ j < (i : ℕ), 4 * w j ≤ w (j + 1))
    (hr : ∀ j, (i : ℕ) ≤ j → j + 1 < n → 4 * w (j + 1) ≤ w j) :
    ∑ j ∈ Finset.univ.erase i, w (j : ℕ) < w (i : ℕ) := by
  have hleft : 3 * (∑ j ∈ Finset.range (i : ℕ), w j) ≤ w (i : ℕ) - w 0 := by
    rw [Finset.mul_sum, ← Nat.Ico_zero_eq_range, ← Finset.sum_Ico_sub w (Nat.zero_le _)]
    exact Finset.sum_le_sum fun j hj => by
      have hstep := hl j (Finset.mem_Ico.mp hj).2
      linarith only [hstep]
  have hi : (i : ℕ) ≤ n - 1 := by omega
  have hshift := Finset.sum_Ico_add' w (i : ℕ) (n - 1) 1
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hshift
  have hright : 3 * (∑ j ∈ Finset.Ico ((i : ℕ) + 1) n, w j) ≤ w (i : ℕ) - w (n - 1) := by
    rw [← hshift, Finset.mul_sum]
    calc
      _ ≤ ∑ j ∈ Finset.Ico (i : ℕ) (n - 1), (w j - w (j + 1)) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hji, hjn⟩ := Finset.mem_Ico.mp hj
        have hstep := hr j hji (by omega)
        linarith only [hstep]
      _ = -(∑ j ∈ Finset.Ico (i : ℕ) (n - 1), (w (j + 1) - w j)) := by
        simp only [← Finset.sum_neg_distrib, neg_sub]
      _ = _ := by rw [Finset.sum_Ico_sub w hi, neg_sub]
  have hsum := Finset.sum_erase_add Finset.univ (fun j : Fin n => w (j : ℕ))
    (Finset.mem_univ i)
  rw [Fin.sum_univ_eq_sum_range] at hsum
  have hsplit := Finset.sum_range_add_sum_Ico w (Nat.succ_le_of_lt i.isLt)
  rw [Finset.sum_range_succ] at hsplit
  linarith only [hleft, hright, hsum, hsplit, hw 0, hw (n - 1), hw (i : ℕ)]

private theorem four_mul_pow_le_pow {a b : ℝ} (ha : 0 ≤ a) (hab : 4 * a ≤ b)
    {k : ℕ} (hk : k ≠ 0) :
    4 * a ^ k ≤ b ^ k := by
  calc
    4 * a ^ k ≤ 4 ^ k * a ^ k :=
      mul_le_mul_of_nonneg_right (le_self_pow₀ (by norm_num) hk) (pow_nonneg ha _)
    _ = (4 * a) ^ k := (mul_pow _ _ _).symm
    _ ≤ b ^ k := pow_le_pow_left₀ (mul_nonneg (by norm_num) ha) hab _

/-- The generalized Vandermonde matrix at nonzero complex points is nonsingular
when consecutive moduli grow by at least a factor of sixteen. -/
theorem separatedVandermonde_det_ne_zero {n : ℕ}
    (z : Fin n → ℂ) (e : Fin n → ℕ)
    (hz : ∀ i, z i ≠ 0)
    (hsep : ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → 16 * ‖z i‖ ≤ ‖z j‖)
    (he : StrictMono e) :
    (Matrix.of fun i j => z i ^ e j).det ≠ 0 := by
  let r (i : ℕ) : ℝ := if h : i < n then ‖z ⟨i, h⟩‖ else 1
  let E (j : ℕ) : ℕ := if h : j < n then e ⟨j, h⟩ else 0
  have hr (i : ℕ) : 0 < r i := by
    dsimp [r]
    split
    · exact norm_pos_iff.mpr (hz _)
    · exact zero_lt_one
  have hr_fin (i : Fin n) : r i = ‖z i‖ := by simp [r, i.isLt]
  have hE_fin (j : Fin n) : E j = e j := by simp [E, j.isLt]
  have hr_sep {j : ℕ} (hj : j + 1 < n) : 16 * r j ≤ r (j + 1) := by
    let a : Fin n := ⟨j, by omega⟩
    let b : Fin n := ⟨j + 1, hj⟩
    change 16 * r (a : ℕ) ≤ r (b : ℕ)
    simpa only [hr_fin] using hsep a b rfl
  have hr_mono {j k : ℕ} (hjk : j ≤ k) (hk : k < n) : r j ≤ r k := by
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hjk ih =>
      exact (ih (by omega)).trans (by linarith only [hr_sep hk, hr k])
  have hE_step {j : ℕ} (hj : j + 1 < n) : E j < E (j + 1) := by
    let a : Fin n := ⟨j, by omega⟩
    let b : Fin n := ⟨j + 1, hj⟩
    change E (a : ℕ) < E (b : ℕ)
    simpa only [hE_fin] using he (show a < b from Nat.lt_succ_self j)
  /- The intermediate base is four times the smaller endpoint, and at most
     one quarter of the larger endpoint. -/
  let d (j : ℕ) : ℝ := (4 * r j) ^ (E (j + 1) - E j)
  let c (j : ℕ) : ℝ := ∏ k ∈ Finset.range j, (d k)⁻¹
  have hd (j : ℕ) : 0 < d j := pow_pos (mul_pos (by norm_num) (hr j)) _
  have hc (j : ℕ) : 0 < c j := Finset.prod_pos fun k _ => inv_pos.mpr (hd k)
  have hc_step (j : ℕ) : c (j + 1) * d j = c j := by
    dsimp [c]
    rw [Finset.prod_range_succ, mul_assoc, inv_mul_cancel₀ (hd j).ne', mul_one]
  apply det_ne_zero_of_scaled_row_dominance _ (fun j => c j)
  intro i
  let w (j : ℕ) : ℝ := r i ^ E j * c j
  have hw (j : ℕ) : 0 < w j := mul_pos (pow_pos (hr i) _) (hc j)
  have hw_step (j : ℕ) (hj : j + 1 < n) :
      w (j + 1) * d j = w j * r i ^ (E (j + 1) - E j) := by
    have hpow : r i ^ E (j + 1) = r i ^ E j * r i ^ (E (j + 1) - E j) := by
      rw [← pow_add, Nat.add_sub_of_le (hE_step hj).le]
    unfold w
    rw [hpow, ← hc_step j]
    ac_rfl
  have hl (j : ℕ) (hji : j < (i : ℕ)) : 4 * w j ≤ w (j + 1) := by
    have hj : j + 1 < n := by omega
    have hbase : 4 * (4 * r j) ≤ r i := by
      simpa only [← mul_assoc, show (4 : ℝ) * 4 = 16 by norm_num] using
        (hr_sep hj).trans (hr_mono (by omega : j + 1 ≤ (i : ℕ)) i.isLt)
    have hpow : 4 * d j ≤ r i ^ (E (j + 1) - E j) :=
      four_mul_pow_le_pow (mul_nonneg (by norm_num) (hr j).le) hbase
        (Nat.sub_ne_zero_of_lt (hE_step hj))
    apply (mul_le_mul_iff_left₀ (hd j)).mp
    rw [hw_step j hj]
    calc
      4 * w j * d j = w j * (4 * d j) := by ac_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (hw j).le
  have hr' (j : ℕ) (hij : (i : ℕ) ≤ j) (hj : j + 1 < n) : 4 * w (j + 1) ≤ w j := by
    have hbase : 4 * r i ≤ 4 * r j :=
      mul_le_mul_of_nonneg_left (hr_mono hij (by omega)) (by norm_num)
    have hpow : 4 * r i ^ (E (j + 1) - E j) ≤ d j :=
      four_mul_pow_le_pow (hr i).le hbase (Nat.sub_ne_zero_of_lt (hE_step hj))
    apply (mul_le_mul_iff_left₀ (hd j)).mp
    rw [mul_assoc, hw_step j hj]
    calc
      4 * (w j * r i ^ (E (j + 1) - E j)) = w j * (4 * r i ^ (E (j + 1) - E j)) := by
        ac_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (hw j).le
  have hweight (j : Fin n) : ‖z i ^ e j * (c j : ℂ)‖ = w j := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hc j).le]
    simp only [w, hr_fin, hE_fin]
  simpa only [Matrix.of_apply, hweight] using sum_off_diagonal_lt i w hw hl hr'

/-- Kernel triviality for the generalized Vandermonde matrix at points of
separated moduli. -/
theorem separatedVandermonde_mulVec_injective {n : ℕ}
    (z : Fin n → ℂ) (e : Fin n → ℕ)
    (hz : ∀ i, z i ≠ 0)
    (hsep : ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → 16 * ‖z i‖ ≤ ‖z j‖)
    (he : StrictMono e) :
    Function.Injective (Matrix.of fun i j => z i ^ e j).mulVec := by
  exact Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (separatedVandermonde_det_ne_zero z e hz hsep he)))

/-- A complex polynomial with at most `n` nonzero coefficients that vanishes at `n`
nonzero points with separated moduli must be zero. -/
theorem eq_zero_of_small_support_eval_at_separated {n : ℕ}
    (p : Polynomial ℂ) (z : Fin n → ℂ)
    (hz : ∀ i, z i ≠ 0)
    (hsep : ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → 16 * ‖z i‖ ≤ ‖z j‖)
    (hp : p.support.card ≤ n) (heval : ∀ i, p.eval (z i) = 0) :
    p = 0 := by
  let e := p.support.orderEmbOfFin rfl
  let x (i : Fin p.support.card) : ℂ := z (Fin.castLE hp i)
  let v (j : Fin p.support.card) : ℂ := p.coeff (e j)
  have hinj := separatedVandermonde_mulVec_injective x e (fun i => hz (Fin.castLE hp i))
    (fun i j hij => hsep (Fin.castLE hp i) (Fin.castLE hp j) hij) e.strictMono
  have hker : (Matrix.of fun i j => x i ^ e j).mulVec v = 0 := by
    funext i
    calc
      _ = ∑ j, p.coeff (e j) * x i ^ e j := by
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, v, mul_comm]
      _ = p.eval (x i) := by
        rw [Polynomial.eval_eq_sum, Polynomial.sum]
        conv_rhs =>
          rw [← p.support.map_orderEmbOfFin_univ (k := p.support.card) rfl]
        rw [Finset.sum_map]
        rfl
      _ = (0 : Fin p.support.card → ℂ) i := heval (Fin.castLE hp i)
  have hv : v = 0 := hinj (by simpa only [Matrix.mulVec_zero] using hker)
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_zero]
  by_contra hk
  have hmem : k ∈ Set.range e := by
    rw [Finset.range_orderEmbOfFin]
    exact Polynomial.mem_support_iff.mpr hk
  obtain ⟨j, rfl⟩ := hmem
  exact hk (congrFun hv j)

/-- The separated-size support bound for polynomials over a coefficient field
embedded in the complex numbers, in particular for rational polynomials. -/
theorem eq_zero_of_small_support_aeval_at_separated {K : Type*} [Field K] [Algebra K ℂ]
    {n : ℕ} (p : Polynomial K) (z : Fin n → ℂ)
    (hz : ∀ i, z i ≠ 0)
    (hsep : ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → 16 * ‖z i‖ ≤ ‖z j‖)
    (hp : p.support.card ≤ n) (heval : ∀ i, Polynomial.aeval (z i) p = 0) :
    p = 0 := by
  have hinj : Function.Injective (algebraMap K ℂ) := (algebraMap K ℂ).injective
  apply (Polynomial.map_eq_zero_iff hinj).mp
  apply eq_zero_of_small_support_eval_at_separated _ z hz hsep
  · simpa only [Polynomial.support_map_of_injective p hinj] using hp
  · intro i
    simpa only [Polynomial.eval_map_algebraMap] using heval i

/-- An element with `n` nonzero images of separated moduli under coefficient-field
algebra homomorphisms has no nonzero annihilator with at most `n` terms. -/
theorem eq_zero_of_small_support_aeval_of_separated_algHoms
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra K ℂ]
    {n : ℕ} (p : Polynomial K) (x : L) (σ : Fin n → L →ₐ[K] ℂ)
    (hx : x ≠ 0)
    (hsep : ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → 16 * ‖σ i x‖ ≤ ‖σ j x‖)
    (hp : p.support.card ≤ n) (heval : Polynomial.aeval x p = 0) :
    p = 0 := by
  refine eq_zero_of_small_support_aeval_at_separated p (fun i => σ i x)
    (fun i => (map_ne_zero_iff (σ i) (σ i).injective).mpr hx) hsep hp ?_
  intro i
  rw [Polynomial.aeval_algHom_apply, heval, map_zero]

/-- Separated conjugate images rule out every annihilator with at most `n` terms. -/
theorem not_hasSparseAnnihilator_of_separated_algHoms
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra K ℂ]
    {n : ℕ} (x : L) (σ : Fin n → L →ₐ[K] ℂ) (hx : x ≠ 0)
    (hsep : ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → 16 * ‖σ i x‖ ≤ ‖σ j x‖) :
    ¬ HasSparseAnnihilator K x n := by
  rintro ⟨p, hp, hsize, heval⟩
  exact hp (eq_zero_of_small_support_aeval_of_separated_algHoms p x σ hx hsep hsize heval)

/-- If a full degree's worth of conjugate images is separated, the minimum
support attains the minimal-polynomial upper bound. -/
theorem minimumSupport_eq_natDegree_add_one_of_separated_algHoms
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra K ℂ]
    {x : L} (hx : IsIntegral K x) (hzero : x ≠ 0)
    (σ : Fin (minpoly K x).natDegree → L →ₐ[K] ℂ)
    (hsep : ∀ i j : Fin (minpoly K x).natDegree, (i : ℕ) + 1 = (j : ℕ) → 16 * ‖σ i x‖ ≤ ‖σ j x‖) :
    minimumSupport hx = (minpoly K x).natDegree + 1 :=
  (minimumSupport_eq_natDegree_add_one_iff hx).2
    ((not_hasSparseAnnihilator_iff x _).1
      (not_hasSparseAnnihilator_of_separated_algHoms x σ hzero hsep))

end GRHArticle.SingularModuli

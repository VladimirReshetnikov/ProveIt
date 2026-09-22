import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Lagrange

/-!
# Classical Prony uniqueness

This file proves `prop:prony` and the orthogonality relations `eq:orthog` of
`docs/surcomplex/prony-reconstruction-at-surreal-scales/article.tex` over an
arbitrary field, which includes the complex Hahn fields and actual surcomplex
workspaces used there.

For nodes `a` and weights `w`, the power moments are `m_r = ∑ w_i a_i^r`. The
Hankel matrix `(m_{r+s})` factors as `Vᵀ diag(w) V` with `V` the Vandermonde
matrix, so its determinant is `(∏ w_i) (∏_{i<j} (a_j - a_i))²`. It is nonzero
for a regular configuration, meaning distinct nodes and nonzero weights.

The monic node polynomial `P = ∏ (X - a_i)` is orthogonal to every
polynomial, so its lower coefficients solve the Hankel system
`H p = -(m_n, …, m_{2n-1})`. Hence any `n`-node configuration, with no
distinctness or nonvanishing assumption, having the same first `2n` moments as a
regular one has the same node polynomial. It is a permutation of the regular
configuration, nodes and weights alike. No configuration with fewer than `n`
nodes reproduces the first `2n - 1` moments, since the Hankel matrix would
factor through a smaller space.
-/

namespace Surreal.Prony

open Matrix Polynomial Finset

noncomputable section

variable {K : Type*} [Field K] {n k : ℕ}

/-- Power moments `m_r = ∑ w_i a_i^r` of a weighted node configuration. -/
def moment (a w : Fin k → K) (r : ℕ) : K :=
  ∑ i, w i * a i ^ r

/-- The Hankel matrix `(m_{r+s})_{0 ≤ r,s < n}` of a moment sequence. -/
def hankel (n : ℕ) (m : ℕ → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun r s => m (r + s)

/-- The rectangular power matrix `(a_i^r)` with `k` nodes and `n` exponents. -/
def powerMatrix (n : ℕ) (a : Fin k → K) : Matrix (Fin k) (Fin n) K :=
  Matrix.of fun i r => a i ^ (r : ℕ)

/-- The Hankel matrix of any finite configuration factors through its nodes. -/
theorem hankel_moment_eq (a w : Fin k → K) :
    hankel n (moment a w) = (powerMatrix n a)ᵀ * diagonal w * powerMatrix n a := by
  ext r s
  rw [mul_apply]
  simp only [mul_diagonal, transpose_apply, hankel, moment, powerMatrix, of_apply, pow_add]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `eq:hankel`: `H = V diag(w) Vᵀ`, written with Mathlib's row-indexed Vandermonde
matrix. -/
theorem hankel_moment (a w : Fin n → K) :
    hankel n (moment a w) = (vandermonde a)ᵀ * diagonal w * vandermonde a :=
  hankel_moment_eq a w

/-- `eq:hankel`: the determinant formula. -/
theorem det_hankel_moment (a w : Fin n → K) :
    (hankel n (moment a w)).det =
      (∏ i, w i) * (∏ i : Fin n, ∏ j ∈ Ioi i, (a j - a i)) ^ 2 := by
  rw [hankel_moment, det_mul, det_mul, det_transpose, det_diagonal, det_vandermonde]
  ring

/-- A regular configuration has an invertible Hankel matrix. -/
theorem det_hankel_moment_ne_zero {a w : Fin n → K} (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) : (hankel n (moment a w)).det ≠ 0 := by
  rw [hankel_moment, det_mul, det_mul, det_transpose, det_diagonal]
  have hv := det_vandermonde_ne_zero_iff.mpr ha
  exact mul_ne_zero (mul_ne_zero hv (prod_ne_zero_iff.mpr fun i _ => hw i)) hv

/-- The moment functional evaluates any polynomial by the weighted node sum. -/
def momentFunctional (a w : Fin k → K) (f : K[X]) : K :=
  ∑ i, w i * f.eval (a i)

/-- The moment functional is determined by the moments through coefficients. -/
theorem momentFunctional_eq_sum_coeff (a w : Fin k → K) (f : K[X]) {N : ℕ}
    (hN : f.natDegree < N) :
    momentFunctional a w f = ∑ j ∈ range N, f.coeff j * moment a w j := by
  simp only [momentFunctional, moment, eval_eq_sum_range' hN, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The monic node polynomial `P = ∏ (X - a_i)`. -/
def nodePoly (a : Fin k → K) : K[X] :=
  ∏ i, (X - C (a i))

theorem nodePoly_monic (a : Fin k → K) : (nodePoly a).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (a i)

theorem natDegree_nodePoly (a : Fin k → K) : (nodePoly a).natDegree = k := by
  rw [nodePoly, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (a i)]
  simp

theorem coeff_nodePoly_self (a : Fin k → K) : (nodePoly a).coeff k = 1 := by
  simpa [natDegree_nodePoly] using (nodePoly_monic a).coeff_natDegree

theorem eval_nodePoly_eq_zero_iff (a : Fin k → K) (x : K) :
    (nodePoly a).eval x = 0 ↔ x ∈ Set.range a := by
  rw [nodePoly, eval_prod, prod_eq_zero_iff]
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero, mem_univ, true_and, Set.mem_range]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

/-- `eq:orthog`: the node polynomial annihilates every polynomial multiple. -/
theorem momentFunctional_nodePoly_mul (a w : Fin k → K) (q : K[X]) :
    momentFunctional a w (nodePoly a * q) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [eval_mul, (eval_nodePoly_eq_zero_iff a _).mpr ⟨i, rfl⟩, zero_mul, mul_zero]

/-- The cofactor `Q_i = P / (X - a_i)`. -/
def cofactor (a : Fin k → K) (i : Fin k) : K[X] :=
  ∏ j ∈ univ.erase i, (X - C (a j))

theorem nodePoly_eq_mul_cofactor (a : Fin k → K) (i : Fin k) :
    nodePoly a = (X - C (a i)) * cofactor a i := by
  rw [nodePoly, cofactor, ← Finset.mul_prod_erase univ (fun j => X - C (a j)) (mem_univ i)]

theorem eval_cofactor_of_ne (a : Fin k → K) {i l : Fin k} (hil : l ≠ i) :
    (cofactor a i).eval (a l) = 0 := by
  rw [cofactor, eval_prod]
  exact prod_eq_zero (mem_erase.mpr ⟨hil, mem_univ l⟩) (by simp)

/-- `eq:orthog`: the cofactors are orthogonal, with diagonal values
`c_i = w_i p_i²`, where `p_i = Q_i(a_i)`. -/
theorem momentFunctional_cofactor_mul (a w : Fin k → K) (i j : Fin k) :
    momentFunctional a w (cofactor a i * cofactor a j) =
      if i = j then w i * (cofactor a i).eval (a i) ^ 2 else 0 := by
  rw [momentFunctional, Finset.sum_eq_single i]
  · split_ifs with hij
    · subst hij
      simp only [eval_mul]
      ring
    · rw [eval_mul, eval_cofactor_of_ne a hij, mul_zero, mul_zero]
  · intro l _ hli
    rw [eval_mul, eval_cofactor_of_ne a hli, zero_mul, mul_zero]
  · simp

/-- The lower coefficients `(P_0, …, P_{n-1})` of the node polynomial. -/
def lowCoeffs (a : Fin n → K) : Fin n → K :=
  fun j => (nodePoly a).coeff j

/-- The node polynomial's lower coefficients solve the Hankel system of the
proof of `prop:prony`. -/
theorem hankel_mulVec_lowCoeffs (a w : Fin n → K) :
    hankel n (moment a w) *ᵥ lowCoeffs a = fun r : Fin n => -moment a w (n + r) := by
  funext r
  have h := momentFunctional_nodePoly_mul a w (X ^ (r : ℕ))
  rw [momentFunctional_eq_sum_coeff a w _ (N := n + r + 1)
    (by rw [natDegree_mul_X_pow _ (nodePoly_monic a).ne_zero, natDegree_nodePoly]; omega)] at h
  simp only [coeff_mul_X_pow'] at h
  rw [Finset.sum_range_succ, if_pos (by omega), Nat.add_sub_cancel, coeff_nodePoly_self,
    one_mul] at h
  -- Discard the vanishing terms below `r` and shift the remaining indices.
  have hsum : ∑ x ∈ range (n + r), (if r ≤ x then (nodePoly a).coeff (x - r) else 0) *
      moment a w x = ∑ j : Fin n, (nodePoly a).coeff j * moment a w (r + j) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le r) (by omega :
      r ≤ n + r)]
    rw [Finset.sum_eq_zero fun x hx => by
      rw [if_neg (by simp only [Finset.mem_Ico] at hx; omega), zero_mul], zero_add]
    rw [Finset.sum_Ico_eq_sum_range, add_tsub_cancel_right, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by
      rw [if_pos (by omega), Nat.add_sub_cancel_left]
  rw [hsum] at h
  simp only [mulVec, dotProduct, hankel, of_apply, lowCoeffs]
  rw [eq_neg_iff_add_eq_zero, ← h]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- `prop:prony`, annihilator step: any `n`-node configuration whose first `2n`
moments agree with those of a regular one has the same node polynomial. -/
theorem nodePoly_eq_of_moment_eq {a w b u : Fin n → K} (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (hm : ∀ r < 2 * n, moment a w r = moment b u r) :
    nodePoly a = nodePoly b := by
  have hH : hankel n (moment a w) = hankel n (moment b u) := by
    ext r s
    exact hm _ (by omega)
  have hlow : lowCoeffs a = lowCoeffs b := by
    have h1 := hankel_mulVec_lowCoeffs a w
    have h2 := hankel_mulVec_lowCoeffs b u
    rw [← hH] at h2
    have htail : (fun r : Fin n => -moment a w (n + r)) =
        fun r : Fin n => -moment b u (n + r) := by
      funext r
      rw [hm _ (by omega)]
    have hzero : hankel n (moment a w) *ᵥ (lowCoeffs a - lowCoeffs b) = 0 := by
      rw [mulVec_sub, h1, h2, htail, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_mulVec_eq_zero (det_hankel_moment_ne_zero ha hw) hzero)
  ext j
  rcases lt_trichotomy j n with hj | rfl | hj
  · exact congrFun hlow ⟨j, hj⟩
  · rw [coeff_nodePoly_self, coeff_nodePoly_self]
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_nodePoly]),
      coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_nodePoly])]

/-- `prop:prony`: a regular `n`-node realization of the first `2n` moments is
unique up to permutation. The competing configuration is not assumed regular. -/
theorem exists_perm_of_moment_eq {a w b u : Fin n → K} (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (hm : ∀ r < 2 * n, moment a w r = moment b u r) :
    ∃ σ : Equiv.Perm (Fin n), b = a ∘ σ ∧ u = w ∘ σ := by
  classical
  have hP := nodePoly_eq_of_moment_eq ha hw hm
  have hrange : Set.range a = Set.range b := by
    ext x
    rw [← eval_nodePoly_eq_zero_iff, ← eval_nodePoly_eq_zero_iff, hP]
  -- Equal node sets force the competing nodes to be distinct.
  have hb : Function.Injective b := by
    have himage : univ.image b = univ.image a := by
      apply Finset.coe_injective
      simp only [coe_image, coe_univ, Set.image_univ, hrange]
    have hcard : (univ.image b).card = (univ : Finset (Fin n)).card := by
      rw [himage, card_image_of_injective _ ha]
    exact fun x y hxy => (card_image_iff.mp hcard) (mem_coe.mpr (mem_univ x))
      (mem_coe.mpr (mem_univ y)) hxy
  have hex : ∀ j, ∃ i, a i = b j := fun j => by
    have : b j ∈ Set.range a := hrange ▸ ⟨j, rfl⟩
    exact this
  choose f hf using hex
  have hfinj : Function.Injective f := fun x y hxy => hb (by rw [← hf x, ← hf y, hxy])
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  have hbσ : b = a ∘ σ := funext fun j => (hf j).symm
  refine ⟨σ, hbσ, ?_⟩
  -- The first `n` moments then determine the weights through the Vandermonde matrix.
  have hvec : (w - u ∘ σ.symm) ᵥ* vandermonde a = 0 := by
    funext r
    have hr := hm r (by omega)
    simp only [moment, hbσ, Function.comp_apply] at hr
    have hre : ∑ x, u x * a (σ x) ^ (r : ℕ) = ∑ i, u (σ.symm i) * a i ^ (r : ℕ) := by
      rw [← Equiv.sum_comp σ (fun i => u (σ.symm i) * a i ^ (r : ℕ))]
      simp
    rw [hre] at hr
    simp only [vecMul, dotProduct, vandermonde_apply, Pi.sub_apply, Function.comp_apply,
      Pi.zero_apply, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    simpa only [mul_comm] using hr
  have hwu := sub_eq_zero.mp (eq_zero_of_vecMul_eq_zero (det_vandermonde_ne_zero_iff.mpr ha) hvec)
  funext j
  have := congrFun hwu (σ j)
  simpa using this.symm

/-- `prop:prony`: a regular `n`-node moment vector has no realization with fewer
than `n` nodes, even using only its first `2n - 1` moments. -/
theorem not_moment_eq_of_lt {a w : Fin n → K} (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0)
    {k : ℕ} (hk : k < n) (b u : Fin k → K) :
    ¬ ∀ r < 2 * n - 1, moment a w r = moment b u r := by
  classical
  intro hm
  have hH : hankel n (moment a w) = (powerMatrix n b)ᵀ * diagonal u * powerMatrix n b := by
    rw [← hankel_moment_eq]
    ext r s
    exact hm _ (by omega)
  have hunit : IsUnit (hankel n (moment a w)) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_hankel_moment_ne_zero ha hw))
  have hrank := rank_of_isUnit _ hunit
  rw [Fintype.card_fin] at hrank
  have hle : (hankel n (moment a w)).rank ≤ k := by
    rw [hH]
    exact (rank_mul_le_left _ _).trans ((rank_mul_le_left _ _).trans (rank_le_width _))
  omega

end

end Surreal.Prony

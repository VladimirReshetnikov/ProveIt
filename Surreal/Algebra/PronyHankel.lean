import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.LinearCombination

/-!
# Classical Prony uniqueness

This file proves `prony:prop:prony` and the orthogonality relations `prony:eq:orthog` of
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

/-- `prony:eq:hankel`: `H = V diag(w) Vᵀ`, written with Mathlib's row-indexed Vandermonde
matrix. -/
theorem hankel_moment (a w : Fin n → K) :
    hankel n (moment a w) = (vandermonde a)ᵀ * diagonal w * vandermonde a :=
  hankel_moment_eq a w

/-- `prony:eq:hankel`: the determinant formula. -/
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

/-- `prony:eq:orthog`: the node polynomial annihilates every polynomial multiple. -/
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

/-- `prony:eq:orthog`: the cofactors are orthogonal, with diagonal values
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

theorem eval_cofactor_ne_zero (a : Fin k → K) {i : Fin k} {x : K} (hx : ∀ j ≠ i, x ≠ a j) :
    (cofactor a i).eval x ≠ 0 := by
  rw [cofactor, eval_prod]
  exact prod_ne_zero_iff.mpr fun j hj => by
    simpa [sub_eq_zero] using hx j (mem_erase.mp hj).1

/-- `prony:eq:localeq`: dividing a cofactor-coordinate perturbation `P + ∑ b_j Q_j` by
`Q_i` at a point `x` away from the other nodes gives, with `z = x - a_i`,
`z + b_i + ∑_{j ≠ i} b_j z/(a_i - a_j + z)`. The identity is exact. -/
theorem eval_perturbed_eq (a b : Fin k → K) {i : Fin k} {x : K} (hx : ∀ j ≠ i, x ≠ a j) :
    (nodePoly a + ∑ j, C (b j) * cofactor a j).eval x =
      (cofactor a i).eval x *
        (x - a i + b i + ∑ j ∈ univ.erase i, b j * (x - a i) / (x - a j)) := by
  have hQ : ∀ j ∈ univ.erase i, (cofactor a j).eval x =
      (x - a i) * (cofactor a i).eval x / (x - a j) := by
    intro j hj
    have hxj : x - a j ≠ 0 := sub_ne_zero.mpr (hx j (mem_erase.mp hj).1)
    rw [eq_div_iff hxj]
    have h1 := congrArg (eval x) (nodePoly_eq_mul_cofactor a j)
    have h2 := congrArg (eval x) (nodePoly_eq_mul_cofactor a i)
    simp only [eval_mul, eval_sub, eval_X, eval_C] at h1 h2
    rw [mul_comm, ← h1, h2]
  have hsum : ∑ j ∈ univ.erase i, b j * (cofactor a j).eval x =
      (cofactor a i).eval x * ∑ j ∈ univ.erase i, b j * (x - a i) / (x - a j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hQ j hj]
    ring
  have h2 := congrArg (eval x) (nodePoly_eq_mul_cofactor a i)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at h2
  rw [eval_add, eval_finsetSum, ← Finset.add_sum_erase _ _ (mem_univ i), h2]
  simp only [eval_mul, eval_C]
  rw [hsum]
  ring

/-- `prony:eq:localeq`: a root of the perturbation away from the other nodes satisfies
the local equation. -/
theorem local_root_equation (a b : Fin k → K) {i : Fin k} {x : K} (hx : ∀ j ≠ i, x ≠ a j)
    (hroot : (nodePoly a + ∑ j, C (b j) * cofactor a j).eval x = 0) :
    x - a i + b i + ∑ j ∈ univ.erase i, b j * (x - a i) / (x - a j) = 0 := by
  rw [eval_perturbed_eq a b hx] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left (eval_cofactor_ne_zero a hx)

/-- `prony:eq:rootexact`, multiplied out: `z(1 + ∑_{j ≠ i} b_j/(a_i - a_j + z)) = -b_i`. -/
theorem local_root_mul (a b : Fin k → K) {i : Fin k} {x : K} (hx : ∀ j ≠ i, x ≠ a j)
    (hroot : (nodePoly a + ∑ j, C (b j) * cofactor a j).eval x = 0) :
    (x - a i) * (1 + ∑ j ∈ univ.erase i, b j / (x - a j)) = -b i := by
  have h := local_root_equation a b hx hroot
  have hs : ∑ j ∈ univ.erase i, b j * (x - a i) / (x - a j) =
      (x - a i) * ∑ j ∈ univ.erase i, b j / (x - a j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs] at h
  linear_combination h

/-- `prony:eq:rootexact`: the node displacement is `-b_i(1 + ∑_{j ≠ i} b_j/(a_i - a_j + z))⁻¹`
whenever the bracket is nonzero, as it is when all its summands are infinitesimal. -/
theorem local_root_exact (a b : Fin k → K) {i : Fin k} {x : K} (hx : ∀ j ≠ i, x ≠ a j)
    (hroot : (nodePoly a + ∑ j, C (b j) * cofactor a j).eval x = 0)
    (hbr : 1 + ∑ j ∈ univ.erase i, b j / (x - a j) ≠ 0) :
    x - a i = -b i * (1 + ∑ j ∈ univ.erase i, b j / (x - a j))⁻¹ := by
  rw [← local_root_mul a b hx hroot, mul_assoc, mul_inv_cancel₀ hbr, mul_one]

/-- The lower coefficients `(P_0, …, P_{n-1})` of the node polynomial. -/
def lowCoeffs (a : Fin n → K) : Fin n → K :=
  fun j => (nodePoly a).coeff j

/-- The node polynomial's lower coefficients solve the Hankel system of the
proof of `prony:prop:prony`. -/
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

/-- `prony:prop:prony`, annihilator step: any `n`-node configuration whose first `2n`
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

/-- `prony:prop:prony`: a regular `n`-node realization of the first `2n` moments is
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

/-- `prony:prop:prony`: a regular `n`-node moment vector has no realization with fewer
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

section LastMoment

/-- The linear moment functional `f ↦ ∑ f_j m_j` of an arbitrary moment sequence. -/
def momentLinear (m : ℕ → K) : K[X] →ₗ[K] K :=
  Polynomial.lsum fun j => LinearMap.mulRight K (m j)

theorem momentLinear_eq_sum (m : ℕ → K) (f : K[X]) {N : ℕ} (hN : f.natDegree < N) :
    momentLinear m f = ∑ j ∈ range N, f.coeff j * m j := by
  rw [momentLinear, Polynomial.lsum_apply, sum_over_range' f (by simp) N hN]
  rfl

theorem momentLinear_C_mul_X_pow (m : ℕ → K) (c : K) (r : ℕ) :
    momentLinear m (C c * X ^ r) = c * m r := by
  rw [momentLinear, Polynomial.lsum_apply, C_mul_X_pow_eq_monomial,
    sum_monomial_index _ _ (by simp)]
  rfl

theorem momentLinear_moment (a w : Fin k → K) (f : K[X]) :
    momentLinear (moment a w) f = momentFunctional a w f := by
  rw [momentLinear_eq_sum _ _ (Nat.lt_succ_self _),
    momentFunctional_eq_sum_coeff _ _ _ (Nat.lt_succ_self _)]

/-- Multiplying by `X^r` shifts the moment indices. -/
theorem momentLinear_mul_X_pow (m : ℕ → K) {P : K[X]} {d : ℕ} (hP : P.natDegree ≤ d) (r : ℕ) :
    momentLinear m (P * X ^ r) = ∑ j ∈ range (d + 1), P.coeff j * m (j + r) := by
  conv_lhs => rw [P.as_sum_range' (d + 1) (by omega)]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, ← pow_add, momentLinear_C_mul_X_pow]

/-- A monic degree-`n` annihilator of `1, X, …, X^{n-1}` solves the Hankel system. -/
theorem hankel_mulVec_of_annihilates (m : ℕ → K) {P : K[X]} (hPm : P.Monic)
    (hPd : P.natDegree = n) (hann : ∀ r < n, momentLinear m (P * X ^ r) = 0) :
    hankel n m *ᵥ (fun j : Fin n => P.coeff j) = fun r : Fin n => -m (n + r) := by
  funext r
  have h := hann r r.2
  have hn1 : P.coeff n = 1 := by
    rw [← hPd]
    exact hPm.coeff_natDegree
  rw [momentLinear_mul_X_pow m hPd.le, Finset.sum_range_succ, hn1, one_mul,
    ← Fin.sum_univ_eq_sum_range (fun j => P.coeff j * m (j + r))] at h
  simp only [mulVec, dotProduct, hankel, of_apply]
  rw [eq_neg_iff_add_eq_zero, ← h]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm, add_comm (r : ℕ)]

/-- Uniqueness of the monic annihilator when the Hankel matrix is invertible. -/
theorem monic_annihilator_unique (m : ℕ → K) (hH : (hankel n m).det ≠ 0) {P Q : K[X]}
    (hPm : P.Monic) (hPd : P.natDegree = n) (hPann : ∀ r < n, momentLinear m (P * X ^ r) = 0)
    (hQm : Q.Monic) (hQd : Q.natDegree = n)
    (hQann : ∀ r < n, momentLinear m (Q * X ^ r) = 0) : P = Q := by
  have hzero : hankel n m *ᵥ ((fun j : Fin n => P.coeff j) - fun j : Fin n => Q.coeff j) = 0 := by
    rw [mulVec_sub, hankel_mulVec_of_annihilates m hPm hPd hPann,
      hankel_mulVec_of_annihilates m hQm hQd hQann, sub_self]
  have hlow := sub_eq_zero.mp (eq_zero_of_mulVec_eq_zero hH hzero)
  ext j
  rcases lt_trichotomy j n with hj | rfl | hj
  · exact congrFun hlow ⟨j, hj⟩
  · rw [← hPd, hPm.coeff_natDegree, ← hQd.trans hPd.symm, hQm.coeff_natDegree]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

/-- The moments with only `m_{2n-1}` perturbed by `e`. -/
def lastPerturbed (a w : Fin n → K) (e : K) (r : ℕ) : K :=
  moment a w r + if r = 2 * n - 1 then e else 0

/-- The original Hankel matrix is unchanged by the last-moment perturbation. -/
theorem hankel_lastPerturbed (a w : Fin n → K) (e : K) :
    hankel n (lastPerturbed a w e) = hankel n (moment a w) := by
  ext r s
  simp only [hankel, of_apply, lastPerturbed]
  rw [if_neg (by omega), add_zero]

theorem momentLinear_lastPerturbed (a w : Fin n → K) (e : K) (f : K[X]) :
    momentLinear (lastPerturbed a w e) f =
      momentFunctional a w f + e * f.coeff (2 * n - 1) := by
  have hN : f.natDegree < f.natDegree + 2 * n + 1 := by omega
  rw [momentLinear_eq_sum _ _ hN, ← momentLinear_moment, momentLinear_eq_sum _ _ hN]
  simp only [lastPerturbed, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', mem_range]
  rw [if_pos (by omega)]
  ring

/-- `prony:eq:Pe`: `P_e = P - e ∑ Q_i/(w_i P'(a_i)²)`, written with `P'(a_i) = Q_i(a_i)`. -/
def lastMomentPoly (a w : Fin n → K) (e : K) : K[X] :=
  nodePoly a - ∑ i, C (e / (w i * (cofactor a i).eval (a i) ^ 2)) * cofactor a i

theorem natDegree_cofactor (a : Fin n → K) (i : Fin n) :
    (cofactor a i).natDegree = n - 1 := by
  rw [cofactor, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C (a j)]
  simp [Finset.card_erase_of_mem]

theorem cofactor_monic (a : Fin n → K) (i : Fin n) : (cofactor a i).Monic :=
  monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (a j)

theorem natDegree_lastMomentCorrection_le (a w : Fin n → K) (e : K) :
    (∑ i, C (e / (w i * (cofactor a i).eval (a i) ^ 2)) * cofactor a i).natDegree ≤ n - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (natDegree_C_mul_le _ _).trans (natDegree_cofactor a i).le

theorem lastMomentPoly_monic (a w : Fin n → K) (e : K) (hn : 0 < n) :
    (lastMomentPoly a w e).Monic := by
  refine (nodePoly_monic a).sub_of_left ?_
  refine (degree_le_natDegree.trans (WithBot.coe_le_coe.mpr
    (natDegree_lastMomentCorrection_le a w e))).trans_lt ?_
  rw [degree_eq_natDegree (nodePoly_monic a).ne_zero, natDegree_nodePoly]
  exact WithBot.coe_lt_coe.mpr (Nat.sub_lt hn one_pos)

theorem natDegree_lastMomentPoly (a w : Fin n → K) (e : K) (hn : 0 < n) :
    (lastMomentPoly a w e).natDegree = n := by
  rw [lastMomentPoly, natDegree_sub_eq_left_of_natDegree_lt, natDegree_nodePoly]
  rw [natDegree_nodePoly]
  exact (natDegree_lastMomentCorrection_le a w e).trans_lt (by omega)

/-- The node values of the perturbed annihilator: `P_e(a_j) = -e/(w_j p_j)`. -/
theorem eval_lastMomentPoly (a w : Fin n → K) (e : K) (j : Fin n) :
    (lastMomentPoly a w e).eval (a j) =
      -(e / (w j * (cofactor a j).eval (a j) ^ 2) * (cofactor a j).eval (a j)) := by
  rw [lastMomentPoly, eval_sub, (eval_nodePoly_eq_zero_iff a _).mpr ⟨j, rfl⟩, zero_sub,
    eval_finsetSum, Finset.sum_eq_single j]
  · simp only [eval_mul, eval_C]
  · intro i _ hij
    rw [eval_mul, eval_cofactor_of_ne a (Ne.symm hij), mul_zero]
  · simp

theorem eval_cofactor_self_ne_zero {a : Fin n → K} (ha : Function.Injective a) (j : Fin n) :
    (cofactor a j).eval (a j) ≠ 0 :=
  eval_cofactor_ne_zero a fun _ hij h => hij (ha h).symm

/-- The test against a cofactor: the node part contributes `-e`. -/
theorem momentFunctional_lastMomentPoly_mul_cofactor {a w : Fin n → K}
    (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0) (e : K) (j : Fin n) :
    momentFunctional a w (lastMomentPoly a w e * cofactor a j) = -e := by
  rw [momentFunctional, Finset.sum_eq_single j]
  · rw [eval_mul, eval_lastMomentPoly]
    have hp := eval_cofactor_self_ne_zero ha j
    have hwj := hw j
    set p := (cofactor a j).eval (a j)
    have hden : w j * p ^ 2 ≠ 0 := mul_ne_zero hwj (pow_ne_zero 2 hp)
    calc w j * (-(e / (w j * p ^ 2) * p) * p) = -(e / (w j * p ^ 2) * (w j * p ^ 2)) := by
          ring
      _ = -e := by rw [div_mul_cancel₀ e hden]
  · intro l _ hlj
    rw [eval_mul, eval_cofactor_of_ne a hlj, mul_zero, mul_zero]
  · simp

/-- The top coefficient of the test against a cofactor is `1`. -/
theorem coeff_lastMomentPoly_mul_cofactor (a w : Fin n → K) (e : K) (j : Fin n) :
    (lastMomentPoly a w e * cofactor a j).coeff (2 * n - 1) = 1 := by
  have hn : 0 < n := Fin.pos j
  have h := coeff_mul_add_eq_of_natDegree_le (natDegree_lastMomentPoly a w e hn).le
    (natDegree_cofactor a j).le
  rw [show n + (n - 1) = 2 * n - 1 by omega] at h
  rw [h]
  have h1 := (lastMomentPoly_monic a w e hn).coeff_natDegree
  have h2 := (cofactor_monic a j).coeff_natDegree
  rw [natDegree_lastMomentPoly a w e hn] at h1
  rw [natDegree_cofactor a j] at h2
  rw [h1, h2, one_mul]

/-- The cofactors divided by their node values are Mathlib's Lagrange basis. -/
theorem lagrange_basis_eq (a : Fin n → K) (j : Fin n) :
    Lagrange.basis Finset.univ a j = C ((cofactor a j).eval (a j))⁻¹ * cofactor a j := by
  rw [Lagrange.basis, cofactor, eval_prod]
  simp only [Lagrange.basisDivisor, Finset.prod_mul_distrib, ← map_prod, eval_sub, eval_X,
    eval_C, Finset.prod_inv_distrib]

/-- `prony:prop:last`: for every `e`, regardless of its valuation, `P_e` annihilates all
polynomials of degree below `n` for the perturbed moment functional. -/
theorem momentLinear_lastMomentPoly_mul {a w : Fin n → K} (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (e : K) {f : K[X]} (hf : f.degree < n) :
    momentLinear (lastPerturbed a w e) (lastMomentPoly a w e * f) = 0 := by
  have hf' : f.degree < (Finset.univ : Finset (Fin n)).card := by simpa using hf
  rw [Lagrange.eq_interpolate (v := a) ha.injOn hf', Lagrange.interpolate_apply,
    Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [lagrange_basis_eq]
  have hsm : lastMomentPoly a w e * (C (f.eval (a j)) *
      (C ((cofactor a j).eval (a j))⁻¹ * cofactor a j)) =
      (f.eval (a j) * ((cofactor a j).eval (a j))⁻¹) • (lastMomentPoly a w e * cofactor a j) := by
    rw [← C_mul', C_mul]
    ring
  rw [hsm, map_smul, momentLinear_lastPerturbed, momentFunctional_lastMomentPoly_mul_cofactor ha hw,
    coeff_lastMomentPoly_mul_cofactor, mul_one, neg_add_cancel, smul_zero]

/-- `prony:prop:last`: `P_e` is the unique monic annihilator of the perturbed moments. -/
theorem lastMomentPoly_unique {a w : Fin n → K} (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (e : K) (hn : 0 < n) {Q : K[X]} (hQm : Q.Monic)
    (hQd : Q.natDegree = n)
    (hQann : ∀ r < n, momentLinear (lastPerturbed a w e) (Q * X ^ r) = 0) :
    Q = lastMomentPoly a w e := by
  refine monic_annihilator_unique _ ?_ hQm hQd hQann (lastMomentPoly_monic a w e hn)
    (natDegree_lastMomentPoly a w e hn) fun r hr => ?_
  · rw [hankel_lastPerturbed]
    exact det_hankel_moment_ne_zero ha hw
  · refine momentLinear_lastMomentPoly_mul ha hw e ?_
    rw [degree_X_pow]
    exact WithBot.coe_lt_coe.mpr hr

end LastMoment

end

end Surreal.Prony

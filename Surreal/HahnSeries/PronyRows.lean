import Surreal.HahnSeries.PronyCofactorBound
import Surreal.HahnSeries.PolynomialGaussValuation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Hermite inverse of the moment differential and exact row losses

This file proves `prony:prop:rows` (exact row losses), with `prony:eq:diff`, `prony:eq:hermite`,
`prony:eq:invdiff`, `prony:eq:cancellation`, `prony:eq:gaussrows` and `prony:eq:marginals`, of
`docs/surcomplex/prony-reconstruction-at-surreal-scales/article.tex`.

## Field part

Over an arbitrary field `K`, let `a` be distinct nodes and `w` nonzero weights. With the
cofactors `Q_i` and `p_i = Q_i(a_i)` of `Surreal.Prony`, put `ℓ_i = Q_i/p_i` (`lagBasis`, which
is Mathlib's Lagrange basis), `χ_i = ∑_{j ≠ i} 1/(a_i - a_j)` (`hermiteChi`),
`H_i = (1 - 2χ_i(X - a_i)) ℓ_i²` (`hermiteH`) and `G_i = (X - a_i) ℓ_i²` (`hermiteG`).

* `eval_derivative_lagBasis_self`: `ℓ_i'(a_i) = χ_i`.
* `natDegree_hermiteH_lt`, `natDegree_hermiteG_lt`, `eval_hermiteH`, `eval_derivative_hermiteH`,
  `eval_hermiteG`, `eval_derivative_hermiteG`: `H_i, G_i` have degree `< 2n`, and
  `H_i(a_j) = δ_ij`, `H_i'(a_j) = 0`, `G_i(a_j) = 0`, `G_i'(a_j) = δ_ij`. `eq_sum_hermite`: they
  are the Hermite interpolation basis, `f = ∑ (f(a_i) H_i + f'(a_i) G_i)` for `deg f < 2n`.
* `momentDiff` is the differential `prony:eq:diff`; `momentDiff_eq_derivative` identifies it as
  the derivative of the moments along `(w + h dw, a + h da)` at `h = 0`, and `momentDiff_zero`
  records the convention at `k = 0`. `momentLinear_momentDiff`:
  `dL(f) = ∑ (f(a_i) dw_i + w_i f'(a_i) da_i)`.
* `prony:eq:invdiff`: `dw_i = dL(H_i)` (`momentLinear_momentDiff_hermiteH`) and
  `da_i = dL(G_i)/w_i` (`eq_momentLinear_momentDiff_hermiteG_div`). The Jacobian
  `J : (dw, da) ↦ (dm_k)_{k < 2n}` (`momentJac`) is invertible (`momentJac_bijective`), and
  `momentDiff_eq_iff` identifies the rows of `J⁻¹`: `(dw, da)` has differential `dm` in degrees
  `< 2n` if and only if `dw_i = dL(H_i)` and `da_i = dL(G_i)/w_i`, with `dL(X^k) = dm_k`.

## Hahn part

Work over `R((t^Γ))`, with `R` any field and `Γ` any linearly ordered abelian group; the source
takes `R = ℝ` or `ℂ`. The nodes are integral and distinct, and the weights are nonzero.
`gaussVal` is the Gauss valuation `v_G(f) = min_k v([X^k] f)` (`gaussVal_eq_inf`), an additive
valuation, hence multiplicative (`gaussVal_mul`). `sepSum a i` is `d_i = ∑_{j ≠ i} d_ij` with
`d_ij = v(a_i - a_j)` (`prony:eq:geometry`). `sepMax a i` is `max(0, max_{j ≠ i} d_ij)`, folded
from `0`: for integral distinct nodes and `n ≥ 2` it is the source's `δ_i = max_{j ≠ i} d_ij`
(`sepMax_eq_sup'`), and for `n = 1` it is the source's convention `δ_i = 0` (`sepMax_fin_one`).
`cancelDepth a i` is `q_i` of `prony:eq:cancellation` and `nodeLoss a w i` is
`E_i = v(w_i) + 2 d_i` (from `Surreal.PronyBound`).

* `cancelDepth_le_sepMax` (`prony:eq:cancellation`): `0 ≤ q_i ≤ δ_i`, with `δ_i` read as
  `sepMax a i`; in this form no integrality is needed.
* `gaussVal_hermiteG`, `gaussVal_hermiteH` (`prony:eq:gaussrows`): `v_G(G_i) = -2 d_i` and
  `v_G(H_i) = -2 d_i - q_i`. The second one assumes `(2 : R) ≠ 0`, which the source uses as
  `v(2) = 0`. It can fail in characteristic `2`, where `H_i = ℓ_i²`, so `v_G(H_i) = -2 d_i` even
  when `q_i > 0` (for example `n = 2` and `a_1 - a_2 = t^γ` with `γ > 0`, where `q_1 = γ`).
* `exists_momentLinear_eq_iff`: the image of the ball `t^κ O^N` under the row
  `dm ↦ ∑_k f_k dm_k` is exactly the fractional ideal `t^(κ + v_G(f)) O`.
* `image_node_tangentLattice`, `image_weight_tangentLattice` (`prony:eq:marginals`): the
  coordinate projections of the tangent precision lattice `J⁻¹ t^κ O^{2n}` (`tangentLattice`,
  see `tangentLattice_eq_image_symm`) are the whole fractional ideals `da_i ∈ t^(κ - E_i) O` and
  `dw_i ∈ t^(κ - 2d_i - q_i) O`. `exact_row_losses` bundles `prony:prop:rows`.

Nothing in `prony:prop:rows` remains pending. The finite coefficient criterion
`prony:prop:lattice` and the nonlinear uncertainty set `prony:cor:nonlinear` are not formalized
here.
-/

namespace Surreal.PronyRows

open Polynomial Finset Surreal.Prony Surreal.PronyBound

noncomputable section

section Field

variable {K : Type*} [Field K] {n : ℕ}

/-- `prony:eq:hermite`: the Hermite coefficient `χ_i = ∑_{j ≠ i} 1/(a_i - a_j)`. -/
def hermiteChi (a : Fin n → K) (i : Fin n) : K :=
  ∑ j ∈ univ.erase i, (a i - a j)⁻¹

/-- `prony:eq:hermite`: the Lagrange basis polynomial `ℓ_i = Q_i/p_i`, with `p_i = Q_i(a_i)`. -/
def lagBasis (a : Fin n → K) (i : Fin n) : K[X] :=
  C ((cofactor a i).eval (a i))⁻¹ * cofactor a i

/-- `prony:eq:hermite`: `H_i = (1 - 2χ_i (X - a_i)) ℓ_i²`. -/
def hermiteH (a : Fin n → K) (i : Fin n) : K[X] :=
  (1 - C (2 * hermiteChi a i) * (X - C (a i))) * lagBasis a i ^ 2

/-- `prony:eq:hermite`: `G_i = (X - a_i) ℓ_i²`. -/
def hermiteG (a : Fin n → K) (i : Fin n) : K[X] :=
  (X - C (a i)) * lagBasis a i ^ 2

theorem eval_cofactor_self (a : Fin n → K) (i : Fin n) :
    (cofactor a i).eval (a i) = ∏ j ∈ univ.erase i, (a i - a j) := by
  rw [cofactor, eval_prod]
  simp only [eval_sub, eval_X, eval_C]

theorem lagBasis_eq_lagrange_basis (a : Fin n → K) (i : Fin n) :
    lagBasis a i = Lagrange.basis univ a i :=
  (lagrange_basis_eq a i).symm

variable {a : Fin n → K}

theorem eval_lagBasis_self (ha : Function.Injective a) (i : Fin n) :
    (lagBasis a i).eval (a i) = 1 := by
  rw [lagBasis, eval_mul, eval_C, inv_mul_cancel₀ (eval_cofactor_self_ne_zero ha i)]

theorem eval_lagBasis_of_ne (a : Fin n → K) {i j : Fin n} (hji : j ≠ i) :
    (lagBasis a i).eval (a j) = 0 := by
  rw [lagBasis, eval_mul, eval_cofactor_of_ne a hji, mul_zero]

/-- The logarithmic derivative of the cofactor at its own node: `Q_i'(a_i) = p_i χ_i`. -/
theorem eval_derivative_cofactor_self (ha : Function.Injective a) (i : Fin n) :
    (derivative (cofactor a i)).eval (a i) = (cofactor a i).eval (a i) * hermiteChi a i := by
  rw [eval_cofactor_self, cofactor, derivative_prod_finset, eval_finsetSum, hermiteChi,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : a i - a k ≠ 0 := sub_ne_zero.mpr (ha.ne (Finset.ne_of_mem_erase hk).symm)
  simp only [derivative_X_sub_C, mul_one, eval_prod, eval_sub, eval_X, eval_C]
  rw [← Finset.prod_erase_mul _ _ hk, mul_assoc, mul_inv_cancel₀ hk', mul_one]

/-- `prony:eq:hermite`: `χ_i = ℓ_i'(a_i)`. -/
theorem eval_derivative_lagBasis_self (ha : Function.Injective a) (i : Fin n) :
    (derivative (lagBasis a i)).eval (a i) = hermiteChi a i := by
  rw [lagBasis, derivative_C_mul, eval_mul, eval_C, eval_derivative_cofactor_self ha, ← mul_assoc,
    inv_mul_cancel₀ (eval_cofactor_self_ne_zero ha i), one_mul]

/-- `prony:eq:hermite`: `H_i(a_j) = δ_ij`. -/
theorem eval_hermiteH (ha : Function.Injective a) (i j : Fin n) :
    (hermiteH a i).eval (a j) = if j = i then 1 else 0 := by
  rw [hermiteH, eval_mul, eval_pow]
  split_ifs with hji
  · subst hji
    rw [eval_lagBasis_self ha]
    simp
  · rw [eval_lagBasis_of_ne a hji]
    simp

/-- `prony:eq:hermite`: `H_i'(a_j) = 0`. -/
theorem eval_derivative_hermiteH (ha : Function.Injective a) (i j : Fin n) :
    (derivative (hermiteH a i)).eval (a j) = 0 := by
  simp only [hermiteH, derivative_mul, derivative_sub, derivative_one, derivative_C,
    derivative_X, derivative_sq, eval_add, eval_mul, eval_sub, eval_one, eval_C, eval_X,
    eval_pow, eval_neg, eval_zero, zero_mul, zero_add, zero_sub]
  by_cases hji : j = i
  · subst hji
    rw [eval_lagBasis_self ha, eval_derivative_lagBasis_self ha]
    ring
  · rw [eval_lagBasis_of_ne a hji]
    ring

/-- `prony:eq:hermite`: `G_i(a_j) = 0`. -/
theorem eval_hermiteG (a : Fin n → K) (i j : Fin n) : (hermiteG a i).eval (a j) = 0 := by
  rw [hermiteG, eval_mul, eval_pow]
  by_cases hji : j = i
  · subst hji
    simp
  · rw [eval_lagBasis_of_ne a hji]
    simp

/-- `prony:eq:hermite`: `G_i'(a_j) = δ_ij`. -/
theorem eval_derivative_hermiteG (ha : Function.Injective a) (i j : Fin n) :
    (derivative (hermiteG a i)).eval (a j) = if j = i then 1 else 0 := by
  simp only [hermiteG, derivative_mul, derivative_sub, derivative_C, derivative_X,
    derivative_sq, eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_pow, sub_zero, one_mul]
  split_ifs with hji
  · subst hji
    rw [eval_lagBasis_self ha]
    ring
  · rw [eval_lagBasis_of_ne a hji]
    ring

theorem natDegree_lagBasis_le (a : Fin n → K) (i : Fin n) :
    (lagBasis a i).natDegree ≤ n - 1 :=
  (natDegree_C_mul_le _ _).trans (natDegree_cofactor a i).le

theorem natDegree_hermiteFactor_le (c x : K) : (1 - C c * (X - C x)).natDegree ≤ 1 :=
  (natDegree_sub_le _ _).trans (max_le (by simp)
    ((natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le x)))

/-- `prony:eq:hermite`: `H_i` has degree `< 2n`. -/
theorem natDegree_hermiteH_lt (a : Fin n → K) (i : Fin n) : (hermiteH a i).natDegree < 2 * n := by
  have hi := i.2
  have h2 : (lagBasis a i ^ 2).natDegree ≤ 2 * (n - 1) :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left 2 (natDegree_lagBasis_le a i))
  calc (hermiteH a i).natDegree ≤ 1 + 2 * (n - 1) :=
        natDegree_mul_le.trans (add_le_add (natDegree_hermiteFactor_le _ _) h2)
    _ < 2 * n := by omega

/-- `prony:eq:hermite`: `G_i` has degree `< 2n`. -/
theorem natDegree_hermiteG_lt (a : Fin n → K) (i : Fin n) : (hermiteG a i).natDegree < 2 * n := by
  have hi := i.2
  have h2 : (lagBasis a i ^ 2).natDegree ≤ 2 * (n - 1) :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left 2 (natDegree_lagBasis_le a i))
  calc (hermiteG a i).natDegree ≤ 1 + 2 * (n - 1) :=
        natDegree_mul_le.trans (add_le_add (natDegree_X_sub_C_le _) h2)
    _ < 2 * n := by omega

theorem hermiteH_ne_zero (ha : Function.Injective a) (i : Fin n) : hermiteH a i ≠ 0 := by
  intro h0
  have h := eval_hermiteH ha i i
  rw [h0, eval_zero, if_pos rfl] at h
  exact zero_ne_one h

theorem hermiteG_ne_zero (ha : Function.Injective a) (i : Fin n) : hermiteG a i ≠ 0 := by
  intro h0
  have h := eval_derivative_hermiteG ha i i
  rw [h0, derivative_zero, eval_zero, if_pos rfl] at h
  exact zero_ne_one h

/-- `prony:eq:diff`: the differential `dm_k = ∑_i (a_i^k dw_i + w_i k a_i^{k-1} da_i)` of the
moment map at `(w, a)` in the direction `(dw, da)`. At `k = 0` the derivative term is `0`. -/
def momentDiff (a w dw da : Fin n → K) (k : ℕ) : K :=
  ∑ i, (a i ^ k * dw i + w i * ((k : K) * a i ^ (k - 1)) * da i)

/-- `prony:eq:diff`: at `k = 0` only the weight increments contribute, including when some
`a_i = 0`. -/
theorem momentDiff_zero (a w dw da : Fin n → K) : momentDiff a w dw da 0 = ∑ i, dw i := by
  simp [momentDiff]

/-- `prony:eq:diff` is the differential of the moment map `m_k = ∑ w_i a_i^k`: it is the
derivative at `h = 0` of the moments of `(w + h dw, a + h da)`. -/
theorem momentDiff_eq_derivative (a w dw da : Fin n → K) (k : ℕ) :
    momentDiff a w dw da k = (derivative (∑ i, (C (w i) + C (dw i) * X) *
      (C (a i) + C (da i) * X) ^ k)).eval 0 := by
  rw [derivative_sum, eval_finsetSum, momentDiff]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [derivative_mul, derivative_add, derivative_C, derivative_X, derivative_pow, eval_add,
    eval_mul, eval_C, eval_X, eval_pow, mul_zero, add_zero, zero_add, mul_one, zero_mul]
  ring

/-- The moment functional of the differential `prony:eq:diff`:
`dL(f) = ∑_i (f(a_i) dw_i + w_i f'(a_i) da_i)`. -/
theorem momentLinear_momentDiff (a w dw da : Fin n → K) (f : K[X]) :
    momentLinear (momentDiff a w dw da) f =
      ∑ i, (f.eval (a i) * dw i + w i * (derivative f).eval (a i) * da i) := by
  have hN : f.natDegree < f.natDegree + 1 := Nat.lt_succ_self _
  rw [momentLinear_eq_sum _ _ hN]
  simp only [momentDiff, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_eq_sum_range' hN, derivative_eval, sum_over_range' f (by simp) _ hN]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The moment functional only reads the moments below the degree bound. -/
theorem momentLinear_congr {m m' : ℕ → K} {f : K[X]} {N : ℕ} (hN : f.natDegree < N)
    (h : ∀ k < N, m k = m' k) : momentLinear m f = momentLinear m' f := by
  rw [momentLinear_eq_sum m f hN, momentLinear_eq_sum m' f hN]
  exact Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_range.mp hk)]

/-- `prony:eq:invdiff`, weight rows: `dw_i = (dL)(H_i)`. -/
theorem momentLinear_momentDiff_hermiteH (ha : Function.Injective a) (w dw da : Fin n → K)
    (i : Fin n) : momentLinear (momentDiff a w dw da) (hermiteH a i) = dw i := by
  rw [momentLinear_momentDiff]
  simp only [eval_hermiteH ha, eval_derivative_hermiteH ha, ite_mul, one_mul, zero_mul, mul_zero,
    add_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `prony:eq:invdiff`, node rows: `(dL)(G_i) = w_i da_i`. -/
theorem momentLinear_momentDiff_hermiteG (ha : Function.Injective a) (w dw da : Fin n → K)
    (i : Fin n) : momentLinear (momentDiff a w dw da) (hermiteG a i) = w i * da i := by
  rw [momentLinear_momentDiff]
  simp only [eval_hermiteG, eval_derivative_hermiteG ha, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, zero_add, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `prony:eq:invdiff`, node rows: `da_i = (dL)(G_i)/w_i`. -/
theorem eq_momentLinear_momentDiff_hermiteG_div (ha : Function.Injective a)
    {w : Fin n → K} (dw da : Fin n → K) {i : Fin n} (hw : w i ≠ 0) :
    da i = momentLinear (momentDiff a w dw da) (hermiteG a i) / w i := by
  rw [momentLinear_momentDiff_hermiteG ha, mul_div_cancel_left₀ _ hw]

/-- The Jacobian `J` of the moment map `(w, a) ↦ (m_0, …, m_{2n-1})`, as the linear map
`(dw, da) ↦ (dm_k)_{k < 2n}` of `prony:eq:diff`. -/
def momentJac (a w : Fin n → K) : (Fin n → K) × (Fin n → K) →ₗ[K] (Fin (2 * n) → K) where
  toFun p k := momentDiff a w p.1 p.2 k
  map_add' p q := by
    funext k
    simp only [momentDiff, Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  map_smul' c p := by
    funext k
    simp only [momentDiff, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem momentJac_apply (a w : Fin n → K) (p : (Fin n → K) × (Fin n → K))
    (k : Fin (2 * n)) : momentJac a w p k = momentDiff a w p.1 p.2 k := rfl

/-- `prony:eq:invdiff`: the Jacobian of a regular configuration is injective, since its rows are
recovered by `H_i` and `G_i`. -/
theorem momentJac_injective (ha : Function.Injective a) {w : Fin n → K} (hw : ∀ i, w i ≠ 0) :
    Function.Injective (momentJac a w) := by
  rintro ⟨dw, da⟩ ⟨dw', da'⟩ h
  have hk : ∀ k < 2 * n, momentDiff a w dw da k = momentDiff a w dw' da' k := fun k hk => by
    simpa using congrFun h ⟨k, hk⟩
  have h1 : dw = dw' := funext fun i => by
    rw [← momentLinear_momentDiff_hermiteH ha w dw da i,
      ← momentLinear_momentDiff_hermiteH ha w dw' da' i]
    exact momentLinear_congr (natDegree_hermiteH_lt a i) hk
  have h2 : da = da' := funext fun i => by
    refine mul_left_cancel₀ (hw i) ?_
    rw [← momentLinear_momentDiff_hermiteG ha w dw da i,
      ← momentLinear_momentDiff_hermiteG ha w dw' da' i]
    exact momentLinear_congr (natDegree_hermiteG_lt a i) hk
  rw [h1, h2]

/-- `prony:eq:invdiff`: the Jacobian `J` of a regular configuration is invertible. -/
theorem momentJac_bijective (ha : Function.Injective a) {w : Fin n → K} (hw : ∀ i, w i ≠ 0) :
    Function.Bijective (momentJac a w) := by
  refine ⟨momentJac_injective ha hw, ?_⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (momentJac_injective ha hw)
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]
  omega

/-- Every moment increment `(dm_k)_{k < 2n}` is the differential of some parameter increment. -/
theorem exists_momentDiff_eq (ha : Function.Injective a) {w : Fin n → K} (hw : ∀ i, w i ≠ 0)
    (dm : ℕ → K) : ∃ dw da : Fin n → K, ∀ k < 2 * n, momentDiff a w dw da k = dm k := by
  obtain ⟨⟨dw, da⟩, h⟩ := (momentJac_bijective ha hw).2 fun k => dm k
  exact ⟨dw, da, fun k hk => by simpa using congrFun h ⟨k, hk⟩⟩

/-- `prony:eq:invdiff`: the rows of `J⁻¹`. A parameter increment `(dw, da)` has moment
differential `dm` in degrees `< 2n` if and only if `dw_i = (dL)(H_i)` and
`da_i = (dL)(G_i)/w_i` for every `i`, where `dL(X^k) = dm_k`. -/
theorem momentDiff_eq_iff (ha : Function.Injective a) {w : Fin n → K} (hw : ∀ i, w i ≠ 0)
    (dm : ℕ → K) (dw da : Fin n → K) :
    (∀ k < 2 * n, momentDiff a w dw da k = dm k) ↔
      (∀ i, dw i = momentLinear dm (hermiteH a i)) ∧
        ∀ i, da i = momentLinear dm (hermiteG a i) / w i := by
  have key : ∀ dw da : Fin n → K, (∀ k < 2 * n, momentDiff a w dw da k = dm k) →
      (∀ i, dw i = momentLinear dm (hermiteH a i)) ∧
        ∀ i, da i = momentLinear dm (hermiteG a i) / w i := fun dw da h =>
    ⟨fun i => by
      rw [← momentLinear_congr (natDegree_hermiteH_lt a i) h,
        momentLinear_momentDiff_hermiteH ha],
    fun i => by
      rw [← momentLinear_congr (natDegree_hermiteG_lt a i) h]
      exact eq_momentLinear_momentDiff_hermiteG_div ha dw da (hw i)⟩
  refine ⟨key dw da, fun ⟨h1, h2⟩ => ?_⟩
  obtain ⟨dw', da', h'⟩ := exists_momentDiff_eq ha hw dm
  obtain ⟨h1', h2'⟩ := key dw' da' h'
  have hdw : dw = dw' := funext fun i => (h1 i).trans (h1' i).symm
  have hda : da = da' := funext fun i => (h2 i).trans (h2' i).symm
  rw [hdw, hda]
  exact h'

/-- `prony:eq:hermite`: `H_i` and `G_i` are the Hermite interpolation basis in degree `< 2n`.
Every `f` of degree `< 2n` is `∑_i (f(a_i) H_i + f'(a_i) G_i)`. The proof is dual to the
invertibility of `J`: the difference is killed by every moment functional. -/
theorem eq_sum_hermite (ha : Function.Injective a) {f : K[X]} (hf : f.natDegree < 2 * n) :
    f = ∑ i, (C (f.eval (a i)) * hermiteH a i + C ((derivative f).eval (a i)) * hermiteG a i) := by
  set D := f - ∑ i, (C (f.eval (a i)) * hermiteH a i +
    C ((derivative f).eval (a i)) * hermiteG a i) with hD
  have hsum : (∑ i, (C (f.eval (a i)) * hermiteH a i +
      C ((derivative f).eval (a i)) * hermiteG a i)).natDegree ≤ 2 * n - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le _ _).trans (by have := natDegree_hermiteH_lt a i; omega)
    · exact (natDegree_C_mul_le _ _).trans (by have := natDegree_hermiteG_lt a i; omega)
  have hDdeg : D.natDegree < 2 * n :=
    (natDegree_sub_le _ _).trans_lt (max_lt hf (hsum.trans_lt (by omega)))
  have hL : ∀ m : ℕ → K, momentLinear m D = 0 := by
    intro m
    obtain ⟨dw, da, h⟩ := exists_momentDiff_eq ha (w := fun _ => 1) (fun _ => one_ne_zero) m
    rw [← momentLinear_congr hDdeg h, hD, map_sub, map_sum, momentLinear_momentDiff, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, momentLinear_C_mul, momentLinear_C_mul, momentLinear_momentDiff_hermiteH ha,
      momentLinear_momentDiff_hermiteG ha]
    ring
  have hD0 : D = 0 := by
    ext k
    rw [coeff_zero]
    by_cases hk : k < 2 * n
    · have h := hL fun j => if j = k then 1 else 0
      rw [momentLinear_eq_sum _ _ hDdeg] at h
      simpa [hk] using h
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  exact sub_eq_zero.mp hD0

end Field

section Hahn

open scoped _root_.HahnSeries

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]
  {n : ℕ}

/-- The Gauss valuation `v_G(f) = min_k v([X^k] f)` of `prony:sec:lattice`, as the weighted
Gauss valuation `Surreal.HahnSeries.weightedGaussVal` with center `0` and weight `0`. It is an
additive valuation, so it is multiplicative in the source's sense. -/
def gaussVal : AddValuation R⟦Γ⟧[X] (WithTop Γ) :=
  Surreal.HahnSeries.weightedGaussVal 0 0

theorem gaussVal_eq_inf (f : R⟦Γ⟧[X]) :
    gaussVal f = f.support.inf fun k => (f.coeff k).orderTop := by
  rw [gaussVal, Surreal.HahnSeries.weightedGaussVal_eq_inf, taylor_zero]
  simp only [smul_zero, WithTop.coe_zero, add_zero]

theorem gaussVal_le_coeff (f : R⟦Γ⟧[X]) (k : ℕ) : gaussVal f ≤ (f.coeff k).orderTop := by
  by_cases hk : k ∈ f.support
  · rw [gaussVal_eq_inf]
    exact Finset.inf_le hk
  · rw [notMem_support_iff.mp hk, _root_.HahnSeries.orderTop_zero]
    exact le_top

theorem le_gaussVal_iff {c : WithTop Γ} {f : R⟦Γ⟧[X]} :
    c ≤ gaussVal f ↔ ∀ k, c ≤ (f.coeff k).orderTop := by
  refine ⟨fun h k => h.trans (gaussVal_le_coeff f k), fun h => ?_⟩
  rw [gaussVal_eq_inf]
  exact Finset.le_inf fun k _ => h k

theorem gaussVal_eq_top_iff {f : R⟦Γ⟧[X]} : gaussVal f = ⊤ ↔ f = 0 :=
  Surreal.HahnSeries.weightedGaussVal_eq_top_iff 0 0 f

/-- The Gauss valuation is multiplicative, as used in the proof of `prony:prop:rows`. -/
theorem gaussVal_mul (f g : R⟦Γ⟧[X]) : gaussVal (f * g) = gaussVal f + gaussVal g :=
  AddValuation.map_mul _ f g

/-- The minimum defining the Gauss valuation is attained at some coefficient. -/
theorem exists_coeff_orderTop_eq_gaussVal {f : R⟦Γ⟧[X]} (hf : f ≠ 0) :
    ∃ k, (f.coeff k).orderTop = gaussVal f := by
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image f.support (fun k => (f.coeff k).orderTop)
    (support_nonempty.mpr hf)
  refine ⟨k, le_antisymm ?_ (gaussVal_le_coeff f k)⟩
  rw [gaussVal_eq_inf]
  exact Finset.le_inf fun j hj => hmin j hj

theorem gaussVal_C (c : R⟦Γ⟧) : gaussVal (C c) = c.orderTop := by
  refine le_antisymm ?_ (le_gaussVal_iff.mpr fun k => ?_)
  · simpa using gaussVal_le_coeff (C c) 0
  · rw [coeff_C]
    split_ifs
    · exact le_rfl
    · simp

/-- A monic polynomial with integral coefficients has Gauss valuation `0`. -/
theorem gaussVal_eq_zero_of_monic {f : R⟦Γ⟧[X]} (hf : f.Monic)
    (hint : ∀ k, 0 ≤ (f.coeff k).orderTop) : gaussVal f = 0 := by
  refine le_antisymm ?_ (le_gaussVal_iff.mpr hint)
  have h := gaussVal_le_coeff f f.natDegree
  rwa [hf.coeff_natDegree, _root_.HahnSeries.orderTop_one] at h

/-- Evaluation at an integral point does not lower the Gauss valuation. -/
theorem gaussVal_le_orderTop_eval (f : R⟦Γ⟧[X]) {x : R⟦Γ⟧} (hx : 0 ≤ x.orderTop) :
    gaussVal f ≤ (f.eval x).orderTop := by
  rw [eval_eq_sum_range]
  refine Surreal.ChartIsometry.le_orderTop_finset_sum _ _ fun k _ => ?_
  rw [_root_.HahnSeries.orderTop_mul, Surreal.HahnSeries.orderTop_pow]
  calc gaussVal f = gaussVal f + 0 := (add_zero _).symm
    _ ≤ _ := add_le_add (gaussVal_le_coeff f k) (nsmul_nonneg hx k)

theorem gaussVal_X_sub_C {x : R⟦Γ⟧} (hx : 0 ≤ x.orderTop) : gaussVal (X - C x) = 0 := by
  refine gaussVal_eq_zero_of_monic (monic_X_sub_C x) fun k => ?_
  rw [coeff_sub, coeff_X, coeff_C]
  refine (le_min ?_ ?_).trans _root_.HahnSeries.min_orderTop_le_orderTop_sub
  · split_ifs <;> simp
  · split_ifs
    · exact hx
    · simp

/-- `v(x⁻¹) = -v(x)`. -/
theorem orderTop_inv_eq {x : R⟦Γ⟧} {g : Γ} (hx : x.orderTop = g) :
    x⁻¹.orderTop = ((-g : Γ) : WithTop Γ) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h1 : x⁻¹.orderTop + x.orderTop = 0 := by
    rw [← _root_.HahnSeries.orderTop_mul, inv_mul_cancel₀ hx0, _root_.HahnSeries.orderTop_one]
  rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero (inv_ne_zero hx0), hx,
    ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj] at h1
  rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero (inv_ne_zero hx0), WithTop.coe_inj]
  exact eq_neg_of_add_eq_zero_left h1

theorem orderTop_two (h2 : (2 : R) ≠ 0) : (2 : R⟦Γ⟧).orderTop = 0 := by
  have h : (_root_.HahnSeries.C (2 : R) : R⟦Γ⟧) = 2 := map_ofNat _ 2
  rw [← h, ← _root_.HahnSeries.order_eq_orderTop_of_ne_zero (_root_.HahnSeries.C_ne_zero h2),
    _root_.HahnSeries.order_C, WithTop.coe_zero]

open Classical in
/-- The linear factor of `H_i`. If `χ = 0` it is `1`. Otherwise its Gauss valuation is
`min(0, v(χ)) = -max(0, -v(χ))`, from its `X`-coefficient `-2χ` and its value `1` at the
integral point `x`. This uses `v(2) = 0`, from `(2 : R) ≠ 0`; in characteristic `2` the factor
is `1`, so the formula fails whenever `v(χ) < 0`. -/
theorem gaussVal_hermiteFactor (h2 : (2 : R) ≠ 0) {x : R⟦Γ⟧} (hx : 0 ≤ x.orderTop)
    (χ : R⟦Γ⟧) : gaussVal (1 - C (2 * χ) * (X - C x)) =
      ((-(if χ = 0 then 0 else max 0 (-χ.order)) : Γ) : WithTop Γ) := by
  split_ifs with hχ
  · subst hχ
    simp only [mul_zero, map_zero, zero_mul, sub_zero, AddValuation.map_one, neg_zero,
      WithTop.coe_zero]
  have hc : (2 * χ).orderTop = χ.order := by
    rw [_root_.HahnSeries.orderTop_mul, orderTop_two h2, zero_add,
      _root_.HahnSeries.order_eq_orderTop_of_ne_zero hχ]
  have hmin : (-(max 0 (-χ.order)) : Γ) = min 0 χ.order := by
    rcases le_total 0 χ.order with h | h
    · rw [max_eq_left (neg_nonpos.mpr h), min_eq_left h, neg_zero]
    · rw [max_eq_right (neg_nonneg.mpr h), min_eq_right h, neg_neg]
  rw [hmin, WithTop.coe_min, WithTop.coe_zero]
  refine le_antisymm (le_min ?_ ?_) ?_
  · have h := gaussVal_le_orderTop_eval (1 - C (2 * χ) * (X - C x)) hx
    simpa using h
  · have h := gaussVal_le_coeff (1 - C (2 * χ) * (X - C x)) 1
    have hc1 : (1 - C (2 * χ) * (X - C x)).coeff 1 = -(2 * χ) := by
      rw [coeff_sub, coeff_C_mul, coeff_sub, coeff_X_one, coeff_C, coeff_one]
      simp
    rwa [hc1, _root_.HahnSeries.orderTop_neg, hc] at h
  · refine le_trans (le_of_eq ?_) (AddValuation.map_sub gaussVal _ _)
    rw [AddValuation.map_one, AddValuation.map_mul, gaussVal_C, gaussVal_X_sub_C hx, add_zero,
      hc]

variable {a : Fin n → R⟦Γ⟧}

/-- `prony:eq:geometry`: `d_i = ∑_{j ≠ i} v(a_i - a_j)`, for distinct nodes (`order` gives a
coincident pair the value `0`). -/
def sepSum (a : Fin n → R⟦Γ⟧) (i : Fin n) : Γ :=
  ∑ j ∈ univ.erase i, (a i - a j).order

/-- `prony:eq:geometry`: `max(0, max_{j ≠ i} v(a_i - a_j))`, the maximum folded from `0`. It is
the source's `δ_i = max_{j ≠ i} v(a_i - a_j)` for integral distinct nodes and `n ≥ 2`
(`sepMax_eq_sup'`), and the source's convention `δ_i = 0` for `n = 1` (`sepMax_fin_one`). For
non-integral nodes it can exceed the bare maximum, since it is never negative. -/
def sepMax (a : Fin n → R⟦Γ⟧) (i : Fin n) : Γ :=
  (univ.erase i).fold max 0 fun j => (a i - a j).order

open Classical in
/-- `prony:eq:cancellation`: the cancellation depth `q_i`, which is `max(0, -v(χ_i))` if
`χ_i ≠ 0` and `0` if `χ_i = 0`. -/
def cancelDepth (a : Fin n → R⟦Γ⟧) (i : Fin n) : Γ :=
  if hermiteChi a i = 0 then 0 else max 0 (-(hermiteChi a i).order)

omit [IsOrderedAddMonoid Γ] in
/-- The node loss `E_i = v(w_i) + 2 d_i` of `prony:eq:geometry` in terms of `d_i`. -/
theorem nodeLoss_eq (a w : Fin n → R⟦Γ⟧) (i : Fin n) :
    nodeLoss a w i = (w i).order + 2 • sepSum a i := rfl

omit [IsOrderedAddMonoid Γ] in
theorem orderTop_sub_of_ne (ha : Function.Injective a) {i j : Fin n} (hji : j ≠ i) :
    (a i - a j).orderTop = (a i - a j).order :=
  (_root_.HahnSeries.order_eq_orderTop_of_ne_zero (sub_ne_zero.mpr (ha.ne hji.symm))).symm

/-- `v(p_i) = d_i`, stated after `prony:eq:cofactor`. -/
theorem orderTop_eval_cofactor_self (ha : Function.Injective a) (i : Fin n) :
    ((cofactor a i).eval (a i)).orderTop = sepSum a i := by
  rw [eval_cofactor_self, Surreal.HahnSeries.orderTop_finset_prod, sepSum, WithTop.coe_sum]
  exact Finset.sum_congr rfl fun j hj => orderTop_sub_of_ne ha (Finset.ne_of_mem_erase hj)

/-- The monic integral cofactor `Q_i` has Gauss valuation `0`. -/
theorem gaussVal_cofactor (ha0 : ∀ i, 0 ≤ (a i).orderTop) (i : Fin n) :
    gaussVal (cofactor a i) = 0 :=
  gaussVal_eq_zero_of_monic (cofactor_monic a i) (coeff_orderTop_nonneg_prod ha0 _)

/-- `v_G(ℓ_i) = -d_i`. -/
theorem gaussVal_lagBasis (ha0 : ∀ i, 0 ≤ (a i).orderTop) (ha : Function.Injective a)
    (i : Fin n) : gaussVal (lagBasis a i) = ((-sepSum a i : Γ) : WithTop Γ) := by
  rw [lagBasis, AddValuation.map_mul, gaussVal_C, gaussVal_cofactor ha0, add_zero,
    orderTop_inv_eq (orderTop_eval_cofactor_self ha i)]

/-- `prony:eq:gaussrows`: `v_G(G_i) = -2 d_i`. -/
theorem gaussVal_hermiteG (ha0 : ∀ i, 0 ≤ (a i).orderTop) (ha : Function.Injective a)
    (i : Fin n) : gaussVal (hermiteG a i) = ((-(2 • sepSum a i) : Γ) : WithTop Γ) := by
  rw [hermiteG, AddValuation.map_mul, AddValuation.map_pow, gaussVal_X_sub_C (ha0 i),
    gaussVal_lagBasis ha0 ha, zero_add, ← WithTop.coe_nsmul, smul_neg]

/-- `prony:eq:gaussrows`: `v_G(H_i) = -2 d_i - q_i`, for coefficient fields with `2 ≠ 0`. In
characteristic `2`, `H_i = ℓ_i²` and `v_G(H_i) = -2 d_i`, which differs when `q_i > 0`. -/
theorem gaussVal_hermiteH (h2 : (2 : R) ≠ 0) (ha0 : ∀ i, 0 ≤ (a i).orderTop)
    (ha : Function.Injective a) (i : Fin n) :
    gaussVal (hermiteH a i) = ((-(2 • sepSum a i) - cancelDepth a i : Γ) : WithTop Γ) := by
  rw [hermiteH, AddValuation.map_mul, AddValuation.map_pow, gaussVal_hermiteFactor h2 (ha0 i),
    gaussVal_lagBasis ha0 ha, ← WithTop.coe_nsmul, ← WithTop.coe_add, cancelDepth, smul_neg]
  congr 1
  abel

theorem cancelDepth_nonneg (a : Fin n → R⟦Γ⟧) (i : Fin n) : 0 ≤ cancelDepth a i := by
  unfold cancelDepth
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

omit [IsOrderedAddMonoid Γ] in
theorem sepMax_nonneg (a : Fin n → R⟦Γ⟧) (i : Fin n) : 0 ≤ sepMax a i :=
  (Finset.le_fold_max _).mpr (Or.inl le_rfl)

omit [IsOrderedAddMonoid Γ] in
theorem order_sub_le_sepMax (a : Fin n → R⟦Γ⟧) {i j : Fin n} (hji : j ≠ i) :
    (a i - a j).order ≤ sepMax a i :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, le_rfl⟩)

omit [IsOrderedAddMonoid Γ] in
/-- For integral distinct nodes and `n ≥ 2`, `δ_i` is the maximum of the `d_ij` over `j ≠ i`. -/
theorem sepMax_eq_sup' (ha0 : ∀ i, 0 ≤ (a i).orderTop) (ha : Function.Injective a) {i : Fin n}
    (h : (univ.erase i).Nonempty) :
    sepMax a i = (univ.erase i).sup' h fun j => (a i - a j).order := by
  refine le_antisymm ((Finset.fold_max_le _).mpr ⟨?_, fun j hj =>
    Finset.le_sup' (fun j => (a i - a j).order) hj⟩)
    (Finset.sup'_le _ _ fun j hj => order_sub_le_sepMax a (Finset.ne_of_mem_erase hj))
  obtain ⟨j, hj⟩ := h
  refine le_trans ?_ (Finset.le_sup' (fun j => (a i - a j).order) hj)
  have hle : (0 : WithTop Γ) ≤ (a i - a j).orderTop :=
    (le_min (ha0 i) (ha0 j)).trans _root_.HahnSeries.min_orderTop_le_orderTop_sub
  rwa [orderTop_sub_of_ne ha (Finset.ne_of_mem_erase hj), ← WithTop.coe_zero,
    WithTop.coe_le_coe] at hle

omit [IsOrderedAddMonoid Γ] in
/-- `prony:eq:geometry`, the convention for `n = 1`: the empty maximum `δ_i` is `0`. -/
theorem sepMax_fin_one (a : Fin 1 → R⟦Γ⟧) (i : Fin 1) : sepMax a i = 0 := by
  have h : (univ.erase i : Finset (Fin 1)) = ∅ := by
    ext j
    simp [Subsingleton.elim j i]
  rw [sepMax, h, Finset.fold_empty]

/-- `prony:eq:cancellation`: `0 ≤ q_i ≤ δ_i`, by the ultrametric inequality for the sum
defining `χ_i`. Here `δ_i` is `sepMax a i = max(0, max_{j ≠ i} d_ij)`, so no integrality is
needed; for integral nodes and `n ≥ 2` it is the source's `δ_i` (`sepMax_eq_sup'`). -/
theorem cancelDepth_le_sepMax (ha : Function.Injective a) (i : Fin n) :
    0 ≤ cancelDepth a i ∧ cancelDepth a i ≤ sepMax a i := by
  refine ⟨cancelDepth_nonneg a i, ?_⟩
  unfold cancelDepth
  split_ifs with hχ
  · exact sepMax_nonneg a i
  refine max_le (sepMax_nonneg a i) ?_
  have hbound : ((-sepMax a i : Γ) : WithTop Γ) ≤ (hermiteChi a i).orderTop := by
    refine Surreal.ChartIsometry.le_orderTop_finset_sum _ _ fun j hj => ?_
    rw [orderTop_inv_eq (orderTop_sub_of_ne ha (Finset.ne_of_mem_erase hj)), WithTop.coe_le_coe]
    exact neg_le_neg (order_sub_le_sepMax a (Finset.ne_of_mem_erase hj))
  rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hχ, WithTop.coe_le_coe] at hbound
  exact neg_le.mp hbound

/-- The proof of `prony:prop:rows`: the image of the ball `t^κ O^N` under the row
`dm ↦ ∑_k f_k dm_k` is exactly the fractional ideal `t^(κ + v_G(f)) O`, generated by a
coefficient of least valuation. -/
theorem exists_momentLinear_eq_iff {f : R⟦Γ⟧[X]} (hf : f ≠ 0) {N : ℕ} (hN : f.natDegree < N)
    (κ : Γ) (y : R⟦Γ⟧) :
    (∃ dm : ℕ → R⟦Γ⟧, (∀ k < N, (κ : WithTop Γ) ≤ (dm k).orderTop) ∧ momentLinear dm f = y) ↔
      (κ : WithTop Γ) + gaussVal f ≤ y.orderTop := by
  constructor
  · rintro ⟨dm, hdm, rfl⟩
    rw [momentLinear_eq_sum dm f hN]
    refine Surreal.ChartIsometry.le_orderTop_finset_sum _ _ fun k hk => ?_
    rw [_root_.HahnSeries.orderTop_mul, add_comm (κ : WithTop Γ)]
    exact add_le_add (gaussVal_le_coeff f k) (hdm k (Finset.mem_range.mp hk))
  · intro hy
    obtain ⟨k₀, hk₀⟩ := exists_coeff_orderTop_eq_gaussVal hf
    have htop : gaussVal f ≠ ⊤ := fun h => hf (gaussVal_eq_top_iff.mp h)
    have hne : f.coeff k₀ ≠ 0 := by
      intro h0
      rw [h0, _root_.HahnSeries.orderTop_zero] at hk₀
      exact htop hk₀.symm
    have hk₀N : k₀ < N := (le_natDegree_of_ne_zero hne).trans_lt hN
    refine ⟨fun k => if k = k₀ then y / f.coeff k₀ else 0, fun k _ => ?_, ?_⟩
    · dsimp only
      split_ifs
      · have hmul : (y / f.coeff k₀).orderTop + (f.coeff k₀).orderTop = y.orderTop := by
          rw [← _root_.HahnSeries.orderTop_mul, div_mul_cancel₀ _ hne]
        rw [← hmul, hk₀] at hy
        exact (WithTop.add_le_add_iff_right htop).mp hy
      · simp
    · rw [momentLinear_eq_sum _ f hN]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range, if_pos hk₀N]
      exact mul_div_cancel₀ _ hne

variable {w : Fin n → R⟦Γ⟧}

/-- The tangent precision lattice `J⁻¹ t^κ O^{2n}`: the parameter increments `(dw, da)` whose
moment differentials `dm_k`, `k < 2n`, all have valuation `≥ κ`. -/
def tangentLattice (a w : Fin n → R⟦Γ⟧) (κ : Γ) : Set ((Fin n → R⟦Γ⟧) × (Fin n → R⟦Γ⟧)) :=
  momentJac a w ⁻¹' {m | ∀ k, (κ : WithTop Γ) ≤ (m k).orderTop}

theorem mem_tangentLattice {κ : Γ} {p : (Fin n → R⟦Γ⟧) × (Fin n → R⟦Γ⟧)} :
    p ∈ tangentLattice a w κ ↔
      ∀ k < 2 * n, (κ : WithTop Γ) ≤ (momentDiff a w p.1 p.2 k).orderTop := by
  simp only [tangentLattice, Set.mem_preimage, Set.mem_setOf_eq, momentJac_apply]
  exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k k.2⟩

/-- For a regular configuration the preimage `tangentLattice` is the image of the ball
`t^κ O^{2n}` under the inverse of the Jacobian. -/
theorem tangentLattice_eq_image_symm (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0) (κ : Γ) :
    tangentLattice a w κ = (LinearEquiv.ofBijective (momentJac a w)
      (momentJac_bijective ha hw)).symm '' {m | ∀ k, (κ : WithTop Γ) ≤ (m k).orderTop} := by
  rw [LinearEquiv.image_symm_eq_preimage]
  rfl

/-- `prony:eq:marginals`, weight coordinates (`prony:prop:rows`): the projection of the tangent
lattice to `dw_i` is the whole fractional ideal `t^(κ - 2d_i - q_i) O`. -/
theorem image_weight_tangentLattice (h2 : (2 : R) ≠ 0) (ha0 : ∀ i, 0 ≤ (a i).orderTop)
    (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0) (κ : Γ) (i : Fin n) :
    (fun p => p.1 i) '' tangentLattice a w κ =
      {y | ((κ - 2 • sepSum a i - cancelDepth a i : Γ) : WithTop Γ) ≤ y.orderTop} := by
  have hv : ((κ - 2 • sepSum a i - cancelDepth a i : Γ) : WithTop Γ) =
      (κ : WithTop Γ) + gaussVal (hermiteH a i) := by
    rw [gaussVal_hermiteH h2 ha0 ha, ← WithTop.coe_add]
    congr 1
    abel
  have hrow := exists_momentLinear_eq_iff (hermiteH_ne_zero ha i) (natDegree_hermiteH_lt a i) κ
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, hv]
  constructor
  · rintro ⟨⟨dw, da⟩, hp, rfl⟩
    rw [mem_tangentLattice] at hp
    change (κ : WithTop Γ) + gaussVal (hermiteH a i) ≤ (dw i).orderTop
    rw [← momentLinear_momentDiff_hermiteH ha w dw da i]
    exact (hrow _).mp ⟨_, hp, rfl⟩
  · intro hy
    obtain ⟨dm, hdm, hdmy⟩ := (hrow y).mpr hy
    obtain ⟨dw, da, h⟩ := exists_momentDiff_eq ha hw dm
    refine ⟨(dw, da), mem_tangentLattice.mpr fun k hk => ?_, ?_⟩
    · rw [h k hk]
      exact hdm k hk
    · change dw i = y
      rw [← momentLinear_momentDiff_hermiteH ha w dw da i,
        momentLinear_congr (natDegree_hermiteH_lt a i) h, hdmy]

/-- `prony:eq:marginals`, node coordinates (`prony:prop:rows`): the projection of the tangent
lattice to `da_i` is the whole fractional ideal `t^(κ - E_i) O`, `E_i = v(w_i) + 2 d_i`. -/
theorem image_node_tangentLattice (ha0 : ∀ i, 0 ≤ (a i).orderTop) (ha : Function.Injective a)
    (hw : ∀ i, w i ≠ 0) (κ : Γ) (i : Fin n) :
    (fun p => p.2 i) '' tangentLattice a w κ =
      {y | ((κ - nodeLoss a w i : Γ) : WithTop Γ) ≤ y.orderTop} := by
  have hwv : (w i).orderTop = (w i).order :=
    (_root_.HahnSeries.order_eq_orderTop_of_ne_zero (hw i)).symm
  have hsplit : (κ : WithTop Γ) + gaussVal (hermiteG a i) =
      ((κ - nodeLoss a w i : Γ) : WithTop Γ) + ((w i).order : WithTop Γ) := by
    rw [gaussVal_hermiteG ha0 ha, ← WithTop.coe_add, ← WithTop.coe_add, nodeLoss_eq]
    congr 1
    abel
  have hkey : ∀ y : R⟦Γ⟧, ((κ - nodeLoss a w i : Γ) : WithTop Γ) ≤ y.orderTop ↔
      (κ : WithTop Γ) + gaussVal (hermiteG a i) ≤ (w i * y).orderTop := by
    intro y
    rw [hsplit, _root_.HahnSeries.orderTop_mul, hwv, add_comm ((w i).order : WithTop Γ),
      WithTop.add_le_add_iff_right WithTop.coe_ne_top]
  have hrow := exists_momentLinear_eq_iff (hermiteG_ne_zero ha i) (natDegree_hermiteG_lt a i) κ
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, hkey]
  constructor
  · rintro ⟨⟨dw, da⟩, hp, rfl⟩
    rw [mem_tangentLattice] at hp
    change (κ : WithTop Γ) + gaussVal (hermiteG a i) ≤ (w i * da i).orderTop
    rw [← momentLinear_momentDiff_hermiteG ha w dw da i]
    exact (hrow _).mp ⟨_, hp, rfl⟩
  · intro hy
    obtain ⟨dm, hdm, hdmy⟩ := (hrow _).mpr hy
    obtain ⟨dw, da, h⟩ := exists_momentDiff_eq ha hw dm
    refine ⟨(dw, da), mem_tangentLattice.mpr fun k hk => ?_, ?_⟩
    · rw [h k hk]
      exact hdm k hk
    · change da i = y
      refine mul_left_cancel₀ (hw i) ?_
      rw [← momentLinear_momentDiff_hermiteG ha w dw da i,
        momentLinear_congr (natDegree_hermiteG_lt a i) h, hdmy]

/-- `prony:prop:rows` (exact row losses). For integral distinct nodes, nonzero weights and a
coefficient field with `2 ≠ 0`: `v_G(G_i) = -2 d_i`, `v_G(H_i) = -2 d_i - q_i`
(`prony:eq:gaussrows`), and the coordinate projections of the tangent precision lattice
`J⁻¹ t^κ O^{2n}` are the whole fractional ideals `da_i ∈ t^(κ - E_i) O` and
`dw_i ∈ t^(κ - 2d_i - q_i) O` (`prony:eq:marginals`). -/
theorem exact_row_losses (h2 : (2 : R) ≠ 0) (ha0 : ∀ i, 0 ≤ (a i).orderTop)
    (ha : Function.Injective a) (hw : ∀ i, w i ≠ 0) (κ : Γ) (i : Fin n) :
    gaussVal (hermiteG a i) = ((-(2 • sepSum a i) : Γ) : WithTop Γ) ∧
      gaussVal (hermiteH a i) = ((-(2 • sepSum a i) - cancelDepth a i : Γ) : WithTop Γ) ∧
      (fun p => p.2 i) '' tangentLattice a w κ =
        {y | ((κ - nodeLoss a w i : Γ) : WithTop Γ) ≤ y.orderTop} ∧
      (fun p => p.1 i) '' tangentLattice a w κ =
        {y | ((κ - 2 • sepSum a i - cancelDepth a i : Γ) : WithTop Γ) ≤ y.orderTop} :=
  ⟨gaussVal_hermiteG ha0 ha i, gaussVal_hermiteH h2 ha0 ha i,
    image_node_tangentLattice ha0 ha hw κ i, image_weight_tangentLattice h2 ha0 ha hw κ i⟩

end Hahn

end

end Surreal.PronyRows

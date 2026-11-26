import Lib.DiscreteSeries.FlenstedJensen.Defs
import Lib.General.Analysis.HolomorphicIntegrals

/-!
# Products of principal minors, Fischer's inequality and the Cauchy–Binet formula

For an integer vector `w` and an invertible complex matrix `x`, m_w(x) = `New.weightMinors w x` is
the product over all integers `t` of the principal minors `New.principalMinor` of `x` on
`{i | t ≤ w i}`. The factors with `t ≤ 0` are divided by `x.det`. The file develops the calculus of
m_w and the closure properties of the invertible triangular matrices `New.IsBorelMatrix o`.

## Main definitions and results

* `New.weightMinors_eq_det_zpow_mul_prod`: the finite form `x.det ^ a * ∏_{a < t ≤ b}` of minors,
  when `a ≤ w ≤ b`.
* `New.fischer_det_inequality`: for a positive semidefinite matrix in 2×2 block form,
  |det z| ≤ |det z₁₁| · |det z₂₂|.
* `New.fischer_inequality`: for positive semidefinite z, the principal minor
  (`New.principalMinor`) on a disjoint union of two index sets is at most, in absolute value, the
  product of the two principal minors.
* `New.hadamard_det_inequality`: for positive semidefinite z, |det z| is at most the product of
  the |z_ii|.
* `New.det_mul_eq_sum_minors`: the Cauchy–Binet formula.
* `New.det_fromCols_eq_sum_minors`, `New.sum_norm_det_fromCols_sq_le`: the Laplace expansion along
  a block of columns and a bound for its complementary minors.
-/

/-!
## The products m_w of principal minors and invertible triangular matrices

The matrices with `New.IsBorelMatrix o` (invertible, `b i j = 0` when `o j < o i`) are closed under
products and inverses. For injective `o` their diagonal entries are non-zero and multiply.
-/

namespace New

open Matrix Finset Complex ComplexConjugate Norms.L2Operator DiscreteSeries

variable {n : Type} [Fintype n] [DecidableEq n]
  {w o : n → ℤ} {x b b' : Matrix n n ℂ} {p : n → Prop} {c : ℤ} {d : n → ℂ} [DecidablePred p]

/-! ### The functions `New.weightMinors w` -/

omit [DecidableEq n] in
/-- Every entry `w i` of an integer vector lies between `-∑ j, |w j|` and `∑ j, |w j|`, so these
two sums can serve as the bounds `a`, `b` in `New.weightMinors_eq_det_zpow_mul_prod`. -/
theorem DiscreteSeries.neg_sum_abs_le_and_le_sum_abs (w : n → ℤ) (i : n) :
    -∑ j : n, |w j| ≤ w i ∧ w i ≤ ∑ j : n, |w j| :=
  abs_le.1 (single_le_sum (fun j _ ↦ abs_nonneg (w j)) (mem_univ i))

theorem weightMinors_transpose : weightMinors w xᵀ = weightMinors w x := by simp [weightMinors]

lemma conj_weightMinors : conj (weightMinors w x) = weightMinors w xᴴ := by
  have h_map (F : ℤ → ℂ) : conj (∏ᶠ t, F t) = ∏ᶠ t, conj (F t) := conjAe.toMulEquiv.map_finprod F
  simp [weightMinors, h_map, apply_ite conj]

/-- For invertible `x`, the product of principal minors `weightMinors` for the weight `-w` at `x` is
the one for `w` at `x⁻¹`. -/
theorem weightMinors_neg (hx : x.det ≠ 0) (w : n → ℤ) :
    weightMinors (-w) x = weightMinors w x⁻¹ := by
  -- Reindex the levels of `weightMinors (-w) x` by `t ↦ 1 - t`. The set `{i | 1 - t ≤ -w i}` is
  -- the complement of `{i | t ≤ w i}`, so the factors agree level by level by Jacobi's identity:
  -- the minor of `x⁻¹` on a set is the minor of `x` on the complement, divided by `x.det`.
  rw [weightMinors, weightMinors, ← finprod_comp_equiv (.subLeft (1 : ℤ))]
  refine finprod_congr fun t ↦ ?_
  have h_compl : principalMinor x (1 - t ≤ (-w) ·) = principalMinor x (¬t ≤ w ·) := by
    congr
    grind [Pi.neg_apply]
  rw [Equiv.subLeft_apply, h_compl, jacobi_complementary_minor hx, det_nonsing_inv,
    Ring.inverse_eq_inv']
  grind

/-- For invertible `x` and integers `a`, `b` with `a ≤ w i ≤ b` for all `i`: the product of
principal minors `m_w(x) = weightMinors w x` is `x.det ^ a` times the product over the levels
`a < t ≤ b` of the principal minor of `x` on `{i | t ≤ w i}`. -/
theorem weightMinors_eq_det_zpow_mul_prod (hx : x.det ≠ 0) (a b : ℤ)
    (hw : ∀ i : n, a ≤ w i ∧ w i ≤ b) :
    weightMinors w x = x.det ^ a * ∏ t ∈ Ioc a b, principalMinor x (t ≤ w ·) := by
  obtain ⟨h_sub_pos, h_sub_nonpos, h_sub⟩ : Ioc 0 a ⊆ Icc (-|a|) (|a| ⊔ b) ∧
      Ioc a 0 ⊆ Icc (-|a|) (|a| ⊔ b) ∧ Ioc a b ⊆ Icc (-|a|) (|a| ⊔ b) := by grind
  -- For `t ≤ a` the minor is `x.det` and for `b < t` it is `1`. So the factors of `weightMinors`
  -- are `1` outside the interval `[-|a|, max |a| b]`.
  have h_low (t : ℤ) (ht : t ≤ a) : principalMinor x (t ≤ w ·) = x.det := by
    grind [principalMinor_of_forall]
  have h_high (t : ℤ) (ht : b < t) : principalMinor x (t ≤ w ·) = 1 := by
    grind [principalMinor_of_forall_not]
  have h_supp : (fun t : ℤ ↦ principalMinor x (t ≤ w ·) / ite (t ≤ 0) x.det 1).mulSupport ⊆
      Icc (-|a|) (|a| ⊔ b) := by
    refine Function.mulSupport_subset_iff'.2 fun t ht ↦ ?_
    grind
  -- The factor at `t` is `x.det` if `0 < t ≤ a`; otherwise it is the minor if `a < t ≤ b`
  -- (else `1`), divided by `x.det` if `a < t ≤ 0`.
  have h_factor (t : ℤ) : principalMinor x (t ≤ w ·) / ite (t ≤ 0) x.det 1 =
      ite (t ∈ Ioc 0 a) x.det 1 / ite (t ∈ Ioc a 0) x.det 1 *
        ite (t ∈ Ioc a b) (principalMinor x (t ≤ w ·)) 1 := by
    grind
  -- The powers of `x.det` from `Ioc 0 a` and `Ioc a 0` (one is empty) combine to `x.det ^ a`.
  have h_pow : x.det ^ #(Ioc 0 a) / x.det ^ #(Ioc a 0) = x.det ^ a := by
    simp [← zpow_natCast, ← zpow_sub₀ hx]
  rw [weightMinors, finprod_eq_prod_of_mulSupport_subset _ h_supp,
    prod_congr rfl fun t _ ↦ h_factor t]
  simp only [prod_mul_distrib, prod_div_distrib, prod_ite_mem, inter_eq_right.2 h_sub_pos,
    inter_eq_right.2 h_sub_nonpos, inter_eq_right.2 h_sub, prod_const, h_pow]

/-- The product of principal minors `m_w` is complex analytic at every invertible matrix. -/
lemma analyticAt_weightMinors (hx : x.det ≠ 0) : AnalyticAt ℂ (weightMinors w) x := by
  -- Near `x` the determinant does not vanish, so there `weightMinors w` is a power of the
  -- determinant times a finite product of principal minors, which is differentiable.
  let S : ℤ := ∑ j, |w j|
  have h_det : ∀ᶠ y in nhds x, y.det ≠ 0 := ContinuousAt.eventually_ne (by fun_prop) hx
  have h_formula : (fun y ↦ y.det ^ (-S) * ∏ t ∈ Ioc (-S) S, principalMinor y (t ≤ w ·)) =ᶠ[nhds x]
      weightMinors w := h_det.mono fun _ hy ↦
    (weightMinors_eq_det_zpow_mul_prod hy _ _ (neg_sum_abs_le_and_le_sum_abs w)).symm
  refine (analyticAt_of_eventually_differentiableAt (h_det.mono fun y hy ↦ ?_)).congr h_formula
  -- Expand the determinants as polynomials in the entries; the product is indexed by a subtype
  -- for `fun_prop`.
  simp_rw [← (Ioc (-S) S).prod_coe_sort, principalMinor_eq_det, det_apply'] at hy ⊢
  fun_prop (disch := tauto)

@[simp]
theorem weightMinors_const (hx : x.det ≠ 0) (c : ℤ) :
    weightMinors (fun _ : n ↦ c) x = x.det ^ c := by
  simp [Ioc_self, weightMinors_eq_det_zpow_mul_prod hx c c]

/-- For invertible x, an integer c ≥ 0 and a set p of indices with w_j ≤ w_i for i in p, j not
in p: adding c to the entries of w on p multiplies m_w(x) = `weightMinors w x` (the product over
the levels t of the principal minors on {i | t ≤ w i}, normalised by det x) by the c-th power of
the principal minor on p. -/
theorem weightMinors_add_ite (hx : x.det ≠ 0) (hc : 0 ≤ c)
    (h_top : ∀ i j : n, p i → ¬p j → w j ≤ w i) :
    weightMinors (fun i : n ↦ w i + (if p i then c else 0)) x =
      weightMinors w x * principalMinor x p ^ c := by
  -- Let `w m` be the least weight on `p`. The level sets `{i | t ≤ w i + c·[p i]}` of the new
  -- weight are those of `w` for `t ≤ w m`, equal `p` for the `c` levels `w m < t ≤ w m + c`, and
  -- are those of `w` at level `t - c` above.
  by_cases! hp : ∀ i, ¬p i
  · simp [hp, principalMinor_of_forall_not]
  obtain ⟨m, hm, h_min⟩ : ∃ m ∈ ({i | p i} : Finset n), ∀ i ∈ ({i | p i} : Finset n), w m ≤ w i :=
    exists_min_image {i | p i} w (hp.imp (by simp))
  obtain ⟨B, hB⟩ : ∃ B : ℤ, ∀ i, |w i| ≤ B := Finite.exists_le (|w ·|)
  set w' : n → ℤ := fun i ↦ w i + if p i then c else 0
  have h_middle :
      ∏ t ∈ Ioc (w m) (w m + c), principalMinor x (t ≤ w' ·) = principalMinor x p ^ c := by
    have h_eq (t : ℤ) (ht : t ∈ Ioc (w m) (w m + c)) :
        principalMinor x (t ≤ w' ·) = principalMinor x p := by
      congr
      grind
    simp [prod_eq_pow_card h_eq, ← zpow_natCast, hc]
  have h_rest : ∏ t ∈ Ioc (-B) (B + c) \ Ioc (w m) (w m + c), principalMinor x (t ≤ w' ·) =
      ∏ t ∈ Ioc (-B) B, principalMinor x (t ≤ w ·) := by
    -- Close the gap: shift the levels above `w m + c` down by `c`.
    let down : ℤ → ℤ := fun t ↦ if t ≤ w m then t else t - c
    let up : ℤ → ℤ := fun t ↦ if t ≤ w m then t else t + c
    have h_level (t : ℤ) (ht : t ∈ Ioc (-B) (B + c) \ Ioc (w m) (w m + c)) :
        principalMinor x (t ≤ w' ·) = principalMinor x (down t ≤ w ·) := by
      congr
      grind
    exact prod_nbij' down up (by grind) (by grind) (by grind) (by grind) h_level
  rw [weightMinors_eq_det_zpow_mul_prod hx (-B) (B + c) (by grind),
    weightMinors_eq_det_zpow_mul_prod hx (-B) B (by grind),
    ← prod_sdiff (by grind : Ioc (w m) (w m + c) ⊆ Ioc (-B) (B + c)), h_rest, h_middle, mul_assoc]

/-- For invertible `x` and `c ≥ 0`, the weight that is `c` on `p` and `0` elsewhere gives the
`c`-th power of the principal minor on `p`. -/
theorem DiscreteSeries.weightMinors_ite_eq_zpow (hx : x.det ≠ 0) (hc : 0 ≤ c) :
    weightMinors (fun i : n ↦ if p i then c else 0) x = principalMinor x p ^ c := by
  simpa [weightMinors_const hx] using weightMinors_add_ite (w := fun _ ↦ 0) hx hc (by simp)

/-- For invertible `x` and a diagonal matrix with non-zero entries `d i`, multiplying `x` by the
diagonal on the left multiplies the product of principal minors `weightMinors w x` by
`∏ i, d i ^ w i`. -/
@[simp]
lemma weightMinors_diagonal_mul (hx : x.det ≠ 0) (hd : ∀ i : n, d i ≠ 0) :
    weightMinors w (diagonal d * x) = (∏ i : n, d i ^ w i) * weightMinors w x := by
  -- Write both sides by `weightMinors_eq_det_zpow_mul_prod` as products over the levels `t`. A
  -- diagonal factor multiplies each principal minor by its own minor, and `d i` occurs in the
  -- minors of the levels `t ≤ w i`.
  set S : ℤ := ∑ j, |w j|
  have h_bound : ∀ i : n, -S ≤ w i ∧ w i ≤ S := neg_sum_abs_le_and_le_sum_abs w
  have h_single (i : n) : d i ^ w i = d i ^ (-S) * ∏ t ∈ Ioc (-S) S, ite (t ≤ w i) (d i) 1 := by
    have h_levels : {t ∈ Ioc (-S) S | t ≤ w i} = Ioc (-S) (w i) := by grind
    rw [← prod_filter, h_levels, prod_const, ← zpow_natCast, ← zpow_add₀ (hd i),
      Int.card_Ioc_of_le _ _ (h_bound i).1, add_sub_cancel]
  have h_minor (t : ℤ) : principalMinor (diagonal d * x) (t ≤ w ·) =
      (∏ i, ite (t ≤ w i) (d i) 1) * principalMinor x (t ≤ w ·) := by
    rw [principalMinor_mul (by grind [diagonal_apply])]
    simp [principalMinor_eq_det, ← diagonal_one, apply_ite]
  have h_det : (diagonal d * x).det ≠ 0 := by simp [prod_eq_zero_iff, hd, hx]
  simp_rw [weightMinors_eq_det_zpow_mul_prod h_det _ _ h_bound, det_mul, det_diagonal, h_minor,
    weightMinors_eq_det_zpow_mul_prod hx _ _ h_bound, h_single, prod_mul_distrib, prod_zpow,
    mul_zpow, prod_comm (s := Ioc (-S) S), mul_mul_mul_comm]

@[simp]
theorem weightMinors_one : weightMinors w 1 = 1 := by simp [weightMinors]

@[simp]
theorem weightMinors_diagonal (hd : ∀ i : n, d i ≠ 0) :
    weightMinors w (diagonal d) = ∏ i : n, d i ^ w i := by
  simpa using weightMinors_diagonal_mul (x := 1) (by simp) hd

/-! ### Invertible triangular matrices -/

/-- A matrix that is block triangular for an injective `o` (so with blocks of size one) has as
determinant the product of its diagonal entries. -/
theorem DiscreteSeries.det_eq_prod_diag_of_blockTriangular (ho : o.Injective)
    (h_tri : b.BlockTriangular o) : b.det = ∏ i : n, b i i := by
  -- order the indices by the injective `o`; then block triangular means upper triangular
  let _ : LinearOrder n := LinearOrder.lift' o ho
  exact det_of_isUpperTriangular h_tri

theorem IsBorelMatrix.mul (hb : IsBorelMatrix o b) (hb' : IsBorelMatrix o b') :
    IsBorelMatrix o (b * b') := ⟨hb.1.mul hb'.1, by simp [hb.2, hb'.2]⟩

theorem IsBorelMatrix.inv (hb : IsBorelMatrix o b) : IsBorelMatrix o b⁻¹ := by
  let _ : Invertible b := b.invertibleOfIsUnitDet hb.2.isUnit
  exact ⟨blockTriangular_inv_of_blockTriangular hb.1, by simp [hb.2]⟩

theorem IsBorelMatrix.diag_ne_zero (ho : o.Injective) (hb : IsBorelMatrix o b) (i : n) :
    b i i ≠ 0 :=
  prod_ne_zero_iff.1 ((det_eq_prod_diag_of_blockTriangular ho hb.1).symm.trans_ne hb.2) i
    (mem_univ i)

/-- For injective `o`, diagonal entries of matrices with `New.IsBorelMatrix o` multiply. -/
theorem IsBorelMatrix.mul_apply_diag (ho : o.Injective) (hb : IsBorelMatrix o b)
    (hb' : IsBorelMatrix o b') (i : n) : (b * b') i i = b i i * b' i i :=
  Fintype.sum_eq_single i (by grind [IsBorelMatrix, BlockTriangular])

theorem IsBorelMatrix.inv_apply_diag (ho : o.Injective) (hb : IsBorelMatrix o b) (i : n) :
    b⁻¹ i i = (b i i)⁻¹ := by
  -- Compare diagonal entries in `b⁻¹ * b = 1`.
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← mul_apply_diag ho hb.inv hb, nonsing_inv_mul _ hb.2.isUnit, one_apply_eq]

end New

/-! ## Fischer's inequality for principal minors of positive semidefinite matrices -/

section FischerInequality

open Matrix ComplexOrder Fin

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Fischer's inequality: for a positive semidefinite complex matrix z in 2×2 block form,
|det z| ≤ |det z₁₁| · |det z₂₂|, with z₁₁, z₂₂ the diagonal blocks. -/
theorem New.fischer_det_inequality {m : Type*} [Fintype m] [DecidableEq m]
    {z : Matrix (m ⊕ n) (m ⊕ n) ℂ} (hz : z.PosSemidef) :
    ‖z.det‖ ≤ ‖z.toBlocks₁₁.det‖ * ‖z.toBlocks₂₂.det‖ := by
  -- Write `z = (A B; Bᴴ D)` and put `Θ = (A 2B; 0 D)`, so that `Θ + Θᴴ = z + z`. The
  -- Ostrowski–Taussky inequality bounds `‖det (z + z)‖` by `2 ^ card * ‖det A‖ * ‖det D‖`, and
  -- the factor `2 ^ card` cancels against `det (z + z) = 2 ^ card * det z`.
  let Θ := fromBlocks z.toBlocks₁₁ (z.toBlocks₁₂ + z.toBlocks₁₂) 0 z.toBlocks₂₂
  have hΘ_add : Θ + Θᴴ = z + z := by
    ext (i | i) (j | j) <;> simp [Θ, hz.1.apply, toBlocks₁₁, toBlocks₁₂, toBlocks₂₂]
  have h_bound : ‖(z + z).det‖ ≤ 2 ^ Fintype.card (m ⊕ n) * ‖Θ.det‖ :=
    ostrowski_taussky (hz.add hz) (by simp [hΘ_add, PosSemidef.zero])
  simpa [← two_smul ℂ z, Θ] using h_bound

/-- **Fischer's inequality.** Let `z` be positive semidefinite and let the index set `r` be the
disjoint union of `p` and `q`. Then the principal minor of `z` on `r` has norm at most the product
of the norms of the principal minors on `p` and `q`. -/
theorem New.fischer_inequality {z : Matrix n n ℂ} (hz : z.PosSemidef) (p q : n → Prop)
    {r : n → Prop} [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (h_disj : ∀ i : n, p i → ¬q i) (h_union : ∀ i : n, r i ↔ p i ∨ q i) :
    ‖principalMinor z r‖ ≤ ‖principalMinor z p‖ * ‖principalMinor z q‖ := by
  -- Reindex `r` as the disjoint union of `p` and `q`; the two diagonal blocks are then the
  -- principal submatrices on `p` and on `q`.
  let σ : {i // r i} ≃ {i // p i} ⊕ {i // q i} :=
    (Equiv.subtypeEquivRight h_union).trans (subtypeOrEquiv p q (by tauto))
  have h_reindexed : (reindex σ σ (z.toSquareBlockProp r)).PosSemidef := hz.submatrix _
  rw [principalMinor, ← det_reindex_self σ]
  exact fischer_det_inequality h_reindexed

/-- Hadamard's inequality: for a positive semidefinite complex matrix z, |det z| is at most the
product of the |z_ii|.

A weaker form of Hadamard's inequality as in Horn and Johnson, omitting the equality case. -/
lemma New.hadamard_det_inequality {k : ℕ} {z : Matrix (Fin k) (Fin k) ℂ} (hz : z.PosSemidef) :
    ‖z.det‖ ≤ ∏ i : Fin k, ‖z i i‖ := by
  induction k with
  | zero => simp [prod_univ_zero]
  | succ k ih =>
    -- split off the last row and column by Fischer's inequality
    let z' : Matrix (Fin k ⊕ Fin 1) (Fin k ⊕ Fin 1) ℂ := z.submatrix finSumFinEquiv finSumFinEquiv
    have h_last : z'.toBlocks₂₂.det = z (last k) (last k) := det_unique _
    calc ‖z.det‖ = ‖z'.det‖ := by rw [det_submatrix_equiv_self]
      _ ≤ ‖z'.toBlocks₁₁.det‖ * ‖z'.toBlocks₂₂.det‖ := fischer_det_inequality (hz.submatrix _)
      _ ≤ (∏ i : Fin k, ‖z i.castSucc i.castSucc‖) * ‖z (last k) (last k)‖ := by
        rw [h_last]
        gcongr
        exact ih (hz.submatrix castSucc)
      _ = ∏ i : Fin (k + 1), ‖z i i‖ := (prod_univ_castSucc fun i ↦ ‖z i i‖).symm

end FischerInequality

/-!
## Expansions in minors

The Cauchy–Binet formula and the Laplace expansion of a determinant along a block of columns, both
read off from the standard basis of an exterior power, and a bound for the complementary minors of
the Laplace expansion by the Cauchy–Binet formula and Hadamard's inequality.
-/

section MinorExpansions

open Matrix Finset Set.powersetCard ComplexOrder

namespace New

variable {R I L N c : Type} [CommRing R] {k : ℕ}

/-- The elements of a set of `k` indices (`S : Set.powersetCard I k`) in increasing order. -/
abbrev enumSubset [LinearOrder I] (S : Set.powersetCard I k) : Fin k → I := ofFinEmbEquiv.symm S

/-- The value of an alternating form `f` in `k` vectors at the columns of `X` is the sum over the
`k`-sets `S` of rows (listed in increasing order by `enumSubset S`) of the minor of `X` on `S` times
the value of `f` at the basis vectors of `S`. -/
lemma alternatingMap_eq_sum_minors [Fintype I] [LinearOrder I]
    (f : (I → R) [⋀^Fin k]→ₗ[R] R) (X : Matrix I (Fin k) R) :
    f (fun a : Fin k ↦ X.col a) = ∑ S : Set.powersetCard I k,
      (X.submatrix (enumSubset S) id).det * f fun a : Fin k ↦ Pi.single (enumSubset S a) 1 := by
  -- Apply the linear map `φ` induced by `f` to the exterior product `v` of the columns, expanded
  -- in the standard basis of the exterior power.
  let φ : ⋀[R]^k (I → R) →ₗ[R] R := exteriorPower.alternatingMapLinearEquiv f
  let v : ⋀[R]^k (I → R) := exteriorPower.ιMulti R k fun a ↦ X.col a
  let B : Module.Basis (Set.powersetCard I k) R (⋀[R]^k (I → R)) :=
    (Pi.basisFun R I).exteriorPower k
  have h_coord (S : Set.powersetCard I k) : B.repr v S = (X.submatrix (enumSubset S) id).det := by
    rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
      ← det_transpose (X.submatrix _ _)]
    simp [submatrix, transpose]
  have h_value (S : Set.powersetCard I k) : φ (B S) = f fun a ↦ Pi.single (enumSubset S a) 1 := by
    simp [φ, B, exteriorPower.ιMulti_family, Function.comp_def]
  calc f (fun a ↦ X.col a) = φ v := (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f _).symm
    _ = φ (∑ S, B.repr v S • B S) := by rw [B.sum_repr]
    _ = _ := by simp [h_coord, h_value]

/-- The Cauchy–Binet formula: the determinant of `A * X`, with `k` rows in `A` and `k` columns in
`X`, is the sum over the `k`-sets `S` of inner indices (listed in increasing order by
`enumSubset S`) of the products of the minors of `X` and `A` on `S`. -/
theorem det_mul_eq_sum_minors [Fintype I] [LinearOrder I] (A : Matrix (Fin k) I R)
    (X : Matrix I (Fin k) R) :
    (A * X).det = ∑ S : Set.powersetCard I k,
      (X.submatrix (enumSubset S) id).det * (A.submatrix id (enumSubset S)).det := by
  let f : (I → R) [⋀^Fin k]→ₗ[R] R := detRowAlternating.compLinearMap A.mulVecLin
  have h_det : (A * X).det = f fun a ↦ X.col a := (det_transpose (A * X)).symm
  have h_minor (S : Set.powersetCard I k) :
      f (fun a ↦ Pi.single (enumSubset S a) 1) = (A.submatrix id (enumSubset S)).det := by
    rw [← det_transpose]
    exact congrArg det (by ext; simp)
  simp_rw [h_det, alternatingMap_eq_sum_minors, h_minor]

/-- The determinant of the matrix with columns `(Y Z)`, made square by `e`, is an alternating form
in the `k` columns of `Y`. -/
lemma exists_alternatingMap_det_fromCols [Fintype L] [DecidableEq L] (e : L ≃ Fin k ⊕ c)
    (Z : Matrix L c R) :
    ∃ f : (L → R) [⋀^Fin k]→ₗ[R] R, ∀ Y : Matrix L (Fin k) R,
      ((fromCols Y Z).submatrix id e).det = f fun a : Fin k ↦ Y.col a := by
  -- The determinant `g` is an alternating form in columns indexed by `Fin k ⊕ c`. Curry it along
  -- this sum and evaluate the arguments indexed by `c` at the columns of `Z`.
  let g : (L → R) [⋀^Fin k ⊕ c]→ₗ[R] R := detRowAlternating.domDomCongr e
  let atZ : MultilinearMap R (fun _ : c ↦ L → R) R →ₗ[R] R :=
    { toFun φ := φ fun b ↦ Z.col b
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let f : (L → R) [⋀^Fin k]→ₗ[R] R :=
    { atZ.compMultilinearMap g.toMultilinearMap.currySum with
      map_eq_zero_of_eq' v a b hab hne :=
        g.map_eq_zero_of_eq _ (i := .inl a) (j := .inl b) hab (by simpa using hne) }
  refine ⟨f, fun Y ↦ ?_⟩
  have h_rows : ((fromCols Y Z).submatrix id e)ᵀ =
      .of fun a ↦ Sum.elim (fun i ↦ Y.col i) (fun j ↦ Z.col j) (e a) := by
    ext a b
    cases h : e a <;> simp [h]
  change _ = g (Sum.elim (fun i ↦ Y.col i) fun j ↦ Z.col j)
  rw [← det_transpose, h_rows]
  rfl

/-- The Laplace expansion along the first `k` columns, when these are combinations, with
coefficients `X`, of the unit columns at the rows `r`. Here `e` identifies the index set `L` with
these `k` columns followed by those of `Z`, and `enumSubset S` lists a `k`-set `S` in increasing
order. The determinant is the sum over `S` of the minor of `X` on `S` times the determinant with
the unit columns at `r ∘ enumSubset S` in place of the first `k` columns. -/
theorem det_fromCols_eq_sum_minors [Fintype L] [DecidableEq L] [Fintype N] [LinearOrder N]
    (e : L ≃ Fin k ⊕ c) (r : N → L) (X : Matrix N (Fin k) R) (Z : Matrix L c R) :
    ((fromCols ((1 : Matrix L L R).submatrix id r * X) Z).submatrix id e).det =
      ∑ S : Set.powersetCard N k, (X.submatrix (enumSubset S) id).det *
        ((fromCols ((1 : Matrix L L R).submatrix id (r ∘ enumSubset S)) Z).submatrix id e).det := by
  -- The determinant is an alternating form `f` in its first `k` columns. Expand in minors the
  -- form `F`, which is `f` evaluated at combinations of the unit columns `M`.
  obtain ⟨f, hf⟩ := exists_alternatingMap_det_fromCols e Z
  let M : Matrix L N R := (1 : Matrix L L R).submatrix id r
  let F : (N → R) [⋀^Fin k]→ₗ[R] R := f.compLinearMap M.mulVecLin
  have h_right (S : Set.powersetCard N k) : F (fun a ↦ Pi.single (enumSubset S a) 1) =
      f fun a ↦ ((1 : Matrix L L R).submatrix id (r ∘ enumSubset S)).col a :=
    congrArg f (funext fun a ↦ mulVec_single_one M (enumSubset S a))
  simp_rw [hf, ← h_right]
  exact alternatingMap_eq_sum_minors F X

/-- If `ι` and `t` together enumerate the rows, a determinant with unit columns on `ι` has the
modulus of the minor of `Z` on the rows `t`. -/
lemma norm_det_fromCols_one_submatrix [Fintype L] [DecidableEq L] [Fintype c] [DecidableEq c]
    (e : L ≃ Fin k ⊕ c) {ι : Fin k → L} {t : c → L} (h_bij : Function.Bijective (Sum.elim ι t))
    (Z : Matrix L c ℂ) :
    ‖((fromCols ((1 : Matrix L L ℂ).submatrix id ι) Z).submatrix id e).det‖ =
      ‖(Z.submatrix t id).det‖ := by
  -- After a permutation of the rows the matrix is block triangular.
  let ε : Fin k ⊕ c ≃ L := Equiv.ofBijective _ h_bij
  have h_block : (fromCols ((1 : Matrix L L ℂ).submatrix id ι) Z).submatrix id e =
      ((fromBlocks 1 (Z.submatrix ι id) 0 (Z.submatrix t id)).submatrix e e).submatrix
        (ε.symm.trans e.symm) id := by
    ext x y
    obtain ⟨x, rfl⟩ := ε.surjective x
    have h_eq (a : Fin k) : Sum.elim ι t x = ι a ↔ x = .inl a := h_bij.1.eq_iff (b := .inl a)
    simp only [submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    -- compare the four blocks: `x` is a row in `ι` or in `t`, and `y` a column of `1` or of `Z`
    cases x <;> cases h : e y <;> simp_all [ε, one_apply]
  rw [h_block, det_permute, det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
  simp [abs_unit_intCast]

/-- The complementary minors in the Laplace expansion have squared moduli with sum at most the
product of the squared lengths of the columns of `Z`. Here `e` identifies the index set `L` with
`k` columns followed by those of `Z`, and the `k` unit columns are at the rows `r ∘ enumSubset S`,
the images under the embedding `r` of the `k`-set `S` in increasing order. -/
theorem sum_norm_det_fromCols_sq_le [Fintype L] [DecidableEq L] [Fintype c] [Fintype N]
    [LinearOrder N] (e : L ≃ Fin k ⊕ c) (r : N ↪ L) (Z : Matrix L c ℂ) :
    ∑ S : Set.powersetCard N k,
        ‖((fromCols ((1 : Matrix L L ℂ).submatrix id (r ∘ enumSubset S)) Z).submatrix
          id e).det‖ ^ 2 ≤
      ∏ b : c, ∑ x : L, ‖Z x b‖ ^ 2 := by
  classical
  let _ : LinearOrder L := .lift' (Fintype.equivFin L) (Equiv.injective _)
  let ε : c ≃ Fin (Fintype.card c) := Fintype.equivFin c
  let Z' := Z.submatrix id ε.symm
  have h_card : Fintype.card c + k = Fintype.card L := by simp [Fintype.card_congr e, add_comm]
  -- `T S` is the set of rows outside `r S`.
  let T (S : Set.powersetCard N k) := compl h_card (Set.powersetCard.map k r S)
  have T_inj : Function.Injective T := fun S S' h ↦ by simpa [T, Subtype.ext_iff] using h
  -- The rows `r S` and `T S` together enumerate all rows.
  have h_bij (S : Set.powersetCard N k) :
      Function.Bijective (Sum.elim (r ∘ enumSubset S) (enumSubset (T S) ∘ ε)) := by
    rw [Fintype.bijective_iff_surjective_and_card, Fintype.card_congr e]
    refine ⟨fun x ↦ ?_, rfl⟩
    by_cases hx : x ∈ Set.powersetCard.map k r S
    · obtain ⟨y, hy, rfl⟩ := (mem_map_iff_mem_range k r S x).1 hx
      obtain ⟨a, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem S y).2 hy
      exact ⟨.inl a, rfl⟩
    · obtain ⟨b, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem (T S) x).2 (by simpa [T] using hx)
      exact ⟨.inr (ε.symm b), by simp⟩
  calc
    _ = ∑ S, ‖(Z'.submatrix (enumSubset (T S)) id).det‖ ^ 2 := by
      refine sum_congr rfl fun S _ ↦ ?_
      rw [norm_det_fromCols_one_submatrix e (h_bij S) Z, ← det_submatrix_equiv_self ε]
      simp [Z']
    _ ≤ ∑ U, ‖(Z'.submatrix (enumSubset U) id).det‖ ^ 2 := by
      rw [← sum_image (f := fun U ↦ ‖(Z'.submatrix (enumSubset U) id).det‖ ^ 2) T_inj.injOn]
      exact sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
    -- Cauchy–Binet
    _ = ‖(Z'ᴴ * Z').det‖ := by
      simp [det_mul_eq_sum_minors, ← conjTranspose_submatrix, Complex.mul_conj',
        ← Complex.ofReal_pow, ← Complex.ofReal_sum, abs_sum_of_nonneg]
    -- Hadamard's inequality
    _ ≤ ∏ b, ‖(Z'ᴴ * Z') b b‖ := hadamard_det_inequality (posSemidef_conjTranspose_mul_self Z')
    _ = ∏ b : c, ∑ x : L, ‖Z x b‖ ^ 2 := by
      refine (Fintype.prod_equiv ε _ _ fun b ↦ ?_).symm
      simp [Z', mul_apply, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
        abs_of_nonneg (sum_nonneg fun x _ ↦ sq_nonneg ‖Z x b‖)]

end New

end MinorExpansions

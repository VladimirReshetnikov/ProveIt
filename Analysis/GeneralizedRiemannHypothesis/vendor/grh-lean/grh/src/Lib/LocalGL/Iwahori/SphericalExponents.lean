import Lib.LocalGL.Iwahori.HeckeDegrees

/-!
# Exponents that survive on spherical vectors, and a Hecke operator on parahoric eigenvectors

Let `F` be a field with a valuation in `ℤᵐ⁰` and compact ring of integers `𝒪`, with maximal ideal
`𝔭`, uniformiser `ϖ` and residue field of order `q`, and let `K0 = New.proIwahori` be the pro-`p`
Iwahori subgroup of `GL_N(𝒪)`. An exponent is a linear form that is an eigenform for the torus
character `New.torusChar θ = ∏ θ_i(t_i) |t_i| ^ (N - 1 - i)`. This file proves that a non-zero
exponent for `New.torusChar θ` with unramified `θ_i` and non-increasing `|θ_i(ϖ)|` is non-zero on
the vectors fixed by `GL_N(𝒪)`. The proof uses orbit sums for the parahoric subgroups
`P = New.blockParahoric (min m)`, whose columns before `m` lie in `𝔭` below the diagonal, and the
permutation matrices `New.permGL`. For `F` the completion of a number field at a finite place, it
also shows that the Hecke operator of `diag (ϖ, 1, …, 1)` keeps the `New.proIwahori`-fixed
eigenvectors, with eigenvalue depending only on the top left entry, of the stabiliser of a line,
`New.blockParahoric (min 1)`, the matrices in `GL_N(𝒪)` whose first column is in `𝔭` below the
corner.

## Main definitions and results

* `New.Patching.parahoricEigenspace`: for a level function `f` and a function `c` on the group, the
  vectors fixed by `New.proIwahori` on which each `k` in the parahoric subgroup of `f` acts by the
  scalar `c k`.
* `New.Patching.parahoricEigenspace_mem_invtSubmodule`: the Hecke operator of `diag (ϖ, 1, …, 1)`
  keeps this space when `f = min 1` and `c` is a function of the top left entry.
* `New.IsExponent.eq_zero_of_eq_zero_on_spherical`: if `l ≠ 0`, the `θ_i` are unramified and
  `|θ_i(ϖ)|` is non-increasing in `i`, then `l` is non-zero on the vectors fixed by `GL_N(𝒪)`.

Notions from other files:
* `New.blockParahoric`: For a level function b on the indices, the g in GL_N(𝒪) with g_ij in the
  maximal ideal whenever b(j) < b(i).
* `New.IsExponent`: For a character ξ of the torus, the linear form l satisfies l(ρ(t) · mean of x
  over K0) = ξ(t) l(x) for all x and all dominant t.
* `New.heckeCoset`: The Hecke operator of the double coset KgK: the sum of ρ(h) over chosen
  representatives h of the cosets hK in KgK.
* `New.compactMean`: The mean of ρ(h)x over h in a compact subgroup H, for a smooth ρ.

## Relation to the literature

Known result: exponents, U-operators and spherical vectors at pro-p Iwahori level. Here the group is
GL_n at pro-p Iwahori level with tame characters, and eigenforms of the operators U_t on fixed
vectors replace Jacquet modules. No regularity is assumed and ties between roots are allowed.
Source: Casselman, The unramified principal series of p-adic groups I, Compositio 40 (1980), Prop.
2.4, 2.5, 3.6; Haines–Kottwitz–Prasad, Iwahori–Hecke algebras (arXiv math/0309168) §1.
-/

noncomputable section

/-!
## Orbit sums for a parahoric subgroup

* `New.exists_v_entry_eq_one_of_mem_intGL`: a matrix of `GL_N(𝒪)` and its inverse have unit entries
  in matching positions of a column and a row.
* `New.sum_by_last_nonzero_coord`: the count of residue vectors by their last non-zero coordinate.
* `New.exists_compactMean_and_swap_eq_sum`: vectors whose values under an Iwahori-invariant form are
  explicit sums over the translates of `x` by the swaps `(m j)`.
-/

namespace New

open Matrix Valued Finset Equiv IsLocalRing WithZero Function

attribute [local instance low] Fintype.ofFinite

variable {F : Type*} [Field F] [Valued F ℤᵐ⁰] {N : ℕ} {ρ : Rep ℂ (GL (Fin N) F)}
  {m : Fin N} {x : ρ} {φ : ρ →ₗ[ℂ] ℂ}

/-- For `k` in `GL_N(𝒪)` there is an index `r` such that the entries `k r m` and `k⁻¹ m r` are both
units. -/
lemma exists_v_entry_eq_one_of_mem_intGL {k : GL (Fin N) F} (hk : k ∈ intGL (Fin N) 𝒪[F])
    (m : Fin N) :
    ∃ r : Fin N, v (k⁻¹ m r) = 1 ∧ v (k r m) = 1 := by
  -- The diagonal entry `∑ r, k⁻¹ m r * k r m` of `k⁻¹ * k` is 1, so not all of its terms, products
  -- of two integral elements, lie in the maximal ideal; one outside it has unit factors.
  by_contra h
  have h_term_lt (r : Fin N) : v (k⁻¹ m r * k r m) < 1 := by
    grind [mem_intGL, mul_lt_of_lt_of_le_one, v.mem_integer_iff]
  have h_lt : v (∑ r, k⁻¹ m r * k r m) < 1 := v.map_sum_lt' one_pos fun r _ ↦ h_term_lt r
  have h_sum : ∑ r, k⁻¹ m r * k r m = 1 := by rw [← mul_apply, k.inv_mul, one_apply_eq]
  rw [h_sum, map_one] at h_lt
  exact lt_irrefl 1 h_lt

open scoped Classical in
/-- Let `q` be the order of `𝓀[F]`, let indices run over `0, …, N−1`, and let `j(c)` be the last
non-zero coordinate of `c`. The sum of `a (j(c))` over the `c ∈ 𝓀[F]^N` that are non-zero on `I`
with `j(c) ≥ m` equals `∑ q^{j+1} (1 − 1/q)^{|I ∪ {j}|} a j` over the `j ≥ m` that bound `I` from
above. -/
lemma sum_by_last_nonzero_coord [CompactSpace 𝒪[F]] (a : Fin N → ℂ) (I : Finset (Fin N)) :
    letI q : ℂ := Nat.card 𝓀[F]
    ∑ c : Fin N → 𝓀[F] with ∀ s ∈ I, c s ≠ 0, ∑ j ≥ m with c j ≠ 0 ∧ ∀ r > j, c r = 0, a j =
      ∑ j : Fin N with m ≤ j ∧ I ⊆ Iic j,
        q ^ N * ((1 - q⁻¹) ^ #(insert j I) / q ^ #(Ioi j)) * a j := by
  -- Sum first over `j`. The vectors `c` with last non-zero coordinate `j` and non-zero on `I` form
  -- the box `∏ r, allowed j r` if `j` bounds `I`, and there are none otherwise.
  set q : ℂ := ↑(Nat.card 𝓀[F])
  let allowed (j r : Fin N) : Finset 𝓀[F] := {a | (r ∈ insert j I → a ≠ 0) ∧ (r ∈ Ioi j → a = 0)}
  refine (sum_comm' (s' := fun j ↦ Fintype.piFinset (allowed j)) (by grind)).trans
    (sum_congr rfl fun j hj ↦ ?_)
  -- a coordinate has `q - 1` values on `insert j I`, one value after `j`, and `q` values elsewhere
  have card_allowed (r : Fin N) : (#(allowed j r) : ℂ) =
      q * ((if r ∈ insert j I then 1 - q⁻¹ else 1) / if r ∈ Ioi j then q else 1) := by
    split_ifs with h_insert h_Ioi h_Ioi
    · grind
    · simp_all [q, allowed, mul_sub, ← card_subtype, NeZero.one_le, -mem_Ioi]
    · simp_all [q, allowed, ← card_subtype, -mem_Ioi]
    · simp_all [q, allowed, -mem_Ioi]
  simp only [sum_const, nsmul_eq_mul, Fintype.card_piFinset, Nat.cast_prod,
    card_allowed, prod_mul_distrib, prod_div_distrib, prod_ite_mem_eq, prod_const, card_fin]

/-- For `m ≤ j` the permutation matrix of the swap `(m j)` lies in `blockParahoric (min m)`: it
only moves indices from `m` on, which all have the level `m`. -/
private lemma permGL_swap_mem_blockParahoric_min {j : Fin N} (hj : m ≤ j) :
    permGL (swap m j) ∈ blockParahoric (F := F) (min m) := by
  refine ⟨permGL_mem_intGL _, ?_⟩
  simp
  grind [one_pos]

/-- The group of level `update (min m) m N` lies in `blockParahoric (min m)`. -/
private lemma mem_blockParahoric_min_of_mem_update {k : GL (Fin N) F}
    (hk : k ∈ blockParahoric (update (min m) m N)) : k ∈ blockParahoric (min m) := by
  grind

/-- An element of the group of level `update (min m) m N` has row `m` in `𝔭` off the diagonal. -/
private lemma v_apply_lt_one_of_mem_blockParahoric_update {k : GL (Fin N) F}
    (hk : k ∈ blockParahoric (update (min m) m N)) {r : Fin N} (hr : r ≠ m) : v (k m r) < 1 := by
  grind

/-- Reduction modulo `𝔭` on `blockParahoric (min m)`, a homomorphism to `GL_N(𝓀[F])`. -/
private def reduceParahoric (m : Fin N) :
    blockParahoric (F := F) (N := N) (min m) →* GL (Fin N) 𝓀[F] :=
  (intGL.map (residue _)).comp ((blockParahoric (F := F) (N := N) (min m)).inclusion fun _ h ↦ h.1)

/-- Column `m` of the reduction modulo `𝔭` of an element of `blockParahoric (min m)`. -/
private def residueCol (m : Fin N) (p : blockParahoric (F := F) (N := N) (min m)) : Fin N → 𝓀[F] :=
  (reduceParahoric m p).val.col m

/-- Column `m` of a product: the reduction of `k` times column `m` of the reduction of `p` is column
`m` of the reduction of `k * p`. -/
private lemma reduceParahoric_mulVec_residueCol (k p : blockParahoric (F := F) (N := N) (min m)) :
    reduceParahoric m k *ᵥ residueCol m p = residueCol m (k * p) := by
  ext i
  simp [residueCol, map_mul, mulVec, dotProduct, mul_apply]

/-- Let `x` be fixed by the `p ∈ blockParahoric (min m)` with column `m` in `𝔭` off the diagonal.
Then `ρ u x` depends only on column `m` of `u` modulo `𝔭`. -/
private lemma apply_eq_of_residueCol_eq
    (hx : ∀ p ∈ blockParahoric (min m), (∀ r ≠ m, v (p r m) < 1) → ρ p x = x)
    {u t : blockParahoric (F := F) (N := N) (min m)} (h_eq : residueCol m u = residueCol m t) :
    ρ u x = ρ t x := by
  -- `t⁻¹ * u` has column `m` congruent to that of `1`, so it fixes `x`.
  have h_col_eq : residueCol m (t⁻¹ * u) = residueCol m 1 := by
    rw [← reduceParahoric_mulVec_residueCol, h_eq, reduceParahoric_mulVec_residueCol,
      inv_mul_cancel]
  have h_col (r : Fin N) (hr : r ≠ m) : v ((t⁻¹ * u).val r m) < 1 := by
    simpa [residueCol, reduceParahoric, hr, ← ZeroMemClass.zero_def, Subgroup.inclusion] using
      congrFun h_col_eq r
  have h_fix : ρ (t⁻¹ * u).val x = x := hx _ (t⁻¹ * u).property h_col
  simpa [Representation.inv_apply_eq_iff] using h_fix

/-- The vector `ρ p x` at `c = residueCol m p`, and `0` at the `c` that are not of this form. -/
private def colVector (m : Fin N) (x : ρ) : (Fin N → 𝓀[F]) → ρ :=
  (residueCol m).extend (fun p ↦ ρ p x) 0

/-- At column `m` of the reduction of `p`, `colVector m x` is `ρ p x`. -/
private lemma colVector_residueCol
    (hx : ∀ p ∈ blockParahoric (min m), (∀ r ≠ m, v (p r m) < 1) → ρ p x = x)
    (p : blockParahoric (F := F) (N := N) (min m)) :
    colVector m x (residueCol m p) = ρ p x :=
  Function.FactorsThrough.extend_apply (fun _ _ h_eq ↦ apply_eq_of_residueCol_eq hx h_eq) _ p

private lemma colVector_eq_zero_of_not_exists {c : Fin N → 𝓀[F]}
    (hc : ¬∃ p : blockParahoric (F := F) (N := N) (min m), residueCol m p = c) :
    colVector m x c = 0 :=
  Function.extend_apply' _ _ c hc

/-- Let `c` be a column of integers whose entry `c j` is a unit and whose entries below `j` lie in
`𝔭`. The identity matrix with column `j` replaced by `c` lies in the Iwahori subgroup
`blockParahoric (min N)`. -/
private lemma exists_mem_blockParahoric_updateCol {c : Fin N → 𝒪[F]} {j : Fin N}
    (hc_unit : 1 ≤ v (c j : F)) (hc_below : ∀ r > j, v (c r : F) < 1) :
    ∃ u : GL (Fin N) F, u ∈ blockParahoric (min N) ∧
      u.val = updateCol (1 : Matrix (Fin N) (Fin N) F) j (fun r : Fin N ↦ (c r : F)) := by
  refine ⟨.mk'' (updateCol (1 : Matrix (Fin N) (Fin N) F) j (fun r ↦ (c r : F))) ?_, ?_, rfl⟩
  · -- the determinant is `c j`, which is not `0`
    simpa [← cramer_apply, Matrix.one_apply] using
      show c j ≠ 0 from fun h_zero ↦ by simp [h_zero] at hc_unit
  · -- the entries below the diagonal are `0`, or entries of `c` below `j`
    simp [mem_blockParahoric, mem_intGL_iff_det, -ZeroMemClass.coe_eq_zero, ← cramer_apply,
      updateCol_apply, Matrix.one_apply]
    grind [one_pos, v.mem_integer_iff]

open scoped Classical in
/-- Suppose `x` is fixed by every `p` in `blockParahoric (min m)` (entries `p i j` with
`j < min i m` in the maximal ideal) whose column `m` off the diagonal lies in the maximal ideal
(`hx`), and `φ` is invariant under the Iwahori subgroup `blockParahoric (min N)` (`hφ`). For a
residue-field column `c`, `colVector m x c` is `ρ p x` when `c = residueCol m p`, and `0` when `c`
has no such form. Then `φ (colVector m x c)` depends only on the last non-zero coordinate `j` of
`c`: it is `φ (ρ (permGL (swap m j)) x)` if `j ≥ m`, and `0` if `c` vanishes from `m` on. -/
private lemma map_colVector_eq_sum
    (hx : ∀ p ∈ blockParahoric (min m), (∀ r ≠ m, v (p r m) < 1) → ρ p x = x)
    (hφ : ∀ k ∈ blockParahoric (min N), ∀ z : ρ, φ (ρ k z) = φ z) (c : Fin N → 𝓀[F]) :
    φ (colVector m x c) =
      ∑ j ≥ m with c j ≠ 0 ∧ ∀ r > j, c r = 0, φ (ρ (permGL (swap m j)) x) := by
  classical
  by_cases! h_vanish : ∀ r ≥ m, c r = 0
  · -- Column `m` of `p ∈ blockParahoric (min m)` has a unit entry in a row `r ≥ m`: take `r`
    -- with `p⁻¹ m r` and `p r m` units; `r < m` is excluded as `p⁻¹ ∈ blockParahoric (min m)`.
    have not_column : ¬∃ p, residueCol m p = c := fun ⟨p, hp⟩ ↦ by
      simp [← hp, residueCol, reduceParahoric, Subgroup.inclusion] at h_vanish
      grind [exists_v_entry_eq_one_of_mem_intGL (mem_blockParahoric.mp p.property).left m,
        mem_blockParahoric.mp (inv_mem p.property)]
    grind [colVector_eq_zero_of_not_exists, sum_eq_zero]
  obtain ⟨c, rfl⟩ : ∃ c' : Fin N → 𝒪[F], residue _ ∘ c' = c := residue_surjective.comp_left c
  obtain ⟨j, hj, j_max⟩ := exists_maximal_of_wellFoundedGT _ h_vanish
  -- In terms of `v`: `c j` is a unit, and `j` is the last index `≥ m` with this property.
  simp only [Function.comp_apply, ne_eq, residue_eq_zero_iff_valuation_lt_one, not_lt] at hj j_max ⊢
  obtain ⟨hj_ge, hj_unit⟩ := hj
  have h_below : ∀ r > j, v (c r : F) < 1 := by grind
  -- `c` is column `m` of `u * swap m j`, where `u` is the unit matrix with column `j` replaced
  -- by `c`, an element of the Iwahori group.
  obtain ⟨u, hu_mem, hu_val⟩ := exists_mem_blockParahoric_updateCol hj_unit h_below
  have column : residue _ ∘ c = residueCol m
      (⟨u, by grind⟩ * ⟨_, permGL_swap_mem_blockParahoric_min hj_ge⟩) := by
    simp [funext_iff, residueCol, reduceParahoric, hu_val, PEquiv.mul_toMatrix_toPEquiv]
  rw [column, colVector_residueCol hx, sum_eq_single j (by grind) (by grind)]
  simpa using hφ u hu_mem (ρ (permGL (swap m j)) x)

/-- `blockParahoric (min m)` permutes the vectors `colVector m x c` through its action on the
columns `c`. -/
private lemma apply_colVector
    (hx : ∀ p ∈ blockParahoric (min m), (∀ r ≠ m, v (p r m) < 1) → ρ p x = x)
    (k : blockParahoric (F := F) (N := N) (min m)) (c : Fin N → 𝓀[F]) :
    ρ k (colVector m x c) = colVector m x (reduceParahoric m k *ᵥ c) := by
  obtain ⟨p, rfl⟩ | h_none := _root_.em (∃ p, residueCol m p = c)
  · simp [reduceParahoric_mulVec_residueCol, colVector_residueCol hx]
  · -- no column is `reduceParahoric m k *ᵥ c` either: else the column of `k⁻¹ * p` would be `c`
    have h_not : ¬∃ p, residueCol m p = reduceParahoric m k *ᵥ c := fun ⟨p, hp⟩ ↦
      h_none ⟨k⁻¹ * p, by simp [← reduceParahoric_mulVec_residueCol, hp]⟩
    rw [colVector_eq_zero_of_not_exists h_none, colVector_eq_zero_of_not_exists h_not, map_zero]

variable [CompactSpace 𝒪[F]]

open scoped Classical in
/-- Let row `i` of the reduction of `k` be supported in column `a`, for every `a ∈ I`. Then `ρ k`
carries the sum of the `colVector m x c` (`ρ p x` if `c` is column `m` mod `𝔭` of
`p ∈ blockParahoric (min m)`, else `0`) over the `c` that are non-zero on `I` to the sum over the
`c` that are non-zero at `i` (over all `c` if `I` is empty). -/
private lemma apply_sum_colVector
    (hx : ∀ p ∈ blockParahoric (min m), (∀ r ≠ m, v (p r m) < 1) → ρ p x = x)
    (k : blockParahoric (F := F) (N := N) (min m)) (I : Finset (Fin N)) (i : Fin N)
    (h_row : ∀ a ∈ I, ∀ r ≠ a, reduceParahoric m k i r = 0) :
    ρ k (∑ c : Fin N → 𝓀[F] with ∀ s ∈ I, c s ≠ 0, colVector m x c) =
      ∑ c : Fin N → 𝓀[F] with ∀ s ∈ I.image (fun _ ↦ i), c s ≠ 0, colVector m x c := by
  -- Write `κ k` for the reduction of `k`. If row `i` of `κ k` is supported in column `a`, then
  -- `(κ k *ᵥ c) i ≠ 0 ↔ c a ≠ 0`; the entry at `a` is not `0` since `κ k` is invertible.
  have entry (a : Fin N) (ha : a ∈ I) (c : Fin N → 𝓀[F]) :
      (reduceParahoric m k *ᵥ c) i = 0 ↔ c a = 0 := by
    have h_entry_ne : reduceParahoric m k i a ≠ 0 := by
      grind [(reduceParahoric m k).det_ne_zero, det_eq_zero_of_row_eq_zero i]
    rw [mulVec, dotProduct, sum_eq_single a] <;> grind
  simp only [map_sum, apply_colVector hx]
  refine sum_equiv (reduceParahoric m k).toLin.toLinearEquiv ?_ fun _ _ ↦ rfl
  simp
  grind

/-- Let `F` be a field valued in `ℤᵐ⁰` with compact `𝒪[F]`, `ρ` a smooth representation of
`GL_N(F)`, `φ : ρ →ₗ[ℂ] ℂ`, `m : Fin N`, `P = blockParahoric (min m)` (the `p` in `GL_N(𝒪)` with
`p i j ∈ 𝔭` whenever `j < i` and `j < m`), and `x : ρ` fixed by the `p ∈ P` with column `m` in `𝔭`
off the diagonal, and `φ` invariant under the Iwahori group `blockParahoric (min N)`. For `q` the
order of `𝓀[F]` and `a j = (q - 1) q ^ j φ (ρ (permGL (swap m j)) x)` there are `y` and `z`, `z`
fixed by the `p ∈ P` with row `m` in `𝔭` off the diagonal, with (a) `φ` of the mean of `y` over `P`
equal to `∑_{j ≥ m} a j`; (b) `φ (ρ (permGL (swap m i)) z) = a i + (1 - 1 / q) ∑_{j > i} a j` for
`i ≥ m`. -/
lemma exists_compactMean_and_swap_eq_sum [IsSmoothRep ρ.ρ]
    (hx : ∀ p ∈ blockParahoric (min m), (∀ r ≠ m, v (p r m) < 1) → ρ p x = x)
    (hφ : ∀ k ∈ blockParahoric (min N), ∀ z : ρ, φ (ρ k z) = φ z) :
    let q : ℂ := Nat.card 𝓀[F]
    let a (j : Fin N) : ℂ :=
      q ^ N * ((1 - q⁻¹) / q ^ j.rev.val) * φ (ρ (permGL (Equiv.swap m j)) x)
    ∃ y : ρ, ∃ z ∈ levelSpace ρ.ρ (blockParahoric (update (min m) m N)),
      -- (a) the value of the mean of `y`
      φ (compactMean ρ.ρ (blockParahoric (min m)) y) = ∑ j ≥ m, a j ∧
      -- (b) the values of the swapped vectors `z`
      ∀ i ≥ m, φ (ρ (permGL (Equiv.swap m i)) z) = (1 - q⁻¹) * ∑ j > i, a j + a i := by
  classical
  -- For `p` in `P` the vector `ρ p x` depends only on column `m` of `p` modulo `𝔭`
  -- (`colVector`). Take for `y` the sum of all `colVector m x c`, and for `z` the sum over the `c`
  -- with `c m ≠ 0`; count them by their last non-zero coordinate.
  let Y (I : Finset (Fin N)) : ρ := ∑ c with ∀ s ∈ I, c s ≠ 0, colVector m x c
  let q : ℂ := Nat.card 𝓀[F]
  have φ_Y (I : Finset (Fin N)) : φ (Y I) = ∑ j with m ≤ j ∧ I ⊆ Iic j,
      q ^ N * ((1 - q⁻¹) ^ #(insert j I) / q ^ #(Ioi j)) * φ (ρ (permGL (swap m j)) x) := by
    simpa only [Y, map_sum, map_colVector_eq_sum hx hφ] using sum_by_last_nonzero_coord _ I
  refine ⟨Y ∅, Y {m}, mem_levelSpace.mpr fun k ↦ ?_, ?_, fun i hi ↦ ?_⟩
  · -- the group of level `update (min m) m N` lies in `P` and fixes `Y {m}`
    have hk_mem : k.val ∈ blockParahoric (min m) := mem_blockParahoric_min_of_mem_update k.property
    have h_row (r : Fin N) (hr : r ≠ m) : reduceParahoric m ⟨k.val, hk_mem⟩ m r = 0 := by
      simpa [reduceParahoric] using v_apply_lt_one_of_mem_blockParahoric_update k.property hr
    simpa [Y] using apply_sum_colVector hx ⟨k.val, hk_mem⟩ {m} m (by simpa using h_row)
  · -- `Y ∅` is fixed by `P`, so the mean over `P` does not change it.
    have fixed : Y ∅ ∈ levelSpace ρ.ρ (blockParahoric (min m)) :=
      mem_levelSpace.mpr fun k ↦ by simpa [Y] using apply_sum_colVector hx k ∅ m (by simp)
    simp [compactMean_eq_self _ fixed, φ_Y, q, tsub_tsub, add_comm, filter_le_eq_Ici]
  · -- The swap carries `Y {m}` to `Y {i}`; split off the term `j = i` of the count.
    let s : blockParahoric (F := F) (N := N) (min m) :=
      ⟨permGL (swap m i), permGL_swap_mem_blockParahoric_min hi⟩
    have h_row (r : Fin N) (hr : r ≠ m) : reduceParahoric m s i r = 0 := by
      simp [s, reduceParahoric, hr.symm]
    have swap_Y : ρ (permGL (swap m i)) (Y {m}) = Y {i} := by
      simpa [Y, s] using apply_sum_colVector hx s {m} i (by simpa using h_row)
    have indices : ({j | m ≤ j ∧ {i} ⊆ Iic j} : Finset (Fin N)) = Ici i := by grind
    rw [swap_Y, φ_Y, indices, ← sum_Ioi_add_eq_sum_Ici, mul_sum]
    -- For `j > i` the set `{j, i}` has two elements, which gives one more factor `1 - q⁻¹`.
    congr! 2 with j hj
    · rw [show #(insert j {i}) = 2 from card_pair (mem_Ioi.mp hj).ne']
      simp [q, tsub_tsub, add_comm]
      ring
    · simp [q, tsub_tsub, add_comm]

end New

/-!
## A Hecke operator on eigenvectors of the stabiliser of a line

* `New.Patching.exists_clear_first_row`: one element of `New.proIwahori` clears the first row of a
  matrix in this stabiliser.
* `New.Patching.conj_diagGL_mulSingle_zero_mem_blockParahoric`: if the first row of a matrix of this
  stabiliser is cleared, its conjugate by `diag (ϖ, 1, …, 1)` lies in the stabiliser.
* `New.Patching.parahoricEigenspace_mem_invtSubmodule`: the Hecke operator of `diag (ϖ, 1, …, 1)`
  keeps the `proIwahori`-fixed vectors on which the stabiliser acts through a function of the top
  left entry.
-/

section HeckeOnLineStabiliser

open Valued WithZero Matrix Subgroup Pi

namespace New.Patching

variable {E : Type*} [Field E] [NumberField E] {w : FinPlace E} {N : ℕ} [NeZero N]
  {g : GL (Fin N) (LocField w)} (ρ : Rep ℂ (GL (Fin N) (LocField w))) [IsSmoothRep ρ.ρ]

/-- One row operation clears the first row: if `g` lies in `blockParahoric (min 1)`, some `u` in
`proIwahori` makes the first row of `u * g` vanish off the corner. -/
lemma exists_clear_first_row (hg : g ∈ blockParahoric (min 1)) :
    ∃ u ∈ proIwahori, ∀ j ≠ (0 : Fin N), (u * g :) 0 j = 0 := by
  obtain ⟨hg_int, hg_below_small⟩ := mem_blockParahoric.mp hg
  have h_int (j : Fin N) : v (g⁻¹ 0 j) ≤ 1 := (v.mem_integer_iff _).mp (hg_int.isIntMatrix_inv 0 j)
  -- some `g⁻¹ 0 r` and `g r 0` are both units, and `g r 0` is not a unit for `r ≠ 0`
  have h_unit : v (g⁻¹ 0 0) = 1 := by grind [exists_v_entry_eq_one_of_mem_intGL hg_int 0]
  have h_ne : g⁻¹ 0 0 ≠ 0 := by grind [one_ne_zero]
  -- `u` is the identity with first row replaced by that of `g⁻¹`, scaled to have corner entry `1`
  let u : Matrix (Fin N) (Fin N) (LocField w) := updateRow 1 0 ((g⁻¹ 0 0)⁻¹ • g⁻¹ 0)
  have hu : IsUnit u.det := by simpa [u, ← cramer_transpose_apply] using h_ne
  refine ⟨.mk'' u hu, ?_, fun j hj ↦ ?_⟩
  · -- `-coe_units_inv` keeps the entries of `g⁻¹` in the form of `h_unit` and `h_int`
    simp [u, mem_proIwahori, h_unit, Matrix.one_apply, apply_ite v, updateRow_apply, -coe_units_inv]
    grind [one_pos, sub_self]
  · -- the first row of `u g` is a multiple of the first row of `g⁻¹ g = 1`
    simp [u, updateRow_mul, smul_vecMul, ← mul_apply_eq_vecMul, hj.symm]

/-- The vectors fixed by the pro-p Iwahori group on which each `k` in the parahoric subgroup of the
level function `f` acts by the scalar `c k`. -/
noncomputable def parahoricEigenspace (f : ℕ → ℕ) (c : GL (Fin N) (LocField w) → ℂ) :
    Submodule ℂ ρ :=
  levelSpace ρ.ρ proIwahori ⊓
    { carrier := {z : ρ | ∀ k ∈ blockParahoric f, ρ k z = c k • z}
      add_mem' := by simp_all
      zero_mem' := by simp
      smul_mem' := by simp_all [smul_comm (c _)] }

/-- For a uniformiser `ϖ` and `t = diag (ϖ, 1, …, 1)`: if `m` lies in `blockParahoric (min 1)` and
its first row vanishes off the corner, then `t⁻¹ * m * t` lies in `blockParahoric (min 1)`. -/
lemma conj_diagGL_mulSingle_zero_mem_blockParahoric {ϖ : (LocField w)ˣ} (hϖ : v ϖ.val = exp (-1))
    {m : GL (Fin N) (LocField w)} (hm : m ∈ blockParahoric (min 1)) (h_row : ∀ j ≠ 0, m 0 j = 0) :
    (diagGL (mulSingle 0 ϖ))⁻¹ * m * diagGL (mulSingle 0 ϖ) ∈ blockParahoric (min 1) := by
  -- conjugation by `t` only scales row `0` and column `0`, and row `0` of `m` is cleared
  set d : Fin N → (LocField w)ˣ := mulSingle 0 ϖ
  have h_log_le (a b : Fin N) : m a b = 0 ∨
      (v (d b).val).log + (if min 1 (b : ℕ) < min 1 (a : ℕ) then 1 else 0) ≤
        (v (d a).val).log + if min 1 (b : ℕ) < min 1 (a : ℕ) then 1 else 0 := by
    grind [Units.val_one, log_one, log_exp]
  simpa using (conj_monomial_mem_blockParahoric d 1 ⊤ ⟨hm, fun _ ↦ trivial⟩ h_log_le).left

/-- For a uniformiser `ϖ` (`v ϖ = exp (-1)`) and `t = diag (ϖ, 1, …, 1)`, the Hecke operator of the
double coset of `t` under `proIwahori` keeps `parahoricEigenspace ρ (min 1) (χ ∘ (· 0 0))`. This
space consists of the `proIwahori`-fixed vectors on which each `k` in the parahoric subgroup of the
level function `min 1` acts by the scalar `χ (k 0 0)`. That parahoric is the `k` in `GL_N(𝒪)` with
`k i 0` in the maximal ideal for `i ≠ 0`. -/
lemma parahoricEigenspace_mem_invtSubmodule {ϖ : (LocField w)ˣ} (hϖ : v ϖ.val = exp (-1))
    {χ : LocField w → ℂ} :
    let t : GL (Fin N) (LocField w) := diagGL (mulSingle 0 ϖ)
    parahoricEigenspace ρ (min 1) (χ ∘ fun k : GL (Fin N) (LocField w) ↦ k 0 0) ∈
      (heckeCoset ρ.ρ proIwahori t).invtSubmodule := by
  -- Up to a scalar, `heckeCoset ρ.ρ proIwahori t y` is the mean of `ρ t y` over `proIwahori`. This
  -- is also the mean over the stabiliser `S` of `y` in the parahoric subgroup
  -- `blockParahoric (min 1)`, and we compute the action of the parahoric subgroup on that mean.
  intro t y ⟨hy_fixed, (hy : ∀ k ∈ blockParahoric (min 1), ρ k y = χ (k 0 0) • y)⟩
  have h_fix : ∀ u ∈ proIwahori, ρ u y = y := fun u hu ↦ by simpa using hy_fixed ⟨u, hu⟩
  set P : Subgroup (GL (Fin N) (LocField w)) := blockParahoric (min 1)
  have h_le : proIwahori ≤ P := proIwahori_le_blockParahoric (by omega)
  let Stab : Subgroup (GL (Fin N) (LocField w)) := (MulAction.stabilizer _ y).comap ρ.ρ.toHomUnits
  let S : Subgroup (GL (Fin N) (LocField w)) := P ⊓ Stab
  -- the stabiliser of `y` is open, so closed, and the parahoric subgroup is compact
  have hS_compact : CompactSpace S :=
    isCompact_iff_compactSpace.mp <| isCompact_residuePreimage.inter_right <|
      isClosed_of_isOpen Stab (isOpen_of_mem_nhds Stab (IsSmoothRep.eventually_fixed y))
  -- the parahoric subgroup acts on `y` by scalars, so it conjugates `proIwahori` into `S`
  have h_conj (k g : GL (Fin N) (LocField w)) (hk : k ∈ P) (hg : g ∈ proIwahori) :
      k⁻¹ * g * k ∈ S := by
    have h_eq : ρ g (ρ k y) = ρ k y := by simp [hy k hk, h_fix g hg]
    have h_stab : ρ (k⁻¹ * g * k) y = y := by simp [h_eq]
    exact ⟨P.mul_mem (P.mul_mem (P.inv_mem hk) (h_le hg)) hk, h_stab⟩
  -- if the first row of `m` is cleared, then `t⁻¹ * m * t` is again parahoric, with the same
  -- first entry; so both act on `y` by the same scalar
  have h_comm (m : GL (Fin N) (LocField w)) (hm : m ∈ P) (h_row : ∀ j ≠ 0, m 0 j = 0) :
      ρ m (ρ t y) = ρ t (ρ m y) := by
    have h_conj_mem : t⁻¹ * m * t ∈ P := conj_diagGL_mulSingle_zero_mem_blockParahoric hϖ hm h_row
    have h_entry : (t⁻¹ * m * t) 0 0 = m 0 0 := by simp [t, ← map_inv, mul_comm]
    calc ρ m (ρ t y) = ρ t (ρ (t⁻¹ * m * t) y) := by simp
      _ = ρ t (ρ m y) := by rw [hy _ h_conj_mem, hy _ hm, h_entry]
  have h_apply_mean (k : GL (Fin N) (LocField w)) (hk : k ∈ P) :
      ρ k (compactMean ρ.ρ S (ρ t y)) = compactMean ρ.ρ proIwahori (ρ t (ρ k y)) :=
    calc _ = compactMean ρ.ρ proIwahori (ρ k (compactMean ρ.ρ S (ρ t y))) := by
          -- the vector is fixed by `proIwahori`, since `k⁻¹ * g * k ∈ S` for `g ∈ proIwahori`
          refine (compactMean_eq_self _ fun g ↦ ?_).symm
          simpa [Representation.inv_apply_eq_iff] using
            apply_compactMean (ρ := ρ.ρ) (h_conj k g hk g.prop) (ρ t y)
      _ = compactMean ρ.ρ proIwahori (ρ t (ρ k y)) := by
          -- for `g ∈ S`, clear the first row of `k * g` by a `u ∈ proIwahori` and move it past `t`
          refine map_compactMean_of_const (compactMean ρ.ρ proIwahori ∘ₗ ρ.ρ k)
            fun g ⟨hg, (hgy : ρ g y = y)⟩ ↦ ?_
          obtain ⟨u, hu, h_row⟩ := exists_clear_first_row (mul_mem hk hg)
          have h_move : ρ (u * (k * g)) (ρ t y) = ρ t (ρ (u * (k * g)) y) :=
            h_comm _ (mul_mem (h_le hu) (mul_mem hk hg)) h_row
          simpa [hu, hgy, hy k hk, h_fix u hu] using congrArg (compactMean ρ.ρ proIwahori) h_move
  have h_avg : compactMean ρ.ρ S (ρ t y) = compactMean ρ.ρ proIwahori (ρ t y) := by
    simpa using h_apply_mean 1 (one_mem _)
  -- so a parahoric `k` multiplies the mean over `proIwahori` by `χ (k 0 0)`
  have h_eigen (k : GL (Fin N) (LocField w)) (hk : k ∈ P) :
      ρ k (compactMean ρ.ρ proIwahori (ρ t y)) =
        χ (k 0 0) • compactMean ρ.ρ proIwahori (ρ t y) := by
    simpa [h_avg, hy k hk] using h_apply_mean k hk
  -- `proIwahori` fixes the mean, and the Hecke operator is `w.q ^ (N - 1)` times it
  rw [Submodule.mem_comap, (heckeCoset_mulSingle_zero_eq (ρ := ρ.ρ) hϖ hy_fixed).right]
  exact Submodule.smul_mem _ _ ⟨compactMean_mem_levelSpace _, h_eigen⟩

end New.Patching

end HeckeOnLineStabiliser

/-!
## Unramified sorted exponents on spherical vectors

The proof descends from `GL_N(𝒪)` to the Iwahori group through the parahoric groups
`New.blockParahoric (min m)`, using the vectors built in `New.exists_compactMean_and_swap_eq_sum`.
-/

section SphericalExponent

open WithZero Valued Finset Equiv Pi Function

/-- Let `p` lie in the parahoric subgroup `blockParahoric (min m)`, with column `m` in `𝔭` off the
diagonal, and let `b = diag (1, …, ϖ⁻¹, …, 1)` with `ϖ⁻¹` at `m`, for a uniformiser `ϖ`. Then
`b⁻¹ p b` lies in the parahoric subgroup `blockParahoric (update (min m) m N)`, whose row `m` lies
in `𝔭` off the diagonal. -/
lemma New.conj_diagGL_mulSingle_mem_blockParahoric {F : Type*} [Field F] [Valued F ℤᵐ⁰]
    [CompactSpace 𝒪[F]] {N : ℕ} {m : Fin N} {ϖ : Fˣ} (hϖ : v ϖ.val = exp (-1))
    {p : GL (Fin N) F} (hp : p ∈ blockParahoric (min (m : ℕ)))
    (hp_col : ∀ r ≠ m, v (p r m) < 1) :
    (diagGL (mulSingle m ϖ⁻¹))⁻¹ * p * diagGL (mulSingle m ϖ⁻¹) ∈
      blockParahoric (update (min (m : ℕ)) m N) := by
  -- `p` lies in the parahoric of the level function that is `min i m + 1` off `m` and `0` at `m`;
  -- conjugation by `b` multiplies row `m` by `ϖ` and divides column `m` by `ϖ`.
  let c : ℕ → ℕ := update (min (m : ℕ)) m N
  let c' : ℕ → ℕ := update (fun i : ℕ ↦ min i m + 1) m 0
  set d : Fin N → Fˣ := mulSingle m ϖ⁻¹ with hd
  have hp_level : p ∈ blockParahoric c' := by grind
  have h_log_le (a b : Fin N) : p a b = 0 ∨
      log (v (d b).val) + (if c b < c a then 1 else 0) ≤
        log (v (d a).val) + if c' b < c' a then 1 else 0 := by
    simp [c, c', hd, apply_ite (α := Fˣ), apply_ite v, apply_ite log, hϖ, mulSingle_apply,
      update_apply]
    lia
  simpa using (conj_monomial_mem_blockParahoric d 1 ⊤ ⟨hp_level, fun _ ↦ trivial⟩ h_log_le).left

/-- For an exponent `l` of character `torusChar θ`, a vector `z` fixed by the parahoric subgroup
`blockParahoric (update (min m) m N)` and `b = diag (1, …, ϖ⁻¹, …, 1)` with `ϖ⁻¹` at `m`, one has
`l ((m i) b z) = θ_i(ϖ)⁻¹ q ^ (N - 1 - i) l ((m i) z)`. Here `(m i)` is the permutation matrix
`permGL (Equiv.swap m i)` and `q` is the order of the residue field. -/
lemma New.IsExponent.apply_swap_diagGL_mulSingle {F : Type*} [Field F] [Valued F ℤᵐ⁰]
    [CompactSpace 𝒪[F]] {N : ℕ} {ρ : Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ] {ϖ : Fˣ}
    {θ : Fin N → Fˣ →* ℂˣ} {l : ρ →ₗ[ℂ] ℂ} (hl : IsExponent ρ (torusChar θ) l)
    (hϖ : v ϖ.val = exp (-1)) {m : Fin N} {z : ρ}
    (hz : z ∈ levelSpace ρ.ρ (blockParahoric (update (min (m : ℕ)) m N))) (i : Fin N) :
    l (ρ (permGL (Equiv.swap m i)) (ρ (diagGL (mulSingle m ϖ⁻¹)) z)) =
      (θ i ϖ).val⁻¹ * (Nat.card 𝓀[F] : ℂ) ^ i.rev.val * l (ρ (permGL (Equiv.swap m i)) z) := by
  -- `(m i) b = diag (mulSingle i ϖ⁻¹) (m i)`, which `apply_monomial_translate` evaluates.
  set t : Fin N → Fˣ := mulSingle i ϖ⁻¹
  set σ : Perm (Fin N) := Equiv.swap m i
  have h_val_le (a b : Fin N) (h_lt : σ b < σ a) : v (t (σ b)).val ≤ v (t (σ a)).val ∨
      update (min (m : ℕ)) m N a ≤ update (min (m : ℕ)) m N b ∧
        v (t (σ b)).val ≤ v (t (σ a)).val * exp 1 := by
    simp +decide [t, σ, apply_ite, ite_apply, hϖ, mulSingle_apply, update_apply]
    grind
  have h_prod : permGL σ * diagGL (mulSingle m ϖ⁻¹) = diagGL t * permGL σ := by
    simp [t, σ, diagGL_mul_permGL, mulSingle_comp_equiv]
  have h_char : (torusChar θ t : ℂ) = (θ i ϖ).val⁻¹ * (Nat.card 𝓀[F] : ℂ) ^ i.rev.val := by
    simp [t, hϖ, normAbsChar]
  rw [← Module.End.mul_apply, ← map_mul, h_prod, ← h_char]
  exact hl.apply_monomial_translate hϖ hz And.left σ h_val_le

/-- The descent step, for an exponent `(torusChar θ, l)` with `‖θ_i(ϖ)‖` non-increasing in `i`. Let
`l` be Iwahori-invariant and vanish on the averages over the parahoric `P = blockParahoric (min m)`,
and let `x` be fixed by the `p ∈ P` whose column `m` lies in `𝔭` off the diagonal. Write `(m i)` for
the permutation matrix `permGL (Equiv.swap m i)`. If `l ((m i) x) = 0` for all `i ≥ j` (where
`j : Fin (N + 1)`, so that `j = N` asks nothing), then `l x = 0`. -/
lemma New.IsExponent.eq_zero_of_apply_permGL_swap_eq_zero {F : Type*} [Field F] [Valued F ℤᵐ⁰]
    [CompactSpace 𝒪[F]] {N : ℕ} {ρ : Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ] {ϖ : Fˣ}
    {θ : Fin N → Fˣ →* ℂˣ} {l : ρ →ₗ[ℂ] ℂ} (hl : IsExponent ρ (torusChar θ) l)
    (hϖ : v ϖ.val = exp (-1)) (hθ_anti : Antitone fun i : Fin N ↦ ‖(θ i ϖ).val‖)
    (h_invariant : ∀ k ∈ blockParahoric (min N), ∀ z : ρ, l (ρ k z) = l z) {m : Fin N}
    (h_mean_eq_zero : ∀ y : ρ, l (compactMean ρ.ρ (blockParahoric (min m)) y) = 0)
    (j : Fin (N + 1)) (x : ρ)
    (hx : ∀ p ∈ blockParahoric (min m), (∀ r ≠ m, v (p r m) < 1) → ρ p x = x)
    (h_swap : ∀ i : Fin N, j ≤ i.castSucc → l (ρ (permGL (Equiv.swap m i)) x) = 0) :
    l x = 0 := by
  -- Induction on `j`. Write `l_i = l ∘ (m i)`. From `x` one builds `x'` of the same kind, killed
  -- by one more `l_i`; then `l x' = 0` and `l x ≠ 0` force `θ_j(ϖ) = q θ_m(ϖ)`, against `hθ_anti`.
  induction j using Fin.induction generalizing x with
  | zero => simpa [← Perm.one_def] using h_swap m bot_le
  | succ j ih =>
    by_contra h_ne
    have hmj : m ≤ j :=
      le_of_not_gt fun h_lt ↦ h_ne (by simpa [← Perm.one_def] using h_swap m (by grind))
    -- Put `a i = (q - 1) q ^ i l_i x`. There are an average over `P` on which `l` is
    -- `∑_{i ≥ m} a i`, and a vector `z` fixed by the `p ∈ P` with row `m` in `𝔭` off the diagonal,
    -- with `l_i z = a i + (1 - 1 / q) ∑_{i' > i} a i'` for `i ≥ m`.
    set q : ℂ := ↑(Nat.card 𝓀[F]) with hq
    let a (i : Fin N) : ℂ := q ^ N * ((1 - q⁻¹) / q ^ i.rev.val) * l (ρ (permGL (Equiv.swap m i)) x)
    obtain ⟨y, z, hz, hy_sum, hz_sum⟩ :
        ∃ y : ρ, ∃ z ∈ levelSpace ρ.ρ (blockParahoric (update (min m) m N)),
          l (compactMean ρ.ρ (blockParahoric (min m)) y) = ∑ i ≥ m, a i ∧
          ∀ i ≥ m, l (ρ (permGL (Equiv.swap m i)) z) = (1 - q⁻¹) * ∑ i' > i, a i' + a i :=
      exists_compactMean_and_swap_eq_sum hx h_invariant
    have hq_lt : 1 < Nat.card 𝓀[F] := Finite.one_lt_card
    have hq_zero : q ≠ 0 := Nat.cast_ne_zero.mpr hq_lt.ne_bot
    have hq_one : q - 1 ≠ 0 := by simpa [hq, sub_eq_zero] using hq_lt.ne'
    let b : GL (Fin N) F := diagGL (mulSingle m ϖ⁻¹)
    have h_shift (i : Fin N) : l (ρ (permGL (Equiv.swap m i)) (ρ b z)) =
        (θ i ϖ).val⁻¹ * q ^ i.rev.val * l (ρ (permGL (Equiv.swap m i)) z) :=
      hl.apply_swap_diagGL_mulSingle hϖ hz i
    let x' : ρ := (θ j ϖ).val • ρ b z - q ^ N • (1 - q⁻¹) • x
    -- Conjugation by `b⁻¹` carries the group fixing `x` into the group fixing `z`.
    have hx' (p : GL (Fin N) F) (hp : p ∈ blockParahoric (min m))
        (hp_col : ∀ r ≠ m, v (p r m) < 1) : ρ p x' = x' := by
      simpa [x', b, hx p hp hp_col, Representation.inv_apply_eq_iff] using
        hz ⟨b⁻¹ * p * b, New.conj_diagGL_mulSingle_mem_blockParahoric hϖ hp hp_col⟩
    -- For `i ≥ j` the terms beyond `i` vanish; the two parts of `l_i x'` cancel if `i = j` and are
    -- both zero if `i > j`.
    have h_swap' (i : Fin N) (hi : j.castSucc ≤ i.castSucc) :
        l (ρ (permGL (Equiv.swap m i)) x') = 0 := by
      have h_beyond : ∑ i' > i, a i' = 0 :=
        sum_eq_zero fun i' hi' ↦ by simp [a, h_swap i' (by grind)]
      have hz_i : l (ρ (permGL (Equiv.swap m i)) z) = a i := by
        rw [hz_sum i (hmj.trans hi), h_beyond, mul_zero, zero_add]
      obtain rfl | h_lt : j = i ∨ j < i := j.eq_or_lt_of_le hi
      · simp [x', h_shift, hz_i, a, field]
      · simp [x', h_shift, hz_i, a, h_swap i h_lt]
    have hx'_zero :
        (θ j ϖ).val * l (ρ (permGL (Equiv.swap m m)) (ρ b z)) = q ^ N * ((1 - q⁻¹) * l x) := by
      simpa [x', sub_eq_zero, ← Perm.one_def] using ih x' hx' h_swap'
    -- By `h_mean_eq_zero` the terms beyond `m` add up to `-a m`, so `l z = a m / q`.
    have hz_m : l (ρ (permGL (Equiv.swap m m)) z) = a m / q := by
      rw [h_mean_eq_zero y, ← sum_Ioi_add_eq_sum_Ici, eq_comm, add_eq_zero_iff_eq_neg] at hy_sum
      rw [hz_sum m le_rfl, hy_sum]
      ring
    -- Both sides of `hx'_zero` are now multiples of `q ^ N * (1 - 1 / q) * l x ≠ 0`.
    have h_root : θ j ϖ = q * θ m ϖ := by
      rw [h_shift, hz_m] at hx'_zero
      simp only [a, swap_self, ← Perm.one_def, map_one, Module.End.one_apply] at hx'_zero
      field_simp at hx'_zero
      grind
    simpa [h_root, hq, hq_lt.not_ge] using hθ_anti hmj

/-- Let `l` be an exponent of the smooth representation `ρ` with character `torusChar θ`. That is,
`l` is `proIwahori`-invariant and `l (ρ t x) = ∏ i, θ i (t i) |t i| ^ (N - 1 - i) · l x` for
`proIwahori`-fixed `x` and dominant diagonal `t`. Assume all `θ i` are trivial on the units of `𝒪`
and `‖θ i ϖ‖` is non-increasing in `i` for the uniformiser `ϖ`. If `l` vanishes on the vectors fixed
by `GL_N(𝒪)`, then `l` is zero: a converse to the fact that spherical representations have a sorted
exponent of unramified characters.

This is a form, in terms of exponents, of one direction of the description of spherical
representations of `GL_N` in the Langlands–Zelevinsky classification: a nonzero sorted unramified
exponent forces a spherical vector. -/
lemma New.IsExponent.eq_zero_of_eq_zero_on_spherical {F : Type*} [Field F] [Valued F ℤᵐ⁰]
    [CompactSpace 𝒪[F]] {N : ℕ} {ρ : Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ] {ϖ : Fˣ}
    {θ : Fin N → Fˣ →* ℂˣ} {l : ρ →ₗ[ℂ] ℂ} {x : ρ} (hϖ : v ϖ.val = exp (-1))
    (hl : IsExponent ρ (torusChar θ) l)
    (hθ_unit : ∀ y : Fˣ, v y.val = 1 → ∀ i : Fin N, (θ i y).val = 1)
    (hθ_anti : Antitone fun i : Fin N ↦ ‖(θ i ϖ).val‖)
    (h_sph : ∀ y ∈ levelSpace ρ.ρ (intGL (Fin N) 𝒪[F]), l y = 0) :
    l x = 0 := by
  -- `l` is invariant under the Iwahori group `blockParahoric (min N)`: an element of it is a
  -- diagonal matrix of units times a pro-`p` Iwahori element, and `θ` is trivial on units.
  have h_invariant (k : GL (Fin N) F) (hk : k ∈ blockParahoric (min N)) (z : ρ) :
      l (ρ k z) = l z := by
    have hk_int : k ∈ intGL (Fin N) 𝒪[F] := (mem_blockParahoric.mp hk).left
    have h_val_diag (i : Fin N) : v (k i i) = 1 := by
      grind [exists_v_entry_eq_one_of_mem_intGL hk_int i, inv_mem hk, one_pos]
    have h_diag_ne (i : Fin N) : k i i ≠ 0 := fun h_zero ↦ by simpa [h_zero] using h_val_diag i
    let d (i : Fin N) : Fˣ := (Units.mk0 (k i i) (h_diag_ne i))⁻¹
    have h_dk_mem : diagGL d * k ∈ proIwahori := by
      simp_all [d, mem_intGL_iff_det, mem_proIwahori_iff_blockParahoric, mem_blockParahoric]
    -- `θ` is trivial on the unit entries of `d`, so `diagGL d` does not change the values of `l`
    have h_char_d : (torusChar θ d : ℂ) = 1 := by
      simp [d, torusChar, monoidHomMulEquiv, hθ_unit, h_val_diag, normAbsChar]
    calc l (ρ k z) = l (ρ (diagGL d) (ρ k z)) := by
          rw [hl.apply_diagGL_unit (by simp [d, h_val_diag]), h_char_d, one_mul]
      _ = l (ρ (diagGL d * k) z) := by rw [map_mul, Module.End.mul_apply]
      _ = l z := hl.apply_proIwahori _ h_dk_mem z
  -- By induction on `m`, `l` vanishes on the averages over each parahoric `blockParahoric (min m)`.
  have h_mean_eq_zero (m : Fin (N + 1)) (y : ρ) :
      l (compactMean ρ.ρ (blockParahoric (min m)) y) = 0 := by
    induction m using Fin.induction generalizing y with
    | zero => simp_all [mem_blockParahoric]
    | succ m ih =>
      -- There is no `i ≥ N`, so at `j = N` the descent step assumes no vanishing. The `p` in
      -- `blockParahoric (min m)` with column `m` in `𝔭` off the diagonal lie in
      -- `blockParahoric (min (m + 1))`, so they fix the mean.
      refine hl.eq_zero_of_apply_permGL_swap_eq_zero hϖ hθ_anti h_invariant ih (.last N) _ ?_
        (by simp)
      grind [New.apply_compactMean]
  rw [← map_compactMean_of_const l fun k hk ↦ h_invariant k hk x]
  exact h_mean_eq_zero (Fin.last N) x

end SphericalExponent

end

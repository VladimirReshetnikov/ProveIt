import Lib.DiscreteSeries.Holomorphic.HighestVectorExtension

/-!
# Integrals of densities over unitary groups and over the flag variety of `K_ℂ`

We study integrals over unitary groups `G = U(diag ε)` (`New.USign ε`) of functions that are
continuous on invertible matrices and transform under triangular matrices by the modulus character.
Here `New.IsBorelMatrix o b` says that `b` is invertible and upper triangular for the order `o`, `B`
denotes these triangular matrices, `New.diagChar (New.twoRho o _) b = ∏ i, b i i ^ (2ρ) i`, and `o`
is assumed injective. Integrals of such functions over `G` become integrals over an open part of
`U(n)`, and their integral over `U(n)` is invariant under left translation by invertible matrices.
As a consequence, a continuous function on the invertible block diagonal matrices `K_ℂ` that obeys
the same rule block by block has an integral over `K` that is invariant under `K_ℂ`.

## Main definitions and results

* `New.openOrbit`: the set `G B` of products of an element of `G` and a triangular matrix.
* `New.IsFlagDensity`: the transformation rule under triangular matrices.
* `New.integral_mul_left_eq_setIntegral_openOrbit`: the integral over `G` of a translate
  `F (x * g)` equals the integral over the part of `U(n)` in `x G B`.
* `New.integral_unitary_mul_left_of_density`: the integral over `U(n)` of such a function is
  invariant under left translation by an invertible matrix.
* `New.integral_haarK_mul_left_of_density`: the same for densities on `K_ℂ`, integrated over `K`.

Notions from other files:
* `New.USign ε`: the unitary group `U(J)` of the diagonal matrix of signs `J = New.signMatrix ε`.
* `New.twoRho l r`: the sum of the roots selected by `r` that are positive for `l`; its `i`-th entry
  is `#{j | r i j ∧ l j < l i} - #{j | r i j ∧ l i < l j}`.
* `New.lowerLiePart ε 1 o 2⁻¹`: the projection `X ↦ N - J Nᴴ J` to the Lie algebra of `U(J)`, where
  `N` is the part of `X` below the diagonal plus half its diagonal. `New.skewOfReal y` is the
  skew-Hermitian matrix with real coordinates `y`; `New.skewCoords` reads them back (real plus
  imaginary part over `√2` off the diagonal).
* `New.maxCompactU ε`, `New.haarK ε`: the group `K` of the elements of `U(J)` that commute with `J`,
  and its Haar measure of mass one.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Character.FormalDegree` and
`Lib.DiscreteSeries.FlenstedJensen.PsiKTypes` for sources.
-/

namespace New

/-!
## The open orbit of U(p,q) on flags and change of variables

* `New.lintegral_openOrbit_le`: an inequality between integrals over two unitary groups, each
  restricted to a translate of an open orbit.

The inequality holds for any two signatures, so using it both ways gives an equality.
-/

section OpenFlagOrbit

open Matrix MeasureTheory Complex ComplexOrder Norms.L2Operator LinearMap Finset U

variable {n : Type} [Fintype n] [DecidableEq n] {o : n → ℤ} {b c : Matrix n n ℂ}

/-- The set `G B` of matrices `g * b` with `g` in `U(diag ε)` and `b` invertible and upper
triangular for the order `o`: the preimage of an open orbit of `G` on flags. -/
def openOrbit (ε : n → ℤˣ) (o : n → ℤ) : Set (Matrix n n ℂ) :=
  {y : Matrix n n ℂ | ∃ g : USign ε, ∃ b : Matrix n n ℂ, IsBorelMatrix o b ∧ y = g * b}

/-- The function `F` on matrices is a density on the flags of the order `o`:
`F (y * b) = |∏ i, b i i ^ (2ρ) i| ^ 2 • F y` for `y` invertible and `b` invertible and upper
triangular for `o`, where `2ρ = twoRho o ⊤`. The matrices `b` are upper triangular in the order of
increasing `o`, so this `2ρ` is minus the sum of the roots of the triangular group. -/
def IsFlagDensity {E : Type*} [SMul ℝ E] (o : n → ℤ) (F : Matrix n n ℂ → E) : Prop :=
  ∀ (y : GL n ℂ) (b : Matrix n n ℂ), IsBorelMatrix o b →
    F (y * b) = ‖diagChar (twoRho o ⊤) b‖ ^ 2 • F y

/-- Uniqueness of the factorisation. Let `o` be injective. If `g * b = g' * c` with `g`, `g'` in
`U(diag ε)`, `b`, `c` triangular and all ratios `c i i / b i i` positive reals, then `g = g'`. -/
lemma IsBorelMatrix.unitary_eq_of_mul_eq (ho : o.Injective) (ε : n → ℤˣ) {g g' : USign ε}
    (hb : IsBorelMatrix o b) (hc : IsBorelMatrix o c) (h_eq : g * b = g' * c)
    (h_pos : ∀ i : n, 0 < c i i / b i i) : g = g' := by
  -- Write `g = g' * t`. Then `t = c * b⁻¹` is triangular and in the group, hence diagonal with
  -- entries `exp (θ i * I)` of norm one; these are the positive numbers `c i i / b i i`.
  obtain ⟨t, rfl⟩ : ∃ t : USign ε, g' * t = g := mul_left_surjective g' g
  obtain rfl : t * b = c := by simpa [mul_assoc] using h_eq
  have ht : IsBorelMatrix o t := by simpa [hb.right] using hc.mul hb.inv
  obtain ⟨θ, hθ⟩ : ∃ θ : n → ℝ, (t : Matrix n n ℂ) = diagonal fun i : n ↦ cexp (θ i * I) :=
    ht.exists_eq_diagonal_exp ho
  have h_one (i : n) : cexp (θ i * I) = 1 := by
    simpa [hθ, hb.diag_ne_zero ho] using eq_coe_norm_of_nonneg (h_pos i).le
  exact Subtype.ext (Units.ext (by simp [hθ, h_one]))

/-- Let `o` be injective and `b` triangular. If `y` vanishes at all entries further below the
diagonal than `(i, j)`, then conjugation by `b` multiplies the entry `(i, j)` of `y` by
`b i i * b⁻¹ j j`. -/
lemma IsBorelMatrix.mul_mul_inv_apply (ho : o.Injective) (hb : IsBorelMatrix o b)
    {y : Matrix n n ℂ} {i j : n} (hy : ∀ k l : n, o i - o j < o k - o l → y k l = 0) :
    (b * y * b⁻¹) i j = b i i * y i j * b⁻¹ j j := by
  simp_rw [mul_apply, sum_mul, ← sum_product']
  refine sum_eq_single_of_mem (j, i) (by simp) fun ⟨l, k⟩ _ h_ne ↦ ?_
  -- An outer factor vanishes unless `o i ≤ o k` and `o l ≤ o j`; in that case `y k l` vanishes.
  have b_tri : o k < o i → b i k = 0 := fun h ↦ hb.left h
  have inv_tri : o j < o l → b⁻¹ l j = 0 := fun h ↦ hb.inv.left h
  have h_further : o i ≤ o k → o l ≤ o j → o i - o j < o k - o l := by grind [Function.Injective]
  change b i k * y k l * b⁻¹ l j = 0
  grind

/-- Let `o` be injective and `J = diag ε`. The real coordinates (`skewCoords`: real plus imaginary
part, divided by `√2` off the diagonal) of `J * (N - J Nᴴ J)`, where `N` is the part of `Z` below
the diagonal plus half its diagonal, in terms of the entries of `Z` on and below the diagonal. -/
lemma skewCoords_signMatrix_mul_lowerLiePart_apply (ho : o.Injective) (ε : n → ℤˣ)
    (Z : Matrix n n ℂ) (i j : n) :
    skewCoords (signMatrix ε * lowerLiePart ε 1 o 2⁻¹ Z) i j =
      if o j < o i then ε i * ((Z i j).re + (Z i j).im) / √2
      else if o i < o j then ε j * ((Z j i).im - (Z j i).re) / √2
      else ε i * (Z i i).im := by
  -- With `N` the part of `Z` below the diagonal plus half its diagonal, the matrix is
  -- `J * (N - J * Nᴴ * J) = J * N - Nᴴ * J`. In each case we compute its entry `(i, j)`.
  have h_sign : (ε i * ε i : ℂ) = 1 := by exact_mod_cast Int.units_coe_mul_self (ε i)
  rcases lt_trichotomy (o i) (o j) with h_lt | h_eq | h_gt
  · have h_ne : i ≠ j := ne_of_apply_ne o h_lt.ne
    have h_entry : (signMatrix ε * lowerLiePart ε 1 o 2⁻¹ Z) i j = -(star (Z j i) * ε j) := by
      simp [lowerLiePart, signMatrix, h_lt, h_lt.not_gt, h_ne.symm, h_ne, ← mul_assoc, h_sign]
    simp [skewCoords, h_entry, h_lt, h_lt.not_gt, h_ne, field, neg_add_eq_sub]
  · obtain rfl : i = j := ho h_eq
    have h_entry : (signMatrix ε * lowerLiePart ε 1 o 2⁻¹ Z) i i = ε i * (Z i i).im * I := by
      simp [lowerLiePart, signMatrix, mul_sub, ← mul_assoc, h_sign, im_eq_sub_conj, field]
    simp [skewCoords, h_entry]
  · have h_ne : i ≠ j := ne_of_apply_ne o h_gt.ne'
    have h_entry : (signMatrix ε * lowerLiePart ε 1 o 2⁻¹ Z) i j = ε i * Z i j := by
      simp [lowerLiePart, signMatrix, h_gt, h_gt.not_gt, h_ne.symm, h_ne]
    simp [skewCoords, h_entry, h_gt, h_ne, mul_add]

section

omit [Fintype n]

/-- Off the diagonal, the coordinate `y i j` is read off from the entry `(i, j)` of
`skewOfReal y`. -/
lemma re_add_im_skewOfReal_div (y : Matrix n n ℝ) {i j : n} (h_ne : i ≠ j) :
    ((skewOfReal y i j).re + (skewOfReal y i j).im) / √2 = y i j := by
  simp [skewOfReal, h_ne, ← add_div, div_div]

/-- Off the diagonal, the coordinate `y i j` is read off from the entry `(j, i)` of
`skewOfReal y`. -/
lemma im_sub_re_skewOfReal_swap_div (y : Matrix n n ℝ) {i j : n} (h_ne : i ≠ j) :
    ((skewOfReal y j i).im - (skewOfReal y j i).re) / √2 = y i j := by
  simp [skewOfReal, h_ne.symm, ← sub_div, div_div]

lemma im_skewOfReal_diag (y : Matrix n n ℝ) (i : n) : (skewOfReal y i i).im = y i i := by
  simp [skewOfReal]

end

omit [DecidableEq n] in
/-- Let `o` be injective and `d` a vector with nonzero entries. The product over all pairs
`(i, j)` of the ratio of `d` at the later index to `d` at the earlier index is
`(∏ i, d i ^ (2ρ) i) ^ 2`, where `2ρ = twoRho o ⊤`. -/
lemma prod_prod_ite_div_eq_prod_zpow_twoRho_sq (ho : o.Injective) {d : n → ℝ}
    (hd : ∀ i : n, d i ≠ 0) :
    (∏ i : n, ∏ j : n, if o i < o j then d j / d i else d i / d j) =
      (∏ i : n, d i ^ twoRho o ⊤ i) ^ 2 := by
  let r (i j : n) : ℝ := (if o j < o i then d i else 1) / if o i < o j then d i else 1
  have h_row (i : n) : d i ^ twoRho o ⊤ i = ∏ j : n, r i j := by
    simp [r, twoRho, zpow_sub₀ (hd i), prod_div_distrib, ← prod_filter]
  have h_pair (i j : n) : (if o i < o j then d j / d i else d i / d j) = r i j * r j i := by
    rcases lt_trichotomy (o i) (o j) with h_lt | h_eq | h_gt
    · simp [r, h_lt, h_lt.not_gt, div_eq_inv_mul]
    · simp [r, hd, ho h_eq]
    · simp [r, h_gt, h_gt.not_gt, div_eq_mul_inv]
  calc _ = (∏ i : n, ∏ j : n, r i j) * ∏ i : n, ∏ j : n, r j i := by
        simp only [h_pair, prod_mul_distrib]
    _ = (∏ i : n, ∏ j : n, r i j) ^ 2 := by rw [sq, prod_comm (f := fun i j : n ↦ r j i)]
    _ = (∏ i : n, d i ^ twoRho o ⊤ i) ^ 2 := by simp only [h_row]

/-- The Jacobian. Let `o` be injective, `b` triangular with positive diagonal, `J = diag ε`,
`J' = diag ε'`. Take a skew-Hermitian `Y` (real coordinates `New.skewOfReal`), conjugate `J' * Y` by
`b`, and project to the Lie algebra of `U(J)` by `New.lowerLiePart ε 1 o 2⁻¹`, the map
`X ↦ N - J Nᴴ J` with `N = lowerMask 1 o X` plus half the diagonal of `X`. Then multiply by `J` and
read off coordinates by `New.skewCoords`. The determinant of this real linear map has absolute value
`|∏ i, b i i ^ (2ρ) i| ^ 2`, where `(2ρ) i = #{j | o j < o i} - #{j | o i < o j}`. -/
lemma abs_det_lowerLiePart (ho : o.Injective) (ε : n → ℤˣ) (hb : IsBorelMatrix o b)
    (h_pos : ∀ i : n, 0 < b i i) (ε' : n → ℤˣ) :
    |(skewCoords ∘ₗ mulLeft ℝ (signMatrix ε) ∘ₗ lowerLiePart ε 1 o 2⁻¹ ∘ₗ
        mulLeftRight ℝ (b, b⁻¹) ∘ₗ mulLeft ℝ (signMatrix ε') ∘ₗ skewOfReal).det| =
      ‖diagChar (twoRho o ⊤) b‖ ^ 2 := by
  -- Order the pairs `(i, j)` first by their distance `|o i - o j|` from the diagonal. Conjugation
  -- by `b` multiplies an entry by `b i i / b j j` and adds only entries further below the diagonal,
  -- so the matrix `T` of the map is triangular, and we multiply its diagonal entries.
  let key (p : n × n) : ℤ ×ₗ ℤ ×ₗ ℤ := toLex (|o p.1 - o p.2|, toLex (o p.1, o p.2))
  have key_inj : key.Injective := fun p q h_key ↦ by simp_all [key, ho.eq_iff, Prod.ext_iff]
  let pairOrder : LinearOrder (n × n) := .lift' key key_inj
  have h_real (i : n) : ∃ d : ℝ, 0 < d ∧ (d : ℂ) = b i i := RCLike.pos_iff_exists_ofReal.1 (h_pos i)
  choose d hd_pos hd using h_real
  rw [← det_toMatrix (stdBasis ℝ n n)]
  set T : Matrix (n × n) (n × n) ℝ := toMatrix (stdBasis ℝ n n) (stdBasis ℝ n n) _ with hT_def
  -- Column `q` of `T` holds the coordinates of the image of `Z q = b * (J' * Y q) * b⁻¹`.
  let Y (q : n × n) : Matrix n n ℂ := skewOfReal (Matrix.single q.1 q.2 1)
  let Z (q : n × n) : Matrix n n ℂ := b * (signMatrix ε' * Y q) * b⁻¹
  have T_apply (p q : n × n) :
      T p q = skewCoords (signMatrix ε * lowerLiePart ε 1 o 2⁻¹ (Z q)) p.1 p.2 := by
    simp [hT_def, Z, Y, toMatrix_apply, stdBasis, single_eq_of_single_single]
  have Z_apply (q : n × n) (i j : n) (h_dist : |o q.1 - o q.2| ≤ o i - o j) :
      Z q i j = (ε' i * d i / d j : ℝ) * Y q i j := by
    have h_zero (k l : n) (h_further : o i - o j < o k - o l) : (signMatrix ε' * Y q) k l = 0 := by
      have h_ne : ¬(q.1 = k ∧ q.2 = l) ∧ ¬(q.1 = l ∧ q.2 = k) := by grind
      simp [Y, signMatrix, skewOfReal, Matrix.single_apply, h_ne]
    calc Z q i j = b i i * (signMatrix ε' * Y q) i j * b⁻¹ j j := hb.mul_mul_inv_apply ho h_zero
      _ = _ := by simp [signMatrix, hb.inv_apply_diag ho, hd, field]
  -- The entries of `T` on and below its diagonal.
  let x (i j : n) : ℝ := ε i * (ε' i * d i / d j)
  have hT (i j : n) (q : n × n) (hq : q ≤ (i, j)) :
      T (i, j) q = (if o i < o j then x j i else x i j) * Matrix.single q.1 q.2 1 i j := by
    have h_dist : |o q.1 - o q.2| ≤ |o i - o j| := Prod.Lex.monotone_fst _ _ hq
    rw [T_apply, skewCoords_signMatrix_mul_lowerLiePart_apply ho]
    rcases lt_trichotomy (o i) (o j) with h_lt | h_eq | h_gt
    · rw [ite_eq_right h_lt.not_gt, ite_eq_left h_lt, ite_eq_left h_lt, Z_apply q j i (by grind),
        re_ofReal_mul, im_ofReal_mul,
        ← im_sub_re_skewOfReal_swap_div (Matrix.single q.1 q.2 1) (ne_of_apply_ne o h_lt.ne)]
      ring
    · obtain rfl : i = j := ho h_eq
      simp [Z_apply q i i (by simpa using h_dist), Y, im_skewOfReal_diag, x, mul_assoc]
    · rw [ite_eq_left h_gt, ite_eq_right h_gt.not_gt, Z_apply q i j (by grind), re_ofReal_mul,
        im_ofReal_mul, ← re_add_im_skewOfReal_div (Matrix.single q.1 q.2 1)
          (ne_of_apply_ne o h_gt.ne')]
      ring
  have h_tri : T.IsUpperTriangular := fun p q (hq : q < p) ↦ by
    rw [hT p.1 p.2 q hq.le, single_apply_of_ne _ _ _ _ _ (Prod.ext_iff.not.1 hq.ne), mul_zero]
  have h_abs (i j : n) : |T (i, j) (i, j)| = if o i < o j then d j / d i else d i / d j := by
    simp [hT, x, apply_ite abs, abs_div, abs_mul, abs_unit_intCast, abs_of_pos (hd_pos _)]
  calc |T.det| = ∏ i : n, ∏ j : n, if o i < o j then d j / d i else d i / d j := by
        simp only [det_of_isUpperTriangular h_tri, abs_prod, Fintype.prod_prod_type, h_abs]
    _ = (∏ i : n, d i ^ twoRho o ⊤ i) ^ 2 :=
        prod_prod_ite_div_eq_prod_zpow_twoRho_sq ho fun i ↦ (hd_pos i).ne'
    _ = ‖diagChar (twoRho o ⊤) b‖ ^ 2 := by simp [diagChar, ← hd, abs_of_pos (hd_pos _)]

/-- For injective `o`, a point of the open orbit is `g * b` with `g` in `U(diag ε)` and `b`
triangular with positive diagonal. -/
lemma exists_mul_isBorelMatrix_of_mem_openOrbit (ho : o.Injective) (ε : n → ℤˣ) {y : Matrix n n ℂ}
    (hy : y ∈ openOrbit ε o) :
    ∃ g : USign ε, ∃ b : Matrix n n ℂ, IsBorelMatrix o b ∧ (∀ i : n, 0 < b i i) ∧ g * b = y := by
  obtain ⟨g, b, hb, rfl⟩ := hy
  -- Move the phases of the diagonal of `b` into `g`.
  let t : USign ε := diagTorus ε fun i : n ↦
    ⟨‖b i i‖ / b i i, by simp [Submonoid.unitSphere, hb.diag_ne_zero ho]⟩
  have ht : IsBorelMatrix o t := ⟨blockTriangular_diagonal _, GeneralLinearGroup.det_ne_zero t.1⟩
  refine ⟨g * t⁻¹, t * b, ht.mul hb, fun i ↦ ?_, by simp [mul_assoc]⟩
  simp [t, diagTorus, hb.diag_ne_zero ho]

/-- A chart at `1` for the factorisation. There is `ψ` with `ψ 1 = 0` and derivative the identity
at `1` such that each matrix `x` near `1` is `exp (L (ψ x)) * b`, where
`L = lowerLiePart ε 1 o 2⁻¹` takes values in the Lie algebra of `U(diag ε)` and `b` is triangular
with positive diagonal. -/
lemma exists_chart_exp_lowerLiePart_mul_borel (ε : n → ℤˣ) (o : n → ℤ) :
    ∃ ψ : Matrix n n ℂ → Matrix n n ℂ,
      HasFDerivAt ψ (ContinuousLinearMap.id ℝ (Matrix n n ℂ)) 1 ∧ ψ 1 = 0 ∧
      ∀ᶠ x : Matrix n n ℂ in nhds 1, ∃ b : Matrix n n ℂ, IsBorelMatrix o b ∧
        (∀ i : n, 0 < b i i) ∧ x = NormedSpace.exp (lowerLiePart ε 1 o 2⁻¹ (ψ x)) * b := by
  set L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := lowerLiePart ε 1 o 2⁻¹
  have L_lower (Z : Matrix n n ℂ) : lowerMask 1 o (L Z) = lowerMask 1 o Z := by
    simp [L, lowerLiePart, signMatrix]
    grind
  obtain ⟨ψ, ⟨ψ_deriv, ψ_one⟩, chart⟩ :=
    exists_borel_chart 1 o L hasStrictFDerivAt_exp_zero NormedSpace.exp_zero (by simp) L_lower
  have accretive : ∀ᶠ x : Matrix n n ℂ in nhds 1, (1 + ψ x).IsAccretive :=
    ψ_deriv.continuousAt.const_add 1
      (IsAccretive.setOf_mem_nhds (by simp [ψ_one, PosDef.one.isAccretive]))
  refine ⟨ψ, ψ_deriv, ψ_one, (chart.and accretive).mono fun x ⟨hx, x_accretive⟩ ↦ ?_⟩
  obtain ⟨tri, -, x_eq⟩ := hx (by simp)
  refine ⟨1 + (1 - L) (ψ x), tri, fun i ↦ ?_, x_eq⟩
  -- The diagonal of `1 + (1 - L) (ψ x)` is the real part of that of `1 + ψ x`.
  simpa [L, lowerLiePart, lt_def, ← two_mul, signMatrix, mul_right_comm, ← Int.cast_mul]
    using x_accretive.diag_pos

/-- The set `openOrbit ε o = G B` is a neighbourhood of each of its points. -/
lemma openOrbit_mem_nhds (ε : n → ℤˣ) {y : Matrix n n ℂ} (hy : y ∈ openOrbit ε o) :
    openOrbit ε o ∈ nhds y := by
  obtain ⟨g, c, hc, rfl⟩ := hy
  obtain ⟨ψ, -, -, chart⟩ := exists_chart_exp_lowerLiePart_mul_borel ε o
  -- Carry the chart at `1` to `g * c` by the map `A` that takes `g * c` to `1`.
  let A : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := .mulLeftRight ℝ _ (g : Matrix n n ℂ)⁻¹ c⁻¹
  have A_tendsto : Filter.Tendsto A (nhds (g * c)) (nhds 1) :=
    A.cont.tendsto' (g * c) 1 (by simp [A, hc.2])
  filter_upwards [A_tendsto.eventually chart] with x ⟨b, hb, _, A_x⟩
  let u : USign ε := expU ⟨_, lowerLiePart_mem_unitaryLie ε 1 o 2⁻¹ (ψ (A x))⟩
  refine ⟨g * u, b * c, hb.mul hc, ?_⟩
  calc x = g * A x * c := by simp [A, mul_assoc, hc.2]
    _ = (g * u : USign ε) * (b * c) := by
      rw [A_x]
      simp [u, mul_assoc]

/-- Let `o` be injective and `y = Φ y * B y` for `y` in the open orbit, with `Φ y` in `U(diag ε)`
and `B y` triangular with positive diagonal. Then at each point `y` of the orbit `Φ` has the
derivative `Z ↦ Φ y * L ((Φ y)⁻¹ * Z * (B y)⁻¹)`, where `L = lowerLiePart ε 1 o 2⁻¹`. -/
lemma hasFDerivAt_unitary_factor_of_mem_openOrbit (ho : o.Injective) (ε : n → ℤˣ)
    {Φ : Matrix n n ℂ → USign ε} {B : Matrix n n ℂ → Matrix n n ℂ}
    (tri : ∀ y ∈ openOrbit ε o, IsBorelMatrix o (B y))
    (pos : ∀ y ∈ openOrbit ε o, ∀ i : n, 0 < B y i i) (factor : ∀ y ∈ openOrbit ε o, Φ y * B y = y)
    {y : Matrix n n ℂ} (hy : y ∈ openOrbit ε o) :
    HasFDerivAt (fun x : Matrix n n ℂ ↦ (Φ x : Matrix n n ℂ))
      ((Φ y : Matrix n n ℂ) • lowerLiePart ε 1 o 2⁻¹ ∘L
        ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (Φ y : Matrix n n ℂ)⁻¹ (B y)⁻¹) y := by
  obtain ⟨ψ, ψ_deriv, ψ_one, chart⟩ := exists_chart_exp_lowerLiePart_mul_borel ε o
  set L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := lowerLiePart ε 1 o 2⁻¹
  -- Carry the chart at `1` to `y` by the map `A` that takes `y` to `1`.
  let A : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := .mulLeftRight ℝ _ (Φ y : Matrix n n ℂ)⁻¹ (B y)⁻¹
  have A_y : A y = 1 := by simpa [A, (tri y hy).2] using (congrArg A (factor y hy)).symm
  have near : ∀ᶠ x : Matrix n n ℂ in nhds y,
      (Φ x : Matrix n n ℂ) = Φ y * NormedSpace.exp (L (ψ (A x))) := by
    filter_upwards [(A.cont.tendsto' y 1 A_y).eventually chart, openOrbit_mem_nhds ε hy]
      with x ⟨b, tri_b, pos_b, (A_x : A x = NormedSpace.exp (L (ψ (A x))) * b)⟩ hx
    let u : USign ε := expU ⟨L (ψ (A x)), lowerLiePart_mem_unitaryLie ε 1 o 2⁻¹ (ψ (A x))⟩
    have x_eq : Φ x * B x = (Φ y * u : USign ε) * (b * B y) := by
      simpa [factor x hx, A, u, mul_assoc, (tri y hy).2]
        using congrArg ((Φ y : Matrix n n ℂ) * · * B y) A_x
    -- Both factorisations of `x` have positive diagonal, so they agree.
    rw [(tri x hx).unitary_eq_of_mul_eq ho ε (tri_b.mul (tri y hy)) x_eq fun i ↦ ?_]
    · simp [u]
    · simp [tri_b.mul_apply_diag ho (tri y hy), pos_b, pos y hy, pos x hx]
  -- So near `y` the map `Φ` is `Φ y * exp (L (ψ (A x)))`; differentiate.
  have exp_deriv : HasFDerivAt (fun x : Matrix n n ℂ ↦ NormedSpace.exp (L (ψ x))) L (A y) := by
    rw [A_y]
    exact HasFDerivAt.comp 1 (g' := 1) (by simpa [ψ_one] using hasFDerivAt_exp_zero)
      (L.hasFDerivAt.comp 1 ψ_deriv)
  exact ((exp_deriv.comp y A.hasFDerivAt).const_mul (Φ y)).congr_of_eventuallyEq near

lemma isOpen_openOrbit (ε : n → ℤˣ) (o : n → ℤ) : IsOpen (openOrbit ε o) :=
  isOpen_iff_mem_nhds.2 fun _ hy ↦ openOrbit_mem_nhds ε hy

/-- Let `o` be injective and `y = Φ y * B y` for `y` in the open orbit, with `Φ y` in `U(diag ε)`
and `B y` triangular with positive diagonal. Let `c` map real matrices to `U(diag ε')`, be
differentiable at `y`, and let `x * c y` lie in the orbit. Then the Jacobian of `z ↦ Φ (x * c z)` at
`y` (the absolute value of the determinant of the logarithmic derivative
`logDerivU f y v = (f y)ᴴ * J * f' v` (`J` the sign matrix of the group of `f`, `f'` the derivative
of `f` at `y`) in the real coordinates `skewCoords`) is `|∏ i, b i i ^ (2ρ) i| ^ 2` times that of
`c`, where `b = B (x * c y)` and `2ρ = twoRho o ⊤`. -/
lemma abs_det_logDerivU_unitary_factor (ho : o.Injective) {ε ε' : n → ℤˣ}
    {Φ : Matrix n n ℂ → USign ε} {B : Matrix n n ℂ → Matrix n n ℂ}
    (tri : ∀ y ∈ openOrbit ε o, IsBorelMatrix o (B y))
    (pos : ∀ y ∈ openOrbit ε o, ∀ i : n, 0 < B y i i) (factor : ∀ y ∈ openOrbit ε o, Φ y * B y = y)
    (x : GL n ℂ) {c : Matrix n n ℝ → USign ε'} {y : Matrix n n ℝ} (c_diff : DifferentiableAtU c y)
    (hy : (x : Matrix n n ℂ) * c y ∈ openOrbit ε o) :
    |(skewCoords ∘ₗ logDerivU (fun z : Matrix n n ℝ ↦ Φ (x * c z)) y).det| =
      ‖diagChar (twoRho o ⊤) (B (x * c y))‖ ^ 2 * |(skewCoords ∘ₗ logDerivU c y).det| := by
  -- Write `x * c y = u * b`, `J = signMatrix ε`, `J' = signMatrix ε'` and `dc` for the derivative
  -- of `c`. The derivative of `Φ (x * c z)` is `u * L (u⁻¹ * x * dc * b⁻¹)`, and
  -- `u⁻¹ * x * dc = b * J' * logDerivU c y` with `logDerivU c y` skew-Hermitian.
  set L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := lowerLiePart ε 1 o 2⁻¹
  let u : USign ε := Φ (x * c y)
  let b : Matrix n n ℂ := B (x * c y)
  let dc : Matrix n n ℝ →L[ℝ] Matrix n n ℂ := fderiv ℝ (fun z ↦ (c z : Matrix n n ℂ)) y
  have deriv : HasFDerivAt (fun z : Matrix n n ℝ ↦ (Φ (x * c z) : Matrix n n ℂ))
      (((u : Matrix n n ℂ) • L ∘L .mulLeftRight ℝ _ (u : Matrix n n ℂ)⁻¹ b⁻¹) ∘L
        ((x : Matrix n n ℂ) • dc)) y :=
    (hasFDerivAt_unitary_factor_of_mem_openOrbit ho ε tri pos factor hy).comp y
      (f := fun z ↦ (x : Matrix n n ℂ) * c z) (c_diff.hasFDerivAt.const_mul _)
  have x_eq : (x : Matrix n n ℂ) = u * b * (c y : Matrix n n ℂ)⁻¹ := by simp [u, b, factor _ hy]
  have h_log (v : Matrix n n ℝ) : logDerivU (fun z : Matrix n n ℝ ↦ Φ (x * c z)) y v =
      signMatrix ε * L (b * (signMatrix ε' * logDerivU c y v) * b⁻¹) :=
    calc _ = (u : Matrix n n ℂ)ᴴ * signMatrix ε * u * L ((u : Matrix n n ℂ)⁻¹ * (x * dc v) * b⁻¹) :=
        by simp [logDerivU, deriv.fderiv, u, mul_assoc]
      _ = _ := by simp [mem_U.1 u.prop, x_eq, dc, logDerivU, inv_coe_eq_mul_conjTranspose_mul (c y),
        ← mul_assoc]
  have h_comp : skewCoords ∘ₗ logDerivU (fun z : Matrix n n ℝ ↦ Φ (x * c z)) y =
      (skewCoords ∘ₗ mulLeft ℝ (signMatrix ε) ∘ₗ L ∘ₗ mulLeftRight ℝ (b, b⁻¹) ∘ₗ
        mulLeft ℝ (signMatrix ε') ∘ₗ skewOfReal) ∘ₗ skewCoords ∘ₗ logDerivU c y :=
    LinearMap.ext fun v ↦ by simp [h_log, conjTranspose_logDerivU c_diff]
  rw [h_comp, det_comp, abs_mul, abs_det_lowerLiePart ho ε (tri _ hy) (pos _ hy) ε']

/-- Change of variables on flags. Let `o` be injective, `B` its triangular group, `x` invertible and
`f` a real density on flags (it scales under `B` by the modulus character). Then the integral of the
positive part of `f` over `x U(ε') ∩ U(ε) B`, for the Haar measure `volume` of `U(ε')` (in Cayley's
chart `cayleyChart`, the density `cayleyDensity / volU (card n)`, as for every signature) moved by
`x`, is at most that over `U(ε) ∩ x U(ε') B`. -/
lemma lintegral_openOrbit_le (ho : o.Injective) (ε ε' : n → ℤˣ) (x : GL n ℂ) (f : Matrix n n ℂ → ℝ)
    (hf : IsFlagDensity o f) :
    ∫⁻ g : USign ε', (openOrbit ε o).indicator (ENNReal.ofReal ∘ f) (x * g) ≤
      ∫⁻ g : USign ε, {y : Matrix n n ℂ | (x : Matrix n n ℂ)⁻¹ * y ∈ openOrbit ε' o}.indicator
        (ENNReal.ofReal ∘ f) g := by
  -- Factor each `y` of the orbit as `Φ y * B y`, with `B y` triangular with positive diagonal.
  choose! Φ B tri pos factor using fun y : Matrix n n ℂ ↦
    exists_mul_isBorelMatrix_of_mem_openOrbit ho ε (y := y)
  have Φ_eq (y : Matrix n n ℂ) (hy : y ∈ openOrbit ε o) : y * (B y)⁻¹ = Φ y := by
    simpa [(tri y hy).2] using congrArg (· * (B y)⁻¹) (factor y hy).symm
  -- Change variables by `g ↦ Φ (x * g)` from `U(ε')`, in Cayley's chart `c` on `D`, to `U(ε)`.
  let c : Matrix n n ℝ → USign ε' := cayleyChart (signMatrix ε')
  let D : Set (Matrix n n ℝ) := {y | (cayleyDenom (signMatrix ε') y).det ≠ 0}
  let S : Set (Matrix n n ℝ) := {y | (x : Matrix n n ℂ) * c y ∈ openOrbit ε o}
  have h_open : IsOpen {g : USign ε' | (x : Matrix n n ℂ) * g ∈ openOrbit ε o} :=
    (isOpen_openOrbit ε o).preimage (by fun_prop)
  have hS : MeasurableSet S := measurable_cayleyChart h_open.measurableSet
  -- `c y * (B (x * c y))⁻¹ = x⁻¹ * Φ (x * c y)` is a factorisation for `U(ε')`, which is unique.
  have inj : (S ∩ D).InjOn fun y ↦ Φ (x * c y) := by
    rintro z ⟨hzS, hzD⟩ y ⟨hyS, hyD⟩ (hΦ : Φ (x * c z) = Φ (x * c y))
    have h_eq : c z * (B (x * c z))⁻¹ = c y * (B (x * c y))⁻¹ :=
      x.isUnit.mul_left_cancel (by simp only [← mul_assoc, Φ_eq _ hzS, Φ_eq _ hyS, hΦ])
    have h_pos (i : n) : 0 < (B (x * c y))⁻¹ i i / (B (x * c z))⁻¹ i i := by
      simp [(tri _ hzS).inv_apply_diag ho, (tri _ hyS).inv_apply_diag ho, pos _ hzS, pos _ hyS]
    exact cayleyChart_injOn hzD hyD
      ((tri _ hzS).inv.unitary_eq_of_mul_eq ho ε' (tri _ hyS).inv h_eq h_pos)
  -- The Jacobian is the density `w y` of `c` times the modulus character `m y` of `B (x * c y)`.
  let w (y : Matrix n n ℝ) : ℝ := cayleyDensity (signMatrix ε') y
  let m (y : Matrix n n ℝ) : ℝ := ‖diagChar (twoRho o ⊤) (B (x * c y))‖ ^ 2
  have jac (y : Matrix n n ℝ) (hy : y ∈ S ∩ D) : DifferentiableAtU (fun z ↦ Φ (x * c z)) y ∧
      |(skewCoords ∘ₗ logDerivU (fun z ↦ Φ (x * c z)) y).det| = m y * w y := by
    obtain ⟨hyS, hyD⟩ := hy
    obtain ⟨c_diff : DifferentiableAtU c y, c_jac⟩ := abs_det_logDerivU_cayleyChart hyD
    have Φ_diff : DifferentiableAt ℝ (fun v : Matrix n n ℂ ↦ (Φ v : Matrix n n ℂ)) (x * c y) :=
      (hasFDerivAt_unitary_factor_of_mem_openOrbit ho ε tri pos factor hyS).differentiableAt
    refine ⟨Φ_diff.comp (f := fun z ↦ (x : Matrix n n ℂ) * c z) y (c_diff.const_mul _), ?_⟩
    rw [abs_det_logDerivU_unitary_factor ho tri pos factor x c_diff hyS, c_jac]
  -- Change of variables, up to a scalar `u = exp (i t)` that left invariance removes again.
  let vol : ℝ := volU (Fintype.card n)
  obtain ⟨u, change⟩ : ∃ u : USign ε, ∀ F : USign ε → ENNReal,
      ∫⁻ y in S ∩ D, .ofReal (m y * w y / vol) * F (u * Φ (x * c y)) ≤ ∫⁻ g, F g :=
    (Haar.lintegral_chart_rotate_le (.refl ℝ (Matrix n n ℝ)) (.id volume)
      (hS.inter (by measurability)) inj (fun y hy ↦ (jac y hy).1)
      fun y hy ↦ (jac y hy).2).exists.elim fun t ht ↦ ⟨circleScalar t, ht⟩
  let F (g : USign ε) : ENNReal :=
    {y : Matrix n n ℂ | (x : Matrix n n ℂ)⁻¹ * y ∈ openOrbit ε' o}.indicator (.ofReal ∘ f) g
  have pointwise (y : Matrix n n ℝ) :
      .ofReal (w y / vol) * (openOrbit ε o).indicator (ENNReal.ofReal ∘ f) (x * c y) =
        S.indicator (fun y ↦ .ofReal (m y * w y / vol) * F (Φ (x * c y))) y := by
    -- For `g = c y`: `x⁻¹ Φ (x g) = g (B (x g))⁻¹` lies in `U(ε') B`, and `x g = Φ (x g) B (x g)`.
    by_cases mem : (x : Matrix n n ℂ) * c y ∈ openOrbit ε o
    · have mem_inv : (x : Matrix n n ℂ)⁻¹ * Φ (x * c y) ∈ openOrbit ε' o :=
        ⟨c y, (B (x * c y))⁻¹, (tri _ mem).inv, by simp [← Φ_eq _ mem, mul_assoc]⟩
      have f_eq : f (x * c y) = m y * f (Φ (x * c y)) := by
        simpa only [factor _ mem, smul_eq_mul] using hf (Φ (x * c y)) (B (x * c y)) (tri _ mem)
      simp [S, F, m, mem_inv, mem, f_eq, mul_left_comm, mul_assoc, mul_div_assoc]
    · simp [S, mem]
  calc _ = ∫⁻ y in D, .ofReal (w y / vol) * (openOrbit ε o).indicator (.ofReal ∘ f) (x * c y) :=
        lintegral_eq_cayleyChart _
    _ = ∫⁻ y in S ∩ D, .ofReal (m y * w y / vol) * F (Φ (x * c y)) := by
        rw [lintegral_congr pointwise, setLIntegral_indicator hS]
    _ ≤ ∫⁻ g, F (u⁻¹ * g) := by simpa only [inv_mul_cancel_left] using change fun g ↦ F (u⁻¹ * g)
    _ = ∫⁻ g, F g := lintegral_mul_left_eq_self F u⁻¹

/-- By Gram-Schmidt every invertible matrix is a unitary times a triangular matrix. -/
lemma mem_openOrbit_one (o : n → ℤ) (y : GL n ℂ) : (y : Matrix n n ℂ) ∈ openOrbit 1 o := by
  obtain ⟨b, b_tri, b_unit⟩ := exists_orthonormal_mul o ⟨y.inv, y.inv_val⟩
  exact ⟨⟨y * b, by simpa [mem_U] using b_unit⟩, (b : Matrix n n ℂ)⁻¹,
    IsBorelMatrix.inv ⟨b_tri, GeneralLinearGroup.det_ne_zero b⟩, by simp⟩
end OpenFlagOrbit

/-!
## Integrals of densities over unitary groups

Both directions of the inequality `New.lintegral_openOrbit_le` give an integral formula for complex
valued densities on the flags of `GL n ℂ`.
-/

section UnitaryIntegrals

open Matrix MeasureTheory Complex ComplexOrder Norms.L2Operator LinearMap Finset U

variable {n : Type} [Fintype n] [DecidableEq n] {o : n → ℤ}
/-- Let `o` be injective, `B` its triangular group, `f` a real density on flags and `x`
invertible. Then the integral of the positive part of `g ↦ f (x * g)` over `U(ε)` is that of the
positive part of `f` over `U(n) ∩ x U(ε) B`. -/
lemma lintegral_mul_left_eq_setLIntegral_openOrbit (ho : o.Injective) (ε : n → ℤˣ)
    {f : Matrix n n ℂ → ℝ} (hf : IsFlagDensity o f) (x : GL n ℂ) :
    ∫⁻ g : USign ε, ENNReal.ofReal (f (x * g)) =
      ∫⁻ k in {k : USign (1 : n → ℤˣ) | (x : Matrix n n ℂ)⁻¹ * k ∈ openOrbit ε o},
        ENNReal.ofReal (f k) := by
  classical
  have h_meas : MeasurableSet {k : USign (1 : n → ℤˣ) | (x : Matrix n n ℂ)⁻¹ * k ∈ openOrbit ε o} :=
    ((isOpen_openOrbit ε o).preimage (by fun_prop)).measurableSet
  have h_mem (g : USign ε) : (x : Matrix n n ℂ) * g ∈ openOrbit 1 o := mem_openOrbit_one o (x * g)
  have hf_translate : IsFlagDensity o fun y : Matrix n n ℂ ↦ f (x * y) :=
    fun y b hb ↦ by simpa [mul_assoc] using hf (x * y) b hb
  rw [← lintegral_indicator h_meas]
  apply le_antisymm
  · simpa [h_mem, Set.indicator] using lintegral_openOrbit_le ho 1 ε x f hf
  · simpa [h_mem, Set.indicator, ← mul_assoc] using lintegral_openOrbit_le ho ε 1 x⁻¹ _ hf_translate

/-- Let `o` be injective, `F` a density on flags that is continuous on `GL n ℂ`, and `x`
invertible. Then `g ↦ F (x * g)` is integrable on `U(ε)`. -/
lemma integrable_mul_left_of_isFlagDensity (ho : o.Injective) (ε : n → ℤˣ) {F : Matrix n n ℂ → ℂ}
    (hF_density : IsFlagDensity o F) (hF_cont : Continuous fun y : GL n ℂ ↦ F y) (x : GL n ℂ) :
    Integrable fun g : USign ε ↦ F (x * g) := by
  -- The integral of `‖F (x * g)‖` equals an integral over a part of the compact group `U(n)`.
  have h_norm : IsFlagDensity o fun y : Matrix n n ℂ ↦ ‖F y‖ :=
    fun y b hb ↦ by simp [hF_density y b hb]
  have int_K : Integrable fun k : USign (1 : n → ℤˣ) ↦ F k :=
    DiscreteSeries.integrable_of_compactSpace (hF_cont.comp' continuous_subtype_val)
  refine ⟨(hF_cont.comp' (f := fun g : USign ε ↦ x * g) (by fun_prop)).aestronglyMeasurable, ?_⟩
  simpa [HasFiniteIntegral, ← ofReal_norm, lintegral_mul_left_eq_setLIntegral_openOrbit ho ε h_norm]
    using int_K.restrict.hasFiniteIntegral

/-- Let `o` be injective, `B` its triangular group, `F` a density on flags that is continuous on
`GL n ℂ`, and `x` invertible. Then the integral of `g ↦ F (x * g)` over `U(ε)` is that of `F` over
`U(n) ∩ x U(ε) B`. -/
lemma integral_mul_left_eq_setIntegral_openOrbit (ho : o.Injective) (ε : n → ℤˣ)
    {F : Matrix n n ℂ → ℂ} (hF_density : IsFlagDensity o F)
    (hF_cont : Continuous fun y : GL n ℂ ↦ F y) (x : GL n ℂ) :
    ∫ g : USign ε, F (x * g) =
      ∫ k in {k : USign (1 : n → ℤˣ) | (x : Matrix n n ℂ)⁻¹ * k ∈ openOrbit ε o}, F k := by
  have int_K : Integrable fun k : USign (1 : n → ℤˣ) ↦ F k :=
    DiscreteSeries.integrable_of_compactSpace (hF_cont.comp' continuous_subtype_val)
  have int_G := integrable_mul_left_of_isFlagDensity ho ε hF_density hF_cont x
  -- Test against real linear forms `φ`, and split `φ ∘ F` into its positive and negative parts.
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun φ ↦ ?_
  have hφ (ψ : ℂ →L[ℝ] ℝ) : IsFlagDensity o fun y : Matrix n n ℂ ↦ ψ (F y) :=
    fun y b hb ↦ by simp only [hF_density y b hb, map_smul]
  rw [← φ.integral_comp_comm int_G, ← φ.integral_comp_comm int_K.restrict,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (φ.integrable_comp int_G),
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (φ.integrable_comp int_K.restrict),
    lintegral_mul_left_eq_setLIntegral_openOrbit ho ε (hφ φ),
    lintegral_mul_left_eq_setLIntegral_openOrbit ho ε (f := fun y ↦ -φ (F y)) (hφ (-φ))]

/-- Let `o` be injective and `F` a density on flags that is continuous on `GL n ℂ`. Then `F` is
integrable on `U(diag ε)`. -/
lemma integrable_haar_of_isFlagDensity (ho : o.Injective) (ε : n → ℤˣ) {F : Matrix n n ℂ → ℂ}
    (hF_density : IsFlagDensity o F) (hF_cont : Continuous fun y : GL n ℂ ↦ F y) :
    Integrable fun g : USign ε ↦ F g := by
  simpa using integrable_mul_left_of_isFlagDensity ho ε hF_density hF_cont 1

/-- Let `G = U(diag ε)`, let `o` be injective, `B` its triangular group and `F` a density on flags
that is continuous on `GL n ℂ`. Then the integral of `F` over `G` is its integral over the part of
`U(n)` in `openOrbit ε o = G B`. Both groups carry their Haar measure `volume`, which in Cayley's
chart has density `cayleyDensity (signMatrix ε) / volU (card n)`, the same rule for every `ε`. -/
lemma integral_haar_eq_setIntegral_openOrbit (ho : o.Injective) (ε : n → ℤˣ) {F : Matrix n n ℂ → ℂ}
    (hF_density : IsFlagDensity o F) (hF_cont : Continuous fun y : GL n ℂ ↦ F y) :
    ∫ g : USign ε, F g =
      ∫ k in {k : USign (1 : n → ℤˣ) | (k : Matrix n n ℂ) ∈ openOrbit ε o}, F k := by
  simpa using integral_mul_left_eq_setIntegral_openOrbit ho ε hF_density hF_cont 1

/-- Let `o` be injective and `F` a density on flags that is continuous on `GL n ℂ`. Then `F` is
integrable on `U(diag ε)`, and its integral is the integral over `U(n)` less the integral over the
part of `U(n)` outside `openOrbit ε o`. -/
lemma integral_eq_sub_setIntegral_compl_openOrbit (ho : o.Injective) (ε : n → ℤˣ)
    {F : Matrix n n ℂ → ℂ}
    (hF_density : IsFlagDensity o F) (hF_cont : Continuous fun y : GL n ℂ ↦ F y) :
    Integrable (fun g : USign ε ↦ F g) ∧
    ∫ g : USign ε, F g = (∫ k : USign (1 : n → ℤˣ), F k) -
      ∫ k in {k : USign (1 : n → ℤˣ) | (k : Matrix n n ℂ) ∈ openOrbit ε o}ᶜ, F k := by
  have h_meas : MeasurableSet {k : USign (1 : n → ℤˣ) | (k : Matrix n n ℂ) ∈ openOrbit ε o} :=
    ((isOpen_openOrbit ε o).preimage (by fun_prop)).measurableSet
  refine ⟨integrable_haar_of_isFlagDensity ho ε hF_density hF_cont, ?_⟩
  rw [integral_haar_eq_setIntegral_openOrbit ho ε hF_density hF_cont, eq_sub_iff_add_eq,
    integral_add_compl h_meas (integrable_haar_of_isFlagDensity ho 1 hF_density hF_cont)]

/-- Let `o` be injective and `F` a density on flags that is continuous on `GL n ℂ`. Then its
integral over `U(n)` is invariant under left translation by any invertible matrix. -/
lemma integral_unitary_mul_left_of_density (ho : o.Injective) {F : Matrix n n ℂ → ℂ}
    (hF_density : IsFlagDensity o F) (hF_cont : Continuous fun y : GL n ℂ ↦ F y) (x : GL n ℂ) :
    ∫ k : USign (1 : n → ℤˣ), F (x * k) = ∫ k : USign (1 : n → ℤˣ), F k := by
  have h_mem (k : USign (1 : n → ℤˣ)) : (x : Matrix n n ℂ)⁻¹ * k ∈ openOrbit 1 o := by
    simpa using mem_openOrbit_one o (x⁻¹ * k)
  simp [integral_mul_left_eq_setIntegral_openOrbit ho 1 hF_density hF_cont, h_mem]

end UnitaryIntegrals

/-!
## Densities on the flag variety of `K_ℂ`

The group `K = maxCompactU ε` is a product of two unitary groups, one for each sign, and the
invariance follows from the case of one unitary group by Fubini's theorem.
-/

section Densities

open Matrix MeasureTheory Finset

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ}

/-- The indices `i` of sign `ε i = 1`. -/
abbrev PosIndex (ε : n → ℤˣ) : Type := {i : n // ε i = 1}

/-- The indices `i` of sign `ε i ≠ 1`, that is `ε i = -1`. -/
abbrev NegIndex (ε : n → ℤˣ) : Type := {i : n // ¬ε i = 1}

/-- The block diagonal matrix with the block `a` on the indices of sign `1` and the block `b` on
the others. -/
noncomputable def signBlocks (ε : n → ℤˣ) (a : Matrix (PosIndex ε) (PosIndex ε) ℂ)
    (b : Matrix (NegIndex ε) (NegIndex ε) ℂ) : Matrix n n ℂ :=
  reindex (Equiv.sumCompl (ε · = 1)) (Equiv.sumCompl (ε · = 1)) (fromBlocks a 0 0 b)

section

variable {a a' : Matrix (PosIndex ε) (PosIndex ε) ℂ} {b b' : Matrix (NegIndex ε) (NegIndex ε) ℂ}

omit [DecidableEq n] in
theorem signBlocks_mul :
    signBlocks ε a b * signBlocks ε a' b' = signBlocks ε (a * a') (b * b') := by
  simp [signBlocks, fromBlocks_multiply]

theorem det_signBlocks : (signBlocks ε a b).det = a.det * b.det := by simp [signBlocks]

section

omit [Fintype n]

theorem signBlocks_one : signBlocks ε 1 1 = 1 := by simp [signBlocks]

omit [DecidableEq n] in
theorem conjTranspose_signBlocks : (signBlocks ε a b)ᴴ = signBlocks ε aᴴ bᴴ := by
  simp [signBlocks, fromBlocks_conjTranspose]

omit [DecidableEq n] in
/-- The entries of `signBlocks ε a b`: those of `a` or `b` at indices of equal sign, else zero. -/
theorem signBlocks_apply (i j : n) : signBlocks ε a b i j =
    if hi : ε i = 1 then if hj : ε j = 1 then a ⟨i, hi⟩ ⟨j, hj⟩ else 0
    else if hj : ε j = 1 then 0 else b ⟨i, hi⟩ ⟨j, hj⟩ := by
  by_cases hi : ε i = 1 <;> by_cases hj : ε j = 1 <;> simp [signBlocks, hi, hj]

end

/-- The matrix `signBlocks ε a b` lies in `blockDiagAlg ε`: its entries vanish at indices of
different sign. -/
theorem signBlocks_mem_blockDiagAlg : signBlocks ε a b ∈ blockDiagAlg ε :=
  mem_blockDiagAlg.2 fun i j h_ne ↦ by
    grind [signBlocks_apply, Int.units_eq_one_or (ε i), Int.units_eq_one_or (ε j)]

omit [Fintype n] in
theorem signBlocks_eq_one_iff : signBlocks ε a b = 1 ↔ a = 1 ∧ b = 1 := by
  rw [← signBlocks_one (ε := ε), signBlocks, signBlocks, Equiv.apply_eq_iff_eq, fromBlocks_inj]
  simp

/-- A block diagonal matrix with unitary blocks preserves the form `signMatrix ε = diag ε`. -/
theorem signBlocks_preserves_form (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) :
    (signBlocks ε a b)ᴴ * signMatrix ε * signBlocks ε a b = signMatrix ε := by
  rw [mul_assoc, DiscreteSeries.mem_blockDiagAlg_iff_commute.1 signBlocks_mem_blockDiagAlg,
    ← mul_assoc,
    conjTranspose_signBlocks, signBlocks_mul, ha, hb, signBlocks_one, one_mul]

/-- A block diagonal matrix is invertible and triangular for the order `o` if both blocks are. -/
theorem isBorelMatrix_signBlocks {o : n → ℤ} (ha : IsBorelMatrix (fun i : PosIndex ε ↦ o i) a)
    (hb : IsBorelMatrix (fun i : NegIndex ε ↦ o i) b) : IsBorelMatrix o (signBlocks ε a b) := by
  obtain ⟨ha_tri, ha_det⟩ := ha
  obtain ⟨hb_tri, hb_det⟩ := hb
  refine ⟨fun i j h_lt ↦ ?_, by simp [det_signBlocks, ha_det, hb_det]⟩
  rw [signBlocks_apply]
  split_ifs
  exacts [ha_tri h_lt, rfl, rfl, hb_tri h_lt]

omit [DecidableEq n] in
/-- The product `diagChar w m = ∏ i, m i i ^ w i` of a block diagonal matrix splits over the two
blocks. -/
theorem diagChar_signBlocks (w : n → ℤ) : diagChar w (signBlocks ε a b) =
    diagChar (fun i : PosIndex ε ↦ w i) a * diagChar (fun i : NegIndex ε ↦ w i) b := by
  simp [diagChar, ← (Equiv.sumCompl fun i : n ↦ ε i = 1).prod_comp, signBlocks]

end

/-- Every matrix in `blockDiagAlg ε` (entries vanish at indices of different sign) has the form
`signBlocks ε a b`. -/
theorem exists_eq_signBlocks {y : Matrix n n ℂ} (hy : y ∈ blockDiagAlg ε) :
    ∃ (a : Matrix (PosIndex ε) (PosIndex ε) ℂ) (b : Matrix (NegIndex ε) (NegIndex ε) ℂ),
      y = signBlocks ε a b := by
  refine ⟨y.toBlock (ε · = 1) (ε · = 1), y.toBlock (¬ε · = 1) (¬ε · = 1), ext fun i j ↦ ?_⟩
  grind [signBlocks_apply, toBlock_apply, mem_blockDiagAlg.1 hy i j]

omit [Fintype n] [DecidableEq n] in
/-- A block diagonal matrix depends continuously on its two blocks. -/
@[fun_prop] theorem continuous_signBlocks {X : Type*} [TopologicalSpace X]
    {a : X → Matrix (PosIndex ε) (PosIndex ε) ℂ} {b : X → Matrix (NegIndex ε) (NegIndex ε) ℂ}
    (ha : Continuous a) (hb : Continuous b) : Continuous fun x : X ↦ signBlocks ε (a x) (b x) := by
  unfold signBlocks
  fun_prop

/-- The homomorphism `U(p) × U(q) → K = maxCompactU ε` that puts two unitary matrices on the
diagonal; `p` and `q` count the indices of sign `1` and `-1`. -/
noncomputable def signBlocksHom (ε : n → ℤˣ) :
    USign (1 : PosIndex ε → ℤˣ) × USign (1 : NegIndex ε → ℤˣ) →* maxCompactU ε :=
  MonoidHom.mk'
    (fun u ↦ ⟨U.of IsHermitianInvolution.isUnit (signBlocks ε u.1 u.2)
        (signBlocks_preserves_form (by simpa using mem_U.1 u.1.2) (by simpa using mem_U.1 u.2.2)),
      mem_maxCompactU.2 signBlocks_mem_blockDiagAlg⟩)
    fun u v ↦ Subtype.ext <| Subtype.ext <| Units.ext (by simp [signBlocks_mul])

theorem coe_signBlocksHom (u : USign (1 : PosIndex ε → ℤˣ)) (v : USign (1 : NegIndex ε → ℤˣ)) :
    (signBlocksHom ε (u, v) : Matrix n n ℂ) = signBlocks ε u v := rfl

theorem continuous_signBlocksHom : Continuous (signBlocksHom ε) := by
  rw [continuous_induced_rng, continuous_U_iff_matrix]
  exact continuous_signBlocks (by fun_prop) (by fun_prop)

/-- Every element of `K = maxCompactU ε` is block diagonal with unitary blocks. -/
theorem signBlocksHom_surjective : Function.Surjective (signBlocksHom ε) := by
  intro k
  obtain ⟨a, b, hk : (k : Matrix n n ℂ) = signBlocks ε a b⟩ :=
    exists_eq_signBlocks (mem_maxCompactU.1 k.prop)
  have h_unitary : signBlocks ε (aᴴ * a) (bᴴ * b) = 1 := by
    rw [← signBlocks_mul, ← conjTranspose_signBlocks, ← hk, ← maxCompactU.coe_inv,
      nonsing_inv_mul _ (by simp [GeneralLinearGroup.det_ne_zero])]
  obtain ⟨ha, hb⟩ := signBlocks_eq_one_iff.1 h_unitary
  refine ⟨(U.of IsHermitianInvolution.isUnit a (by simpa using ha),
    U.of IsHermitianInvolution.isUnit b (by simpa using hb)), ?_⟩
  ext : 3
  simp [coe_signBlocksHom, hk]

/-- The map `U(p) × U(q) → K = maxCompactU ε`, `(a, b) ↦ signBlocks ε a b`, carries the product of
the Haar measures of mass one to the Haar measure `haarK ε` of mass one. -/
theorem measurePreserving_signBlocksHom :
    MeasurePreserving (signBlocksHom ε) (volume.prod volume) (haarK ε) :=
  MonoidHom.measurePreserving continuous_signBlocksHom signBlocksHom_surjective (by simp)

/-- Fubini's theorem on `K = maxCompactU ε ≃ U(p) × U(q)`: the integral of a continuous function
over `K` is the double integral over the unitary blocks. -/
theorem integral_haarK_eq_integral_signBlocksHom {φ : maxCompactU ε → ℂ} (hφ : Continuous φ) :
    ∫ k : maxCompactU ε, φ k ∂haarK ε = ∫ u : USign (1 : PosIndex ε → ℤˣ),
      ∫ v : USign (1 : NegIndex ε → ℤˣ), φ (signBlocksHom ε (u, v)) :=
  (measurePreserving_signBlocksHom.fubini (DiscreteSeries.integrable_of_compactSpace hφ)).right.symm

omit [DecidableEq n] in
/-- Let `p` select the indices of one sign. On these indices `-2 ρ_c`, minus the sum of the compact
roots (those `e i - e j` with `ε i = ε j`) positive for `l`, is the sum `2 ρ` of all roots of the
block positive for `-l`. -/
theorem twoRho_subtype (l : n → ℤ) {p : n → Prop} [DecidablePred p]
    (hp : ∀ i j : n, p i → (p j ↔ ε i = ε j)) :
    twoRho (fun i : {i : n // p i} ↦ (-l) i) ⊤ =
      fun i : {i : n // p i} ↦ (-twoRho l fun i j : n ↦ ε i = ε j) i := by
  ext i
  have h_class (j : n) : ε i = ε j ↔ p j := (hp i j i.prop).symm
  have h_card (q : n → Prop) [DecidablePred q] :
      #{j : {i : n // p i} | q j} = #{j : n | ε i = ε j ∧ q j} :=
    card_bij (fun j _ ↦ (j : n)) (by simp +contextual [h_class, Subtype.property]) (by simp)
      (by simp +contextual [h_class])
  simp [twoRho, ← h_card]

/-- Let `K_ℂ` be the group of invertible matrices in `blockDiagAlg ε` (entries vanish at indices of
different sign), let `K = maxCompactU ε` be its unitary subgroup with Haar measure `haarK ε`, and
let `l` have distinct entries. Let `B_K` be the subgroup of `K_ℂ` of matrices upper triangular in
the order of decreasing `l`, and let `2 ρ_c` be the sum of the compact roots (those `e i - e j` with
`ε i = ε j`) positive for `l`. If `F` is continuous on `K_ℂ` and
`F (y * b) = |∏ i, b i i ^ (-2 ρ_c) i| ^ 2 * F y` for `y` in `K_ℂ` and `b` in `B_K`, then the
integral of `F (x * k)` over `K` equals that of `F k`, for all `x` in `K_ℂ`.

Classically this invariance follows from the Iwasawa decomposition `K_ℂ = K B_K` and the form
`dk d_r b` of the Haar measure of `K_ℂ`; here the invariance is proved block by block, by Fubini's
theorem and `integral_unitary_mul_left_of_density`, without using the Haar measure of `K_ℂ`. -/
theorem integral_haarK_mul_left_of_density {l : n → ℤ} (hl : l.Injective) {F : Matrix n n ℂ → ℂ}
    (hF_cont : ContinuousOn F {y : Matrix n n ℂ | y ∈ blockDiagAlg ε ∧ y.det ≠ 0})
    (hF_borel : ∀ y ∈ blockDiagAlg ε, y.det ≠ 0 → ∀ b ∈ blockDiagAlg ε, IsBorelMatrix (-l) b →
      F (y * b) = ‖diagChar (-twoRho l fun i j : n ↦ ε i = ε j) b‖ ^ 2 * F y)
    {x : Matrix n n ℂ} (hx_mem : x ∈ blockDiagAlg ε) (hx_det : x.det ≠ 0) :
    ∫ k : maxCompactU ε, F (x * k) ∂haarK ε = ∫ k : maxCompactU ε, F k ∂haarK ε := by
  -- Let `f y z` be `F` at the matrix with blocks `y`, `z`. It is a density in each variable (for
  -- the orders `op`, `oq` that `-l` induces on the blocks), and the integral over `K` is the double
  -- integral over the unitary groups `Up`, `Uq` of the blocks.
  let f (y : GL (PosIndex ε) ℂ) (z : GL (NegIndex ε) ℂ) : ℂ := F (signBlocks ε y z)
  let Up : Subgroup (GL (PosIndex ε) ℂ) := USign 1
  let Uq : Subgroup (GL (NegIndex ε) ℂ) := USign 1
  let op (i : PosIndex ε) : ℤ := (-l) i
  let oq (i : NegIndex ε) : ℤ := (-l) i
  have h_det (y : GL (PosIndex ε) ℂ) (z : GL (NegIndex ε) ℂ) : (signBlocks ε y z).det ≠ 0 := by
    simp [det_signBlocks, GeneralLinearGroup.det_ne_zero]
  have hf_cont : Continuous f.uncurry :=
    hF_cont.comp_continuous (by fun_prop) fun (y, z) ↦ ⟨signBlocks_mem_blockDiagAlg, h_det y z⟩
  have sign_pos (i j : n) (hi : ε i = 1) : ε j = 1 ↔ ε i = ε j := by grind
  have sign_neg (i j : n) (hi : ¬ε i = 1) : ¬ε j = 1 ↔ ε i = ε j := by
    grind [Int.units_eq_one_or (ε i), Int.units_eq_one_or (ε j)]
  have h_inj : (-l).Injective := neg_injective.comp hl
  -- The rule for `F` on block matrices; on each block `-2 ρ_c` is the `2 ρ` of the block.
  have h_rule (y : GL (PosIndex ε) ℂ) (z : GL (NegIndex ε) ℂ)
      {s : Matrix (PosIndex ε) (PosIndex ε) ℂ} {t : Matrix (NegIndex ε) (NegIndex ε) ℂ}
      (hs : IsBorelMatrix op s) (ht : IsBorelMatrix oq t) :
      F (signBlocks ε (y * s) (z * t)) =
        ‖diagChar (twoRho op ⊤) s * diagChar (twoRho oq ⊤) t‖ ^ 2 * f y z := by
    rw [twoRho_subtype l sign_pos, twoRho_subtype l sign_neg, ← signBlocks_mul,
      ← diagChar_signBlocks]
    exact hF_borel _ signBlocks_mem_blockDiagAlg (h_det y z) _ signBlocks_mem_blockDiagAlg
      (isBorelMatrix_signBlocks hs ht)
  have h_pos (y : GL (PosIndex ε) ℂ) (z : GL (NegIndex ε) ℂ) :
      ∫ u : Up, f (y * u) z = ∫ u : Up, f u z := by
    have density : IsFlagDensity op fun s ↦ F (signBlocks ε s z) := fun y' s hs ↦ by
      simpa [diagChar] using h_rule y' z hs ⟨blockTriangular_one, by simp⟩
    exact integral_unitary_mul_left_of_density (h_inj.comp Subtype.val_injective) density
      (hf_cont.uncurry_right z) y
  have h_neg (y : GL (PosIndex ε) ℂ) (z : GL (NegIndex ε) ℂ) :
      ∫ v : Uq, f y (z * v) = ∫ v : Uq, f y v := by
    have density : IsFlagDensity oq fun t ↦ F (signBlocks ε y t) := fun z' t ht ↦ by
      simpa [diagChar] using h_rule y z' ⟨blockTriangular_one, by simp⟩ ht
    exact integral_unitary_mul_left_of_density (h_inj.comp Subtype.val_injective) density
      (hf_cont.uncurry_left y) z
  have h_fubini (y : GL (PosIndex ε) ℂ) (z : GL (NegIndex ε) ℂ) :
      ∫ k : maxCompactU ε, F (signBlocks ε y z * k) ∂haarK ε =
        ∫ u : Up, ∫ v : Uq, f (y * u) (z * v) := by
    have h_cont : Continuous fun k : maxCompactU ε ↦ F (signBlocks ε y z * k) := by
      refine hF_cont.comp_continuous (by fun_prop) fun k ↦ ⟨?_, ?_⟩
      · exact mul_mem signBlocks_mem_blockDiagAlg (mem_maxCompactU.1 k.prop)
      · simp [h_det, GeneralLinearGroup.det_ne_zero]
    simp [integral_haarK_eq_integral_signBlocksHom h_cont, coe_signBlocksHom, signBlocks_mul, f, Up,
      Uq]
  have h_swap (y : GL (PosIndex ε) ℂ) :
      ∫ u : Up, ∫ v : Uq, f (y * u) v = ∫ v : Uq, ∫ u : Up, f (y * u) v :=
    integral_integral_swap (DiscreteSeries.integrable_of_compactSpace (by fun_prop))
  obtain ⟨a, b, rfl⟩ := exists_eq_signBlocks hx_mem
  obtain ⟨⟨y, rfl⟩, ⟨z, rfl⟩⟩ : IsUnit a ∧ IsUnit b := by
    simpa [det_signBlocks, isUnit_iff_isUnit_det] using hx_det
  calc _ = ∫ u : Up, ∫ v : Uq, f (y * u) (z * v) := h_fubini y z
    _ = ∫ u : Up, ∫ v : Uq, f (1 * u) v := by simp only [h_neg, h_swap, h_pos]
    _ = ∫ k : maxCompactU ε, F k ∂haarK ε := by simpa [signBlocks_one] using (h_fubini 1 1).symm

end Densities

end New

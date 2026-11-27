import Lib.Adelic.Adeles.SemilocalProducts
import Lib.Adelic.AutomorphicForms.UnipotentRadical
import Lib.Weil.Construction.AdelicRepresentation
import Lib.Weil.Unramified.HeckeGL

/-!
# Cuspidality bounds, unipotent reduction, rapid decay and finite dimension of forms

This file studies forms of type `e` (`New.Space.IsForm`) on the adelic unitary group of a hermitian
space `V`, for a cusp kernel `e` (`New.IsCuspKernel`). At a point with a short lattice vector,
short vectors span a cusp: a rational isotropic subspace whose radical is covered by its rational
points times a small real ball and a level. A bounded continuous function that is fixed by `e` and
invariant under the rational points of a unipotent radical, of finite covolume, has mean zero along
the radical (`New.Space.integral_unipotentRadical_eq_zero`, in
`Lib.Adelic.AutomorphicForms.UnipotentRadical`). The rational points are cocompact in the radical
of a rational isotropic subspace, so forms are cuspidal. Forms then decay faster than every power
of the height, and those of a fixed level span a finite-dimensional space.

## Main definitions and results

* `New.Space.exists_cuspFrame`: let `N ≠ 0` be a natural number in the different of `E`, `M ≠ 0` and
  `0 < δ ≤ 1`. If the first minimum is less than `(δ / (M κ²))ⁿ`, with `κ = New.cuspConst E n N`,
  short lattice vectors span a rational isotropic subspace `A ≠ 0` and its orthogonal
  (`New.Space.CuspFrame`), and `N_A` lies in `(Γ ∩ N_A) Z_δ J(M)` (`New.Space.RadicalCovered`),
  where `Z_δ` is the real ball of radius `δ` about `1` and `J(M)` is the principal level `M`.
* `New.Space.IsCuspidal`, `New.Space.IsForm.isCuspidal`: cuspidal functions; forms are cuspidal.
* `New.Space.IsCuspidal.norm_le_of_firstMinimum_lt`: at such a point `g`, a cuspidal function of
  level `M` is at most its oscillation under real right translations of size `δ`.
* `New.Space.exists_norm_mul_height_pow_le`, `New.Space.IsForm.mem_rapidFunctions`: forms decay
  faster than every power of the height, uniformly at a fixed level.
* `New.Space.finite_levelSpace`: the forms of a fixed level span a finite-dimensional space.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places (in the coordinates x⁻¹ X this
  form is the adelic matrix `stdForm E s`); `V.Γ` is its group of rational points in the adelic
  group G = G_∞ × G_f, and `V.move g` has the point xg.
* `New.realConv`, `New.Space.IsForm`: R(k)F(g) = ∫ k(x) F(gx) dx over G_∞ (`New.GInf`, one copy of
  U(diag s) for each infinite place of E), for k on G_∞ and F on G. For integrable e, a form of
  type e is a bounded automorphic function fixed by R(e). Here e is a cusp kernel
  (`New.IsCuspKernel`): a minimal idempotent for convolution on G_∞ that decays polynomially and
  is reproduced by a compactly supported function.
* `New.Space.height`: the height ht(g) = 1/λ, with λ the first minimum cut off at 1
  (`New.Space.firstMinimum`) of the moved space `V.move g`.
* `New.unipotentRadical` (in `Lib.Adelic.AutomorphicForms.UnipotentRadical`): the adelic unipotent
  radical of the stabiliser of the span of the columns of an isotropic matrix.
* `New.Reduction.radicalElem` (in `Lib.Adelic.AutomorphicForms.UnipotentRadical`): the matrix
  `1 + 2 (T - Tᴴ - Tᴴ J T) J`; for hermitian `J` and `T = w aᴴ` with `aᴴ J a = aᴴ J w = 0`, it
  preserves `J`, fixes `a` and acts trivially on `a^⊥ / a`.

## Relation to the literature

Known results: cusp forms decay rapidly, and those of a fixed type and level make up a space of
finite dimension. Here a form is a bounded function reproduced by an integrable minimal idempotent,
with no differential equation. Cuspidality is used as a bound by the oscillation along unipotent
orbits, with an explicit depth, and the cusp is spanned by the shortest vectors of a sorted
Minkowski basis.

Sources: A. Borel, Automorphic forms on reductive groups (Park City lectures), IAS/Park City Math.
Ser. 12 (2007) 7-39, sections 7.6-7.9 and 8.3-8.4; I. Satake, Caractérisation de l'espace des
Spitzenformen, Sém. H. Cartan 10 (1957/58), exp. 9 bis; R. Godement, Série de Poincaré et
Spitzenformen, ibid., exp. 10; R. Godement, The spectral
decomposition of cusp forms, Proc. Sympos. Pure Math. 9 (1966) 225-234; S. Miller and W. Schmid, On
the rapid decay of cuspidal automorphic forms, Adv. Math. 231 (2012), arXiv 1106.2149; G. Muić,
Smooth cuspidal automorphic forms and integrable discrete series, arXiv 1610.05483 (cuspidality
through N. Wallach, On the constant term of a square integrable automorphic form, 1984).
-/

/-! ## The cusp of a point with a short vector; cuspidal functions -/

namespace New

open NumberField MeasureTheory Matrix Norms.L2Operator Finset Fintype Submodule G

open Reduction (IsIntBounded radicalElem exists_radicalElem_mul_eq)

/-- The constant `κ = 8 f n · rd + 48 n⁶ f² N + 1` in the bound
`New.Space.IsForm.norm_le_of_firstMinimum_lt`, where `f` is the number of infinite places, `rd` the
root discriminant of `E`, and `N` a natural number (in the bound, a nonzero natural number in the
different of `E`). -/
noncomputable def cuspConst (E n : Type) [Field E] [CMType E] [Fintype n] (N : ℕ) : ℝ :=
  8 * (Core.numInfPlaces E * Fintype.card n) * rootDiscr E +
    (48 * Fintype.card n ^ 6 * Core.numInfPlaces E ^ 2 * N + 1)

lemma one_le_cuspConst (E n : Type) [Field E] [CMType E] [Fintype n] (N : ℕ) :
    1 ≤ cuspConst E n N := by
  rw [cuspConst, rootDiscr, ← add_assoc]
  bound

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  {V : Space E n s} {F : G E s → ℂ} {B : ℕ} {e : GInf E s → ℂ}

lemma Reduction.IsIntBounded.mono {r t : ℝ} {a : Matrix n n (𝔸 E)} (ha : IsIntBounded r a)
    (h_le : r ≤ t) : IsIntBounded t a :=
  ⟨ha.1, fun w ↦ (ha.2 w).trans h_le⟩

namespace Space

/-- The rational matrix `X` in the adelic coordinates `x⁻¹ X` given by the point `x` of `W`, in
which the form of `W` is `stdForm E s`. -/
noncomputable def adelicCoords (W : Space E n s) (X : Matrix n n E) : Matrix n n (𝔸 E) :=
  W.x⁻¹.val * X.map toAdele

/-- The adelic unipotent radical `N_A` of the span `A` of the columns of the rational matrix `X`,
used for isotropic `A`. For `W = V.move g` it is `g⁻¹ N_A g`. -/
noncomputable abbrev radical (W : Space E n s) (X : Matrix n n E) : Subgroup (G E s) :=
  unipotentRadical s (W.adelicCoords X)

/-- The radical `N_A` of the span `A` of the columns of `X` lies in `(Γ ∩ N_A) Z_δ J`, where `Γ` is
the group of rational points of `W` and `Z_δ` is the real ball of radius `δ` about `1`.
For `W = V.move g` it reads `N_A g ⊆ (Γ ∩ N_A) g Z_δ J`, with `Γ` and `N_A` those of `V`. -/
def RadicalCovered (W : Space E n s) (X : Matrix n n E) (δ : ℝ) (J : Subgroup (Gf E n)) : Prop :=
  ∀ u ∈ W.radical X, ∃ γ ∈ W.Γ ⊓ W.radical X, dist (γ * u).1 1 ≤ δ ∧ (γ * u).2 ∈ J

/-- A cusp of size `δ`: a non-zero rational isotropic subspace `A` such that `A` and `A^⊥` are
spanned by the columns of `X = isotropicCols` and of `Y = perpCols`, lattice vectors of lengths at
most `lengthX`, `lengthY` (`W.latticeBall l`: vectors of `W.baseLattice` whose `W.archCoords` have
norm at most `l`) with `lengthX * lengthY ≤ δ`. -/
structure CuspFrame (W : Space E n s) (δ : ℝ) where
  /-- A matrix whose columns span `A`. -/
  isotropicCols : Matrix n n E
  /-- A matrix whose columns span `A^⊥`. -/
  perpCols : Matrix n n E
  /-- The bound for the lengths of the columns of `isotropicCols`. -/
  lengthX : ℝ
  /-- The bound for the lengths of the columns of `perpCols`. -/
  lengthY : ℝ
  /-- `A` is not zero. -/
  ne_zero : isotropicCols ≠ 0
  /-- `A` is isotropic. -/
  isotropic : isotropicColsᴴ * (W.J * isotropicCols) = 0
  /-- The columns of `perpCols` lie in `A^⊥`. -/
  orthogonal : isotropicColsᴴ * (W.J * perpCols) = 0
  /-- The columns of `perpCols` span `A^⊥`: a vector `v` orthogonal to `A` equals
  `perpCols *ᵥ e *ᵥ v`. -/
  spans : ∃ e b : Matrix n n E, perpCols * e + b * (isotropicColsᴴ * W.J) = 1
  /-- The columns of `isotropicCols` are lattice vectors of length at most `lengthX`. -/
  col_isotropicCols_mem (j : n) : isotropicCols.col j ∈ W.latticeBall lengthX
  /-- The columns of `perpCols` are lattice vectors of length at most `lengthY`. -/
  col_perpCols_mem (j : n) : perpCols.col j ∈ W.latticeBall lengthY
  /-- The vectors that span `A` have the smaller bound. -/
  lengthX_le : lengthX ≤ lengthY
  /-- The product of the two bounds is at most `δ`. -/
  length_mul_le : lengthX * lengthY ≤ δ

variable {W : Space E n s} {X Y : Matrix n n E}

/-- The standard pairing of the adelic coordinates of `X` and `Y` is their pairing `Xᴴ J Y` for the
form `J` of `W`. -/
lemma adelicCoords_gram (W : Space E n s) (X Y : Matrix n n E) :
    (W.adelicCoords X)ᴴ * (stdForm E s * W.adelicCoords Y) = (Xᴴ * (W.J * Y)).map toAdele := by
  simp [adelicCoords, W.map_J, mul_assoc]

lemma adelicCoords_gram_eq_zero (h_gram : Xᴴ * (W.J * Y) = 0) :
    (W.adelicCoords X)ᴴ * (stdForm E s * W.adelicCoords Y) = 0 := by
  rw [adelicCoords_gram, h_gram, Matrix.map_zero _ (map_zero _)]

lemma adelicCoords_injective (W : Space E n s) : Function.Injective W.adelicCoords :=
  fun _ _ h_eq ↦ map_injective (toAdele (E := E)).injective (W.x⁻¹.isUnit.mul_left_cancel h_eq)

lemma adelicCoords_evalInf_ne_zero (hX : X ≠ 0) (w : InfinitePlace E) :
    (W.adelicCoords X).map (evalInf w) ≠ 0 := fun h_zero ↦
  hX (ext_col fun j ↦ W.eq_zero_of_vecAtPoint_fst_eq_zero (w := w)
    (funext fun i ↦ congrFun₂ h_zero i j))

/-- If the columns of `X` are lattice vectors of length at most `l`, the adelic coordinates of `X`
are integral at the finite places and of operator norm at most `n² l` at the infinite ones. -/
lemma isIntBounded_adelicCoords {l : ℝ} (hX : ∀ j : n, X.col j ∈ W.latticeBall l) :
    IsIntBounded (Fintype.card n * Fintype.card n * l) (W.adelicCoords X) :=
  ⟨fun i j ↦ (hX j).1 i, fun w ↦ l2_opNorm_le_of_apply fun i j ↦
    (PiLp.norm_apply_le (W.archCoords (X.col j)) (w, i)).trans (hX j).2⟩

/-- Moving the point of `V` by `g` conjugates the embedding of the rational points by `g`. -/
lemma ratEmbed_move (V : Space E n s) (g : G E s) (γ : U V.J) :
    (V.move g).ratEmbed γ = g⁻¹ * V.ratEmbed γ * g := by
  apply ext_adeleMatrix
  rw [adeleMatrix_mul, adeleMatrix_mul, V.adeleMatrix_ratEmbed γ, (V.move g).adeleMatrix_ratEmbed γ]
  simp [move, mul_assoc, adeleMatrix]

/-- If a rational point `ν` of `U(J)` embeds into the adelic radical of the span `A` of the columns
of `X`, it fixes `A` and `A^⊥ / A` pointwise over `E`. -/
lemma mem_dilationGroup_of_ratEmbed_mem_radical {ν : U W.J} (hν : W.ratEmbed ν ∈ W.radical X) :
    (ν, 1) ∈ dilationGroup (m := n) X := by
  obtain ⟨h_fixes, h_trivial⟩ := mem_unipotentRadical_iff.1 hν
  have h_act (v : Matrix n n E) :
      (W.ratEmbed ν).adeleMatrix * W.adelicCoords v = W.adelicCoords ((ν : Matrix n n E) * v) := by
    simp [adelicCoords, adeleMatrix_ratEmbed, mul_assoc]
  refine mk_one_mem_dilationGroup_iff.2 ⟨W.adelicCoords_injective ?_, fun v w hv hw ↦ ?_⟩
  · rw [← h_act, h_fixes]
  · refine map_injective (toAdele (E := E)).injective ?_
    change (wᴴ * (W.J * (ν * v))).map toAdele = (wᴴ * (W.J * v)).map toAdele
    rw [← adelicCoords_gram, ← adelicCoords_gram, ← h_act]
    exact h_trivial _ _ (adelicCoords_gram_eq_zero hv) (adelicCoords_gram_eq_zero hw)

end Space

/-- Pairing from both ends: if the square of a product of `k` real numbers is below `c ^ k` with
`0 ≤ c`, then at some pair of opposite indices `i`, `i.rev` with `m i ≤ m i.rev`, the two
numbers have a product below `c`. -/
lemma exists_le_rev_and_mul_rev_lt {k : ℕ} {m : Fin k → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h_prod : (∏ i : Fin k, m i) ^ 2 < c ^ k) :
    ∃ i : Fin k, m i ≤ m i.rev ∧ m i * m i.rev < c := by
  obtain ⟨i, hi⟩ : ∃ i : Fin k, m i * m i.rev < c := by
    by_contra! h_ge
    refine h_prod.not_ge ?_
    calc c ^ k = ∏ _ : Fin k, c := (Fin.prod_const _ c).symm
      _ ≤ ∏ i : Fin k, m i * m i.rev := by
          gcongr with i
          exact h_ge i
      _ = (∏ i : Fin k, m i) ^ 2 := by rw [prod_mul_distrib, Fin.rev_bijective.prod_comp, sq]
  rcases le_total (m i) (m i.rev) with h_le | h_le
  · exact ⟨i, h_le, hi⟩
  · exact ⟨i.rev, by rwa [Fin.rev_rev], by rwa [Fin.rev_rev, mul_comm]⟩

/-- The square matrix whose rows, numbered by `e`, are the independent vectors `y 0, …, y j`, the
last one repeated, has rank `j + 1`. -/
lemma rank_of_apply_min {K ι : Type*} [Field K] [Fintype ι] {k : ℕ} (e : ι ≃ Fin k)
    {y : Fin k → ι → K} (hy : LinearIndependent K y) (j : Fin k) :
    (of fun a : ι ↦ y (min (e a) j)).rank = j + 1 := by
  have h_rows : Set.range (of fun a : ι ↦ y (min (e a) j)).row = y '' Set.Iic j := by
    refine Set.Subset.antisymm (Set.range_subset_iff.2 fun a ↦ ?_) (Set.image_subset_iff.2 ?_)
    · exact ⟨min (e a) j, min_le_right (e a) j, rfl⟩
    · exact fun l hl ↦ ⟨e.symm l, funext fun i ↦ by simp [min_eq_left (Set.mem_Iic.1 hl)]⟩
  rw [rank_eq_finrank_span_row, h_rows, Set.image_eq_range,
    finrank_span_eq_card (b := fun l : Set.Iic j ↦ y l) (hy.comp _ Subtype.val_injective)]
  simp

/-- Minkowski's basis of a space of rank `k`. Let `1 ≤ κ` and `8 f k · rd ≤ κ`, where `f` is the
number of infinite places and `rd` is the root discriminant of `E`. The lattice of `W` contains a
basis, ordered by length, whose lengths have product at most `κ ^ k`. -/
lemma Space.exists_basis_prod_norm_le (W : Space E n s) {k : ℕ} (hk : Fintype.card n = k) {κ : ℝ}
    (hκ : 1 ≤ κ) (h_discr : 8 * (Core.numInfPlaces E * Fintype.card n) * rootDiscr E ≤ κ) :
    ∃ y : Fin k → n → E,
      LinearIndependent E y ∧
      (∀ j : Fin k, y j ∈ W.baseLattice) ∧
      (Monotone fun j : Fin k ↦ ‖W.archCoords (y j)‖) ∧
      ∏ j : Fin k, ‖W.archCoords (y j)‖ ≤ κ ^ k := by
  subst hk
  -- The lattice and the lengths of `W` are by definition those of the frame `W.x`.
  obtain ⟨y, hy_indep, hy_mem, hy_mono, h_prod⟩ := Core.minkowski_second_theorem W.x
  refine ⟨y, hy_indep, hy_mem, hy_mono,
    le_of_pow_le_pow_left₀ (n := 2 * Core.numInfPlaces E) (by positivity) (by positivity) ?_⟩
  have discr_pos : 0 < rootDiscr E := rootDiscr_pos E
  -- The frame of a space has adelic determinant of absolute value `1`.
  calc (∏ j : Fin (card n), ‖W.archCoords (y j)‖) ^ (2 * Core.numInfPlaces E)
      ≤ (2 * (Core.numInfPlaces E * card n) * rootDiscr E) ^ (Core.numInfPlaces E * card n) := by
        rwa [ideleAbs_det_x, one_mul, prod_pow] at h_prod
    _ ≤ κ ^ (Core.numInfPlaces E * card n) := pow_le_pow_left₀ (by positivity) (by linarith) _
    _ ≤ κ ^ (card n * (2 * Core.numInfPlaces E)) := pow_le_pow_right₀ hκ (by nlinarith)
    _ = (κ ^ card n) ^ (2 * Core.numInfPlaces E) := pow_mul ..

/-- If lattice vectors `y j` of length at most `r` span `E ^ n`, the length of every nonzero lattice
vector times `r` is at least `1`. -/
lemma Space.one_le_norm_mul_of_span_eq_top (W : Space E n s) {ξ : n → E} (hξ : ξ ∈ W.baseLattice)
    (hξ_ne : ξ ≠ 0) {ι : Type*} {y : ι → n → E} (h_span : span E (Set.range y) = ⊤)
    (hy_mem : ∀ j : ι, y j ∈ W.baseLattice) {r : ℝ} (hy_le : ∀ j : ι, ‖W.archCoords (y j)‖ ≤ r) :
    1 ≤ ‖W.archCoords ξ‖ * r := by
  -- Otherwise `ξ` is orthogonal to every `y j`, and the form is nondegenerate.
  by_contra! h_lt
  have h_orth : dotProductBilin E E (star ξ) ∘ₗ W.J.mulVecLin = 0 :=
    LinearMap.ext_on_range h_span fun j ↦ form_eq_zero_of_norm_mul_lt_one hξ (hy_mem j)
      (h_lt.trans_le' (mul_le_mul_of_nonneg_left (hy_le j) (norm_nonneg _)))
  refine hξ_ne (star_eq_zero.1 (dotProduct_eq_zero _ fun v ↦ ?_))
  obtain ⟨u, rfl⟩ : ∃ u : n → E, W.J *ᵥ u = v := mulVec_surjective_iff_isUnit.2 W.isUnit_J v
  exact LinearMap.congr_fun h_orth u

/-- A short lattice vector gives a cusp. Let `W` be a space over the CM field `E` in dimension `n`.
Let `1 ≤ κ`, `0 ≤ θ * κ ≤ 1` and `8 f n · rd ≤ κ`, where `f` is the number of infinite places and
`rd` is the root discriminant of `E`. If the first minimum of `W` (cut off at `1`) is below `θ ^ n`,
there is a cusp of size `θ * κ` (`New.Space.CuspFrame`): a nonzero rational isotropic subspace `A`,
with `A` spanned by lattice vectors of length at most `x` and `A^⊥` spanned by lattice vectors of
length at most `y`, where `x * y ≤ θ * κ`. -/
lemma Space.nonempty_cuspFrame (W : Space E n s) {θ κ : ℝ}
    (h_short : W.firstMinimum < θ ^ Fintype.card n) (hκ : 1 ≤ κ) (hθκ_nonneg : 0 ≤ θ * κ)
    (hθκ_le : θ * κ ≤ 1) (h_discr : 8 * (Core.numInfPlaces E * card n) * rootDiscr E ≤ κ) :
    Nonempty (W.CuspFrame (θ * κ)) := by
  -- Take a short vector `ξ` and a Minkowski basis `y` of lengths `α 0 ≤ … ≤ α k`, `k + 1 = #n`.
  -- As `‖ξ‖ * α k ≥ 1`, the other lengths have a small product; pair them from both ends.
  obtain ⟨ξ, hξ, hξ_ne, hξ_short⟩ : ∃ ξ ∈ W.baseLattice, ξ ≠ 0 ∧ ‖W.archCoords ξ‖ < θ ^ card n := by
    by_contra! h_long
    exact h_short.not_ge
      (W.le_firstMinimum_iff.2 ⟨pow_le_one₀ (by nlinarith) (by nlinarith), h_long⟩)
  have hn : Nonempty n := (Function.ne_iff.mp hξ_ne).nonempty
  obtain ⟨k, hk⟩ : ∃ k : ℕ, card n = k + 1 := Nat.exists_eq_succ_of_ne_zero card_ne_zero
  obtain ⟨y, hy_indep, hy_mem, α_mono, α_prod⟩ : ∃ y : Fin (k + 1) → n → E,
      LinearIndependent E y ∧ (∀ j : Fin (k + 1), y j ∈ W.baseLattice) ∧
      (Monotone fun j : Fin (k + 1) ↦ ‖W.archCoords (y j)‖) ∧
      ∏ j : Fin (k + 1), ‖W.archCoords (y j)‖ ≤ κ ^ (k + 1) :=
    W.exists_basis_prod_norm_le hk hκ h_discr
  set α : Fin (k + 1) → ℝ := fun j ↦ ‖W.archCoords (y j)‖
  have h_last : 1 ≤ ‖W.archCoords ξ‖ * α (Fin.last k) :=
    W.one_le_norm_mul_of_span_eq_top hξ hξ_ne
      (hy_indep.span_eq_top_of_card_eq_finrank' (by simp [hk])) hy_mem fun j ↦ α_mono j.le_last
  have h_prod : ∏ j : Fin k, α j.castSucc < (θ * κ) ^ (k + 1) :=
    calc _ ≤ (∏ j : Fin k, α j.castSucc) * (‖W.archCoords ξ‖ * α (Fin.last k)) :=
          le_mul_of_one_le_right (by positivity) h_last
      _ = ‖W.archCoords ξ‖ * ∏ j : Fin (k + 1), α j := by rw [Fin.prod_univ_castSucc, mul_left_comm]
      _ ≤ ‖W.archCoords ξ‖ * κ ^ (k + 1) := by gcongr
      _ < θ ^ card n * κ ^ (k + 1) := by gcongr
      _ = (θ * κ) ^ (k + 1) := by rw [hk, mul_pow]
  obtain ⟨i, hi_le, hi_lt⟩ :
      ∃ i : Fin k, α i.castSucc ≤ α i.rev.castSucc ∧ α i.castSucc * α i.rev.castSucc < θ * κ :=
    exists_le_rev_and_mul_rev_lt (m := fun j ↦ α j.castSucc) hθκ_nonneg <|
      calc (∏ j : Fin k, α j.castSucc) ^ 2 < ((θ * κ) ^ (k + 1)) ^ 2 := by gcongr
        _ = (θ * κ) ^ ((k + 1) * 2) := (pow_mul ..).symm
        _ ≤ (θ * κ) ^ k := pow_le_pow_of_le_one hθκ_nonneg hθκ_le (by omega)
  -- The columns of `X j` are `y 0, …, y j`, the last one repeated.
  let e : n ≃ Fin (k + 1) := equivFinOfCardEq hk
  let X (j : Fin k) : Matrix n n E := (of fun a : n ↦ y (min (e a) j.castSucc))ᵀ
  have h_col (j : Fin k) (a : n) : (X j).col a ∈ W.latticeBall (α j.castSucc) :=
    ⟨hy_mem _, α_mono (min_le_right ..)⟩
  -- Lattice vectors whose lengths have product below `1` are orthogonal.
  have h_orth (j : Fin k) (hj : α j.castSucc ≤ α i.rev.castSucc) : (X i)ᴴ * (W.J * X j) = 0 := by
    refine funext₂ fun a b ↦ form_eq_zero_of_norm_mul_lt_one (h_col i a).1 (h_col j b).1 ?_
    calc _ ≤ α i.castSucc * α i.rev.castSucc :=
          mul_le_mul (h_col i a).2 ((h_col j b).2.trans hj) (norm_nonneg _) (norm_nonneg _)
      _ < 1 := hi_lt.trans_le hθκ_le
  -- The `k - i` independent columns of `X i.rev` lie in the orthogonal of the `i + 1` independent
  -- columns of `X i`, which has dimension `k - i`; so they span it.
  have h_range : (X i.rev).mulVecLin.range = ((X i)ᴴ * W.J).mulVecLin.ker := by
    refine eq_of_le_of_finrank_le (by simp [h_orth i.rev le_rfl, IsConcreteLE.le_iff, mul_assoc]) ?_
    have star_indep : LinearIndependent E fun j : Fin (k + 1) ↦ star (y j) :=
      hy_indep.map_of_injective_injective star (starAddEquiv : (n → E) ≃+ (n → E)).toAddMonoidHom
        (by simp) (by simp) (by simp)
    have rank_left : ((X i)ᴴ * W.J).rank = i + 1 :=
      (rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 W.isUnit_J)).trans
        (rank_of_apply_min e star_indep i.castSucc)
    have rank_right : (X i.rev).rank = i.rev + 1 :=
      (rank_transpose _).trans (rank_of_apply_min e hy_indep i.rev.castSucc)
    rw [← card_sub_rank_eq_finrank_ker, rank_left, ← rank, rank_right, hk, Fin.val_rev]
    omega
  exact ⟨{
    isotropicCols := X i, perpCols := X i.rev, lengthX := α i.castSucc, lengthY := α i.rev.castSucc
    ne_zero := fun h_zero ↦ hy_indep.ne_zero _ (funext fun a ↦ congrFun₂ h_zero a hn.some)
    isotropic := h_orth i hi_le, orthogonal := h_orth i.rev le_rfl
    spans := exists_mul_add_mul_eq_one h_range.ge
    col_isotropicCols_mem := h_col i, col_perpCols_mem := h_col i.rev
    lengthX_le := hi_le, length_mul_le := hi_lt.le }⟩

/-- If `T` is integral at the finite places and of operator norm at most `δ / (6 M)` at the infinite
ones, with `0 < δ ≤ 1`, a point `x` with matrix `radicalElem (stdForm E s) (M • T)`, where
`radicalElem J T = 1 + 2 (T - Tᴴ - Tᴴ J T) J`, has real part within `δ` of `1` and finite part in
the principal level `M`. -/
lemma dist_le_and_mem_principalLevel_of_adeleMatrix_eq {M : ℕ} (hM : M ≠ 0) {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_le : δ ≤ 1) {T : Matrix n n (𝔸 E)} (hT : IsIntBounded (δ / 6 / M) T) {x : G E s}
    (hx : x.adeleMatrix = radicalElem (stdForm E s) (M • T)) :
    dist x.1 1 ≤ δ ∧ x.2 ∈ principalLevel n M := by
  -- We have `x - 1 = M • Z` with `Z` integral and of size `δ / M`.
  have s_small : IsIntBounded 1 (stdForm E s) := by
    simp [IsIntBounded, stdForm, pi_norm_le_iff_of_nonneg, abs_unit_intCast]
  let Z : Matrix n n (𝔸 E) := 2 • ((T - Tᴴ - Tᴴ * stdForm E s * M • T) * stdForm E s)
  have Z_small : IsIntBounded (δ / M) Z := by
    -- The sizes add up to `(2 * δ / 3 + δ ^ 2 / 18) / M`, and `δ ≤ 1`.
    refine ((((hT.sub hT.star).sub ((hT.star.mul s_small).mul (hT.nsmul M))).mul s_small).nsmul
      2).mono ?_
    field_simp
    push_cast
    linarith
  have hZ : x.adeleMatrix - 1 = M • Z := by
    simp [hx, Z, M.cast_comm, radicalElem, two_mul, mul_sub, sub_mul, add_mul, mul_assoc]
  have x_small : IsIntBounded δ (x.adeleMatrix - 1) := by
    simpa only [hZ, mul_div_cancel₀ δ (Nat.cast_ne_zero.2 hM)] using Z_small.nsmul M
  refine ⟨dist_pi_le_iff'.2 fun w ↦ ?_, mem_stdLevel.2 fun i j ↦ ?_,
    fun i j ↦ ⟨(Z i j).2, Z_small.1 i j, ?_⟩⟩
  · change dist (x.adeleMatrix.map (evalInf w)) 1 ≤ δ
    simpa [Matrix.map_sub, ← dist_eq_norm] using x_small.2 w
  · simpa [Matrix.one_apply, apply_ite Prod.snd] using add_mem x_small.1 (one_mem _) i j
  · simpa [Matrix.one_apply, apply_ite] using congrArg Prod.snd (congrFun₂ hZ i j)

/-- Every adelic matrix is near a rational matrix. If `N ≠ 0` lies in the different of `E`, there is
a rounding map `f : 𝔸 E → E` such that every matrix `c` differs from its entrywise rounding by a
matrix that is integral at the finite places and of operator norm at most `n² (2 r)² N` at the
infinite ones, `r` being the number of infinite places. -/
lemma exists_isIntBounded_sub_map {N : ℕ} [NeZero N]
    (hN_diff : (N : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E)) :
    ∃ f : 𝔸 E → E, ∀ c : Matrix n n (𝔸 E), IsIntBounded
      (card n * card n * ((2 * Core.numInfPlaces E) ^ 2 * N)) (c - c.map (toAdele ∘ f)) := by
  have h_near (c : 𝔸 E) : ∃ a : E, c.2 - algebraMap E (𝔸f E) a ∈ Ô E ∧ ∀ w : InfinitePlace E,
      ‖c.1 w - Φ w a‖ ≤ (2 * Core.numInfPlaces E) ^ 2 * ‖Φ w (N : 𝓞 E)‖ :=
    exists_principal_near_of_mem_differentIdeal NeZero.out hN_diff c.1 c.2
  choose f f_int f_near using h_near
  exact ⟨f, fun c ↦ ⟨fun i j ↦ f_int (c i j),
    fun w ↦ l2_opNorm_le_of_apply fun i j ↦ by simpa using f_near (c i j) w⟩⟩

/-- If `Y e + 2 M b Xᴴ J = 1` over `E`, so that the orthogonal of the columns of
`X` lies in the span of those of `Y`, the same relation holds for their images in the adelic frame
of `W`, in which the form is `stdForm E s`. -/
lemma Space.adelicCoords_mul_add_mul_eq_one (W : Space E n s) {X Y e b : Matrix n n E} {M : ℕ}
    (h_one : Y * e + algebraMap E (Matrix n n E) (2 * M) * b * (Xᴴ * W.J) = 1) :
    W.adelicCoords Y * (e.map toAdele * W.x.val) +
      2 * W.adelicCoords b * M * (W.adelicCoords X)ᴴ * stdForm E s = 1 := by
  -- Map the rational identity to the adeles and conjugate it by the point of `W`.
  simpa [Space.adelicCoords, M.cast_comm, W.map_J, Matrix.map_add, Matrix.map_natCast,
      diagonal_natCast, two_mul, mul_add, add_mul, mul_assoc]
    using congrArg (fun Z : Matrix n n E ↦ W.x⁻¹.val * Z.map toAdele * W.x.val) h_one

/-- The rational matrix `radicalElem W.J (P Xᴴ)`, read in the adelic frame of `W`, is the element
`radicalElem` for the standard form with the adelic coordinates of `P` and `X` as parameters. -/
lemma Space.map_radicalElem (W : Space E n s) (P X : Matrix n n E) :
    (radicalElem W.J (P * Xᴴ)).map toAdele =
      W.x.val * radicalElem (stdForm E s) (W.adelicCoords P * (W.adelicCoords X)ᴴ) * W.x⁻¹.val := by
  simp [Space.adelicCoords, radicalElem, W.map_J, Matrix.map_add, Matrix.map_sub, two_mul, mul_sub,
    mul_add, sub_mul, add_mul, mul_assoc]

/-- Let `p` and `a` be the adelic coordinates of rational matrices `P` and `X`. A point `x` with
matrix `radicalElem (stdForm E s) (p aᴴ)` is a rational point of `W`. -/
lemma Space.mem_Gamma_of_adeleMatrix_eq_radicalElem (W : Space E n s) (P X : Matrix n n E)
    {x : G E s}
    (hx : x.adeleMatrix = radicalElem (stdForm E s) (W.adelicCoords P * (W.adelicCoords X)ᴴ)) :
    x ∈ W.Γ :=
  W.mem_Gamma_iff_range.2 (mem_ratMatrices.1 ⟨_, (W.map_radicalElem P X).trans (by rw [hx])⟩)

/-- Reduction by a rational point. Let `Xᴴ J X = Xᴴ J Y = 0` and `Y e + 2 M b Xᴴ J = 1` over `E`,
so that the columns of `X` span an isotropic subspace `A` and those of `Y` span `A^⊥`, and let `a`,
`y` be the adelic coordinates of `X`, `Y`. Let `r` be any map from adelic to rational matrices (a
rounding). For `u` in the radical `N_A` there are adelic matrices `c`, `d` and a rational point `γ`
of `N_A` such that `γ u` is `radicalElem` of `M (y (c - r c) - a (d - r d)) aᴴ`. -/
lemma Space.exists_mem_Gamma_adeleMatrix_mul_eq_radicalElem (W : Space E n s)
    {X Y e b : Matrix n n E} {M : ℕ}
    (hX : Xᴴ * (W.J * X) = 0) (hXY : Xᴴ * (W.J * Y) = 0)
    (h_one : Y * e + algebraMap E (Matrix n n E) (2 * M) * b * (Xᴴ * W.J) = 1)
    (r : Matrix n n (𝔸 E) → Matrix n n E) {u : G E s} (hu : u ∈ W.radical X) :
    ∃ c d : Matrix n n (𝔸 E), ∃ γ ∈ W.Γ ⊓ W.radical X,
      (γ * u).adeleMatrix = radicalElem (stdForm E s)
      (M • ((W.adelicCoords Y * (c - (r c).map toAdele) -
        W.adelicCoords X * (d - (r d).map toAdele)) * (W.adelicCoords X)ᴴ)) := by
  obtain ⟨c, d, x, hx, hx_rad, hx_mul⟩ :=
    exists_radicalElem_mul_eq hu conjTranspose_stdForm isUnit_stdForm
    (W.adelicCoords b) M (fun c ↦ (r c).map toAdele) (Space.adelicCoords_gram_eq_zero hX)
    (Space.adelicCoords_gram_eq_zero hXY) (W.adelicCoords_mul_add_mul_eq_one h_one)
  obtain ⟨γ, rfl⟩ : ∃ γ : G E s, γ.toUnitary = x := toUnitary.surjective x
  -- The parameter of `γ` is rational.
  have h_param : W.adelicCoords ((X * r d - Y * r c) * M) =
      (W.adelicCoords X * (r d).map toAdele - W.adelicCoords Y * (r c).map toAdele) * M := by
    simp [Space.adelicCoords, Matrix.map_sub, Matrix.map_natCast, diagonal_natCast, mul_sub,
      sub_mul, mul_assoc]
  refine ⟨c, d, γ, ⟨W.mem_Gamma_of_adeleMatrix_eq_radicalElem _ X (by rwa [h_param]), hx_rad⟩, ?_⟩
  rwa [nsmul_eq_mul, ← mul_assoc, M.cast_comm, adeleMatrix_mul]

/-- Some matrix `b` over `E` makes the columns of `1 - 2 b Xᴴ J` orthogonal to those of `X` for `J`:
take `2 b` to be a generalised inverse of `Xᴴ J`. -/
lemma exists_orthogonal_one_sub (J X : Matrix n n E) :
    ∃ b : Matrix n n E, Xᴴ * (J * (1 - 2 * b * (Xᴴ * J))) = 0 := by
  obtain ⟨σ, hσ⟩ := exists_generalized_inverse (Xᴴ * J).toLin'
  have h_inv : Xᴴ * J * (σ.toMatrix' * (Xᴴ * J)) = Xᴴ * J := ext_iff_mulVec.2 fun v ↦ by
    simpa only [← mulVec_mulVec, LinearMap.toMatrix'_mulVec, toLin'_apply] using hσ v
  have h_half : 2 * ((2⁻¹ : E) • σ.toMatrix') = σ.toMatrix' := by norm_num [two_mul, ← add_smul]
  exact ⟨(2⁻¹ : E) • σ.toMatrix', by rw [h_half, ← mul_assoc, mul_sub, mul_one, h_inv, sub_self]⟩

/-- Let `A` be a rational isotropic subspace of the hermitian space `W`, spanned by the columns of
`X`. The group `Γ ∩ N_A` of rational points is cocompact in the adelic unipotent radical `N_A`.

A case of the compactness of `N(F) \ N(𝔸)` for a unipotent group `N` over a number field `F`. -/
theorem Space.isCocompact_radical (W : Space E n s) {X : Matrix n n E} (hX : Xᴴ * (W.J * X) = 0) :
    (W.Γ.subgroupOf (W.radical X)).IsCocompact := by
  -- A point of the radical has two adelic matrices as parameters. A rational point of the radical
  -- moves both into a compact set `C`, because `E` is cocompact in its adeles. The parameters
  -- refer to `X` and to `Y = 1 - 2 b Xᴴ J`, whose columns span `A^⊥` when `2 b` is a generalised
  -- inverse of `Xᴴ J`.
  obtain ⟨b, hb⟩ := exists_orthogonal_one_sub W.J X
  let Y : Matrix n n E := 1 - 2 * b * (Xᴴ * W.J)
  have h_one : Y * 1 + algebraMap E (Matrix n n E) (2 * (1 : ℕ)) * b * (Xᴴ * W.J) = 1 := by
    rw [Nat.cast_one, mul_one, mul_one, map_ofNat, sub_add_cancel]
  let a : Matrix n n (𝔸 E) := W.adelicCoords X
  let y : Matrix n n (𝔸 E) := W.adelicCoords Y
  have a_iso : aᴴ * (stdForm E s * a) = 0 := Space.adelicCoords_gram_eq_zero hX
  have y_orth : aᴴ * (stdForm E s * y) = 0 := Space.adelicCoords_gram_eq_zero hb
  obtain ⟨C, hC, h_cover⟩ : ∃ C : Set (Matrix n n (𝔸 E)), IsCompact C ∧
      ∀ c : Matrix n n (𝔸 E), ∃ γ ∈ ratMatrices E n n, γ + c ∈ C :=
    IsCovolOneLattice.exists_compact_cover (ratMatrices E n n)
  have h_near (c : Matrix n n (𝔸 E)) : ∃ r : Matrix n n E, c - r.map toAdele ∈ C := by
    obtain ⟨_, ⟨r, rfl⟩, hr⟩ := h_cover c
    exact ⟨-r, by simpa [Matrix.map_neg, add_comm] using hr⟩
  choose r hr using h_near
  -- The compact set is cut out by the image of `C × C` under the parametrisation `φ`.
  have h_orth (c d : Matrix n n (𝔸 E)) : aᴴ * (stdForm E s * (y * c - a * d)) = 0 := by
    simp [mul_sub, ← mul_assoc (stdForm E s), ← mul_assoc aᴴ _ c, ← mul_assoc aᴴ _ d, y_orth, a_iso]
  let φ (p : Matrix n n (𝔸 E) × Matrix n n (𝔸 E)) : G E s :=
    ofMatrix (radicalElem (stdForm E s) ((y * p.fst - a * p.snd) * aᴴ))
      (Reduction.gram_radicalElem conjTranspose_stdForm a_iso (h_orth p.fst p.snd))
  have hφ : Continuous φ := by
    simp only [G.continuous_iff, φ, adeleMatrix_ofMatrix, radicalElem]
    fun_prop
  refine ⟨Subtype.val ⁻¹' (φ '' C ×ˢ C), ((hC.prod hC).image hφ).preimage_val, fun u ↦ ?_⟩
  obtain ⟨c, d, γ, ⟨hγ_rat, hγ_rad⟩, hγu⟩ :=
    W.exists_mem_Gamma_adeleMatrix_mul_eq_radicalElem hX hb h_one r u.property
  have h_prod : φ (c - (r c).map toAdele, d - (r d).map toAdele) = γ * u :=
    ext_adeleMatrix (by rw [hγu, one_smul, adeleMatrix_ofMatrix])
  exact ⟨⟨γ, hγ_rad⟩, hγ_rat, _, ⟨hr c, hr d⟩, h_prod⟩

/-- Reduction in the radical of a cusp. Let `N ≠ 0` lie in the different of `E`, let `M ≠ 0` and
`0 < δ ≤ 1`, and let `κ = New.cuspConst E n N = 8 f n · rd + 48 n⁶ f² N + 1` (`f` the number of
infinite places, `rd` the root discriminant of `E`). Let `A` be a cusp of `W` of size `δ / (M κ)`: a
nonzero rational isotropic subspace, spanned by the columns of `A.isotropicCols`, with `A` spanned
by lattice vectors of length at most `x` and `A^⊥` spanned by lattice vectors of length at most `y`,
where `x * y ≤ δ / (M κ)`. Then the radical `N_A` lies in `(Γ ∩ N_A) Z_δ K(M)`
(`New.Space.RadicalCovered`), where `Γ` is the group of rational points of `W`, `Z_δ` is the real
ball of radius `δ` about `1`, and `K(M)` is the principal level `M`. -/
lemma Space.CuspFrame.radicalCovered {W : Space E n s} {N : ℕ} [NeZero N]
    (hN_diff : (N : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E)) {M : ℕ} (hM : M ≠ 0) {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_le : δ ≤ 1) (A : W.CuspFrame (δ / (M * cuspConst E n N))) :
    W.RadicalCovered A.isotropicCols δ (principalLevel n M) := by
  -- A rational point of the radical, with parameters near those of `u`, leaves only the small
  -- remainders as parameters of the product.
  intro u hu
  have hκ : 1 ≤ cuspConst E n N := one_le_cuspConst E n N
  obtain ⟨X, Y, lenX, lenY, hX_ne, hX, hXY, ⟨coeffY, coeffX, h_spans⟩, hX_col, hY_col, hlen_le,
    h_prod⟩ := A
  have hlenX : 0 ≤ lenX := (norm_nonneg _).trans (hX_col (Function.ne_iff.1 hX_ne).choose).2
  have hlenY : 0 ≤ lenY := hlenX.trans hlen_le
  obtain ⟨round, h_approx⟩ := exists_isIntBounded_sub_map (n := n) hN_diff
  -- Reduce `u` in the radical with the factor `M` in all parameters, so that the remainder is
  -- divisible by `M`; for this, write `coeffX` as a multiple of `2 * M`.
  obtain ⟨coeffX, rfl⟩ : ∃ b : Matrix n n E, coeffX = algebraMap E (Matrix n n E) (2 * M) * b :=
    (IsUnit.map _ (by simpa)).dvd
  obtain ⟨c, d, γ, hγ, hγu⟩ :=
    W.exists_mem_Gamma_adeleMatrix_mul_eq_radicalElem hX hXY h_spans (fun c ↦ c.map round) hu
  -- The remainder is small because `lenX * lenY` is: this uses the second summand of `cuspConst`.
  have T_small : IsIntBounded (δ / 6 / M) ((W.adelicCoords Y * (c - c.map (toAdele ∘ round)) -
      W.adelicCoords X * (d - d.map (toAdele ∘ round))) * (W.adelicCoords X)ᴴ) := by
    have X_small : IsIntBounded (card n * card n * lenX) (W.adelicCoords X) :=
      Space.isIntBounded_adelicCoords hX_col
    have Y_small : IsIntBounded (card n * card n * lenY) (W.adelicCoords Y) :=
      Space.isIntBounded_adelicCoords hY_col
    refine (((Y_small.mul (h_approx c)).sub (X_small.mul (h_approx d))).mul X_small.star).mono ?_
    have h_const : 48 * card n ^ 6 * Core.numInfPlaces E ^ 2 * N ≤ cuspConst E n N :=
      le_add_of_nonneg_of_le (by positivity [rootDiscr_pos E]) (le_add_of_nonneg_right zero_le_one)
    calc _ = 4 * card n ^ 6 * Core.numInfPlaces E ^ 2 * N * ((lenY + lenX) * lenX) := by ring
      _ ≤ 4 * card n ^ 6 * Core.numInfPlaces E ^ 2 * N * ((lenY + lenY) * lenX) := by gcongr
      _ = 48 * card n ^ 6 * Core.numInfPlaces E ^ 2 * N / 6 * (lenX * lenY) := by ring
      _ ≤ cuspConst E n N / 6 * (δ / (M * cuspConst E n N)) := by gcongr
      _ = δ / 6 / M := by field_simp
  exact ⟨γ, hγ, dist_le_and_mem_principalLevel_of_adeleMatrix_eq hM hδ_pos hδ_le T_small hγu⟩

/-- A point with a short vector lies high in a cusp. Let `N ≠ 0` lie in the different of `E`, let
`M ≠ 0` and `0 < δ ≤ 1`. Suppose the first minimum (cut off at 1) of the lattice of `W` is less than
`(δ / (M κ²))ⁿ`, where `κ = New.cuspConst E n N`. Then there is a cusp `A` of size `δ` whose radical
`N_A` lies in `(Γ ∩ N_A) Z_δ J(M)`. Such a cusp is a nonzero rational isotropic subspace, spanned by
the columns of `A.isotropicCols`, with `A` and `A^⊥` spanned by lattice vectors of lengths at most
`a`, `b` where `a b ≤ δ`. Here `Γ` is the group of rational points of `W`, `Z_δ` is the real ball of
radius `δ` about `1` and `J(M)` is the principal level `M`. For `W = V.move g` this is the inclusion
`N_A g ⊆ (Γ ∩ N_A) g Z_δ J(M)`. -/
theorem Space.exists_cuspFrame (W : Space E n s) {N : ℕ} [NeZero N]
    (hN_diff : (N : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E)) {M : ℕ} (hM : M ≠ 0) {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_le : δ ≤ 1) (h_short : W.firstMinimum < (δ / (M * cuspConst E n N ^ 2)) ^ Fintype.card n) :
    ∃ A : W.CuspFrame δ, W.RadicalCovered A.isotropicCols δ (principalLevel n M) := by
  have hκ : 1 ≤ cuspConst E n N := one_le_cuspConst E n N
  have h_le : δ / (M * cuspConst E n N) ≤ δ :=
    div_le_self hδ_pos.le (one_le_mul_of_one_le_of_one_le (mod_cast hM.pos) hκ)
  have h_size : δ / (M * cuspConst E n N ^ 2) * cuspConst E n N = δ / (M * cuspConst E n N) := by
    field_simp
  obtain ⟨A⟩ : Nonempty (W.CuspFrame (δ / (M * cuspConst E n N))) := by
    rw [← h_size]
    exact W.nonempty_cuspFrame h_short hκ (by positivity) (h_size.trans_le (h_le.trans hδ_le))
      (le_add_of_nonneg_right (by positivity))
  exact ⟨{ A with length_mul_le := A.length_mul_le.trans h_le },
    A.radicalCovered hN_diff hM hδ_pos hδ_le⟩

/-- Let `A ≠ 0` be the rational isotropic subspace spanned by the columns of `X`, let `J` be a
compact open subgroup of `Gf E n` inside the standard level, called a level, and let
`N_A g ⊆ (Γ ∩ N_A) g Z_δ J` (`New.Space.RadicalCovered`), with `Z_δ` the real ball of radius `δ`
about `1`. A bounded continuous function `F` that is fixed by a cusp kernel `e` and by `J`, and left
invariant under the rational points of the radical `N_A`, is bounded at `g y`, for `y` real, by its
oscillation `D` on `g Z_δ y`. -/
theorem Space.norm_le_of_oscillation [Nonempty n] (he : IsCuspKernel B e) {X : Matrix n n E}
    (hX_ne : X ≠ 0) (hX : Xᴴ * (V.J * X) = 0) {J : Subgroup (Gf E n)} [hJ : IsLevel J] {δ : ℝ}
    {g : G E s} (h_cover : (V.move g).RadicalCovered X δ J) (h_cont : Continuous F) {T : ℝ}
    (hT : ∀ x : G E s, ‖F x‖ ≤ T) (h_fix : realConv e F = F) (h_level : HasLevel F J)
    (h_inv : ∀ ν : U V.J, (ν, 1) ∈ dilationGroup (m := n) X →
      ∀ x : G E s, F (V.ratEmbed ν * x) = F x) (y : GInf E s) {D : ℝ}
    (hD : ∀ z : GInf E s, dist z 1 ≤ δ → ‖F (g * (z * y, 1)) - F (g * (y, 1))‖ ≤ D) :
    ‖F (g * (y, 1))‖ ≤ D := by
  have hK : IsCompact (Metric.closedBall (1 : GInf E s) δ ×ˢ (J : Set (Gf E n))) :=
    (isCompact_closedBall 1 δ).prod hJ.isCompact
  refine (V.move g).norm_le_of_dist_le he (Space.adelicCoords_gram_eq_zero (W := V.move g) hX)
    (Space.adelicCoords_evalInf_ne_zero hX_ne) hK h_cover h_cont hT h_fix ?_ y ?_
  · rintro _ ⟨⟨ν, rfl⟩, hν⟩ x
    have h_move : g * ((V.move g).ratEmbed ν * x) = V.ratEmbed ν * (g * x) := by
      rw [V.ratEmbed_move g ν, mul_assoc, mul_assoc, mul_inv_cancel_left]
    change F (g * ((V.move g).ratEmbed ν * x)) = F (g * x)
    rw [h_move]
    exact h_inv ν (Space.mem_dilationGroup_of_ratEmbed_mem_radical (W := V.move g) hν) _
  · rintro ⟨z, k⟩ ⟨hz, hk⟩
    have h_split : g * ((z, k) * (y, 1)) = g * (z * y, 1) * (1, k) := by simp [mul_assoc]
    rw [h_split, h_level k hk, dist_eq_norm]
    exact hD z hz

/-- A continuous function `F` on `Γ \ G`, with `Γ = V.Γ` the group of rational points, is cuspidal
if its constant terms vanish: the integral of `F (u g)` over `u ∈ (Γ ∩ N_A) \ N_A` is zero for every
point `g` and every rational isotropic subspace `A ≠ 0`, with unipotent radical `N_A`. -/
structure Space.IsCuspidal (V : Space E n s) (F : G E s → ℂ) : Prop where
  /-- `F` is continuous. -/
  continuous : Continuous F
  /-- `F` is left invariant under the rational points. -/
  rat_mul : V.Γ.FixesLeft F
  /-- The integral is written in the frame at `g`, over `v = g⁻¹ u g`, and `A` is spanned by the
  columns of `X`. It is taken against the quotient measure, which is finite because the quotient is
  compact (`New.Space.isCocompact_radical`). -/
  integral_eq_zero (g : G E s) (X : Matrix n n E) (hX_ne : X ≠ 0) (hX : Xᴴ * (V.J * X) = 0) :
    ∫ v : (V.move g).radical X, F (g * v)
      ∂((V.move g).Γ.subgroupOf ((V.move g).radical X)).quotMeasure .haar = 0

/-- A function that is left invariant under the rational points of `V`, read in the frame at `g`, is
left invariant under the rational points of `V.move g`. -/
lemma Space.fixesLeft_move (hF : V.Γ.FixesLeft F) (g : G E s) :
    (V.move g).Γ.FixesLeft fun x : G E s ↦ F (g * x) := by
  rintro _ ⟨ν, rfl⟩ x
  simpa only [V.ratEmbed_move g ν, mul_assoc, mul_inv_cancel_left] using hF _ ⟨ν, rfl⟩ (g * x)

/-- Let `e` be a cusp kernel of order `B` on `G_∞`: a minimal idempotent with ‖x‖^(B+1) e(x)
integrable, ‖x‖^B e(x) bounded, and α ∗ e = e for some continuous compactly supported α. Let `F` be
a form of type `e` for `V`, that is, a bounded automorphic function fixed by right convolution with
`e`. Then `F` is cuspidal: its constant terms along the unipotent radicals of nonzero rational
isotropic subspaces vanish. -/
theorem Space.IsForm.isCuspidal (hF : V.IsForm e F) (he : IsCuspKernel B e) : V.IsCuspidal F := by
  refine ⟨hF.continuous, hF.rat_mul, fun g X hX_ne hX ↦ ?_⟩
  have : Nonempty n := (Function.ne_iff.1 hX_ne).nonempty
  obtain ⟨T, hT⟩ := hF.bounded
  have h_inv : ((V.move g).Γ ⊓ (V.move g).radical X).FixesLeft fun x : G E s ↦ F (g * x) :=
    fun γ hγ ↦ Space.fixesLeft_move hF.rat_mul g γ hγ.1
  have h_fin : IsFiniteMeasure
      (((V.move g).Γ.subgroupOf ((V.move g).radical X)).quotMeasure .haar) :=
    isFiniteMeasure_quotMeasure_of_cocompact .haar ((V.move g).isCocompact_radical hX)
  -- The constant term is the mean along the radical at the real point `1`.
  simpa only [Prod.mk_one_one, mul_one] using (V.move g).integral_unipotentRadical_eq_zero he
    (Space.adelicCoords_gram_eq_zero (W := V.move g) hX) (Space.adelicCoords_evalInf_ne_zero hX_ne)
    h_fin hF.continuous hT (hF.realConv_eq he.integrable) h_inv 1

/-- High in a cusp, a cuspidal function is bounded by its oscillation. Let `F` be a cuspidal
function of level `New.principalLevel n M` with `M ≠ 0`. Let `N ≠ 0` be a natural number in the
different of `E`, and let `0 < δ ≤ 1`. Suppose the first minimum of the lattice at `g` is less than
`(δ / (M κ²))ⁿ`, where `κ = New.cuspConst E n N`. If `‖F (g x) - F g‖ ≤ C` for every real `x` with
`dist x 1 ≤ δ`, then `‖F g‖ ≤ C`. -/
theorem Space.IsCuspidal.norm_le_of_firstMinimum_lt (hF : V.IsCuspidal F) {N : ℕ} [NeZero N]
    (hN_diff : (N : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E)) {M : ℕ} (hM : M ≠ 0)
    (h_level : HasLevel F (principalLevel n M)) {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    {g : G E s} {C : ℝ}
    (h_short : (V.move g).firstMinimum < (δ / (M * cuspConst E n N ^ 2)) ^ Fintype.card n)
    (hC : ∀ x : GInf E s, dist x 1 ≤ δ → ‖F (g * (x, 1)) - F g‖ ≤ C) : ‖F g‖ ≤ C := by
  -- `F g` is the mean of `F g - F (u g)` over the compact quotient of the radical of the cusp.
  obtain ⟨A, h_cover⟩ := (V.move g).exists_cuspFrame hN_diff hM hδ_pos hδ_le h_short
  have hJ : IsLevel (principalLevel n (M : 𝓞 E)) :=
    ⟨principalLevel_le_stdLevel, isOpen_principalLevel (Nat.cast_ne_zero.2 hM)⟩
  refine (V.move g).norm_le_of_integral_eq_zero ((isCompact_closedBall 1 δ).prod hJ.isCompact)
    h_cover (f := fun x ↦ F (g * x)) (hF.continuous.comp (continuous_const_mul g))
    (fun γ hγ ↦ fixesLeft_move hF.rat_mul g γ hγ.1)
    (hF.integral_eq_zero g A.isotropicCols A.ne_zero A.isotropic) ?_
  rintro ⟨z, k⟩ ⟨hz, hk⟩
  have h_split : g * (z, k) = g * (z, 1) * (1, k) := by simp [mul_assoc]
  rw [h_split, h_level k hk, dist_eq_norm]
  exact hC z hz

/-- High in a cusp, a form is bounded by its oscillation. Let `F` be a form of type `e`, with `e` a
cusp kernel, and of principal level `M ≠ 0`. Let `N ≠ 0` lie in the different of `E`, and let
`0 < δ ≤ 1`. If the first minimum of the lattice at `g` is less than `(δ / (M κ²))ⁿ`, where
`κ = New.cuspConst E n N`, then `‖F g‖` is at most the oscillation `C` of `F` at `g` under real
right translations of size `δ`. -/
theorem Space.IsForm.norm_le_of_firstMinimum_lt (hF : V.IsForm e F) (he : IsCuspKernel B e) {N : ℕ}
    [NeZero N] (hN_diff : (N : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E)) {M : ℕ} (hM : M ≠ 0)
    (h_level : HasLevel F (principalLevel n M)) {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    {g : G E s} {C : ℝ}
    (h_short : (V.move g).firstMinimum < (δ / (M * cuspConst E n N ^ 2)) ^ Fintype.card n)
    (hC : ∀ x : GInf E s, dist x 1 ≤ δ → ‖F (g * (x, 1)) - F g‖ ≤ C) : ‖F g‖ ≤ C :=
  (hF.isCuspidal he).norm_le_of_firstMinimum_lt hN_diff hM h_level hδ_pos hδ_le h_short hC

end New

/-! ## Rapid decay, finite dimension at each level, and projection to type `e` -/

section FiniteDimension

open NumberField MeasureTheory Set Ideal Matrix Matrix.Norms.L2Operator

namespace New.Space

variable {E n : Type} {s : n → ℤˣ} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {V : Space E n s} {e : GInf E s → ℂ} {F : G E s → ℂ} {B : ℕ}

/-- Conjugation by a real point `z` multiplies the distance to `1` by at most `‖z‖ ^ 2`, where `‖z‖`
is the product over the infinite places of the operator norms. -/
lemma dist_conj_one_le [Nonempty n] (z x : GInf E s) :
    dist (z⁻¹ * x * z) 1 ≤ (∏ w : InfinitePlace E, ‖(z w : Matrix n n ℂ)‖) ^ 2 * dist x 1 := by
  -- At each place `z⁻¹ x z - 1 = z⁻¹ (x - 1) z`, and `z⁻¹` has the norm of `z`.
  refine dist_pi_le_iff'.2 fun w ↦ ?_
  calc dist ((z⁻¹ * x * z) w) 1
      = ‖(((z w)⁻¹ : USign s) : Matrix n n ℂ) * ((x w : Matrix n n ℂ) - 1) * z w‖ :=
      (dist_eq_norm ((z⁻¹ * x * z) w : Matrix n n ℂ) 1).trans (by simp [mul_sub, sub_mul])
    _ ≤ ‖(z w : Matrix n n ℂ)‖ * ‖(x w : Matrix n n ℂ) - 1‖ * ‖(z w : Matrix n n ℂ)‖ :=
      norm_mul_le_of_le (norm_mul_le_of_le (U.norm_inv (z w)).le le_rfl) le_rfl
    _ = ‖(z w : Matrix n n ℂ)‖ ^ 2 * dist (x w) 1 := by
      rw [← dist_eq_norm, mul_right_comm, ← sq]
      rfl
    _ ≤ (∏ w : InfinitePlace E, ‖(z w : Matrix n n ℂ)‖) ^ 2 * dist x 1 := by
      gcongr
      exacts [(le_prod_opNorm z).2 w, dist_le_pi_dist x 1 w]

/-- The product over the infinite places of the operator norms is submultiplicative. -/
lemma prod_opNorm_mul_le (z v : GInf E s) :
    ∏ w : InfinitePlace E, ‖((z * v) w : Matrix n n ℂ)‖ ≤
      (∏ w : InfinitePlace E, ‖(z w : Matrix n n ℂ)‖) *
        ∏ w : InfinitePlace E, ‖(v w : Matrix n n ℂ)‖ := by
  rw [← Finset.prod_mul_distrib]
  gcongr with w
  exact norm_mul_le _ _

/-- Small oscillation. For a cusp kernel `e` and `j ≥ 0` there is `δ₀ > 0` with the following
property. If a bounded continuous function `f` is fixed by `e` and `|f (g v)| ≤ C ‖v‖ ^ j` for all
real `v`, where `‖v‖` is the product over the infinite places of the operator norms, then
`|f (g u) - f g| ≤ C / 2` for the real `u` within `δ₀` of `1`. -/
lemma exists_norm_sub_le_half (he : IsCuspKernel B e) (j : ℕ) : ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ (f : G E s → ℂ) (T C : ℝ) (g : G E s) (u : GInf E s) (_ : Continuous f)
      (_h_bound : ∀ x : G E s, ‖f x‖ ≤ T) (_h_fix : realConv e f = f) (_hC_nonneg : 0 ≤ C)
      (_h_growth : ∀ v : GInf E s,
        ‖f (g * (v, 1))‖ ≤ C * (∏ w : InfinitePlace E, ‖(v w : Matrix n n ℂ)‖) ^ j)
      (_h_near : dist u 1 ≤ δ₀), ‖f (g * (u, 1)) - f g‖ ≤ C / 2 := by
  -- The bump `α` reproduces `e`, so `f = R(α) f`. The constant `c` bounds the norm on
  -- `Ω = Z_1 · supp α`, and translation by `Z_{δ₀}` moves `α` by at most `c ^ (-j) / 2` in `L¹`.
  let size (z : GInf E s) : ℝ := ∏ w : InfinitePlace E, ‖(z w : Matrix n n ℂ)‖
  obtain ⟨α, -, hα⟩ := he.exists_realConv_realConv_eq
  let Ω : Set (GInf E s) := image2 (fun u x ↦ u * x) (Metric.closedBall 1 1) (tsupport α)
  obtain ⟨c, one_le_c, hc⟩ : ∃ c : ℝ, 1 ≤ c ∧ ∀ y ∈ size '' Ω, y ≤ c :=
    (((isCompact_closedBall 1 1).mul α.hasCompactSupport).bddAbove_image (by fun_prop)).exists_ge 1
  obtain ⟨r, hr_pos, h_translate⟩ : ∃ r : ℝ, 0 < r ∧ ∀ ⦃u : GInf E s⦄, dist u 1 ≤ r →
      ∫ x : GInf E s, ‖α (u⁻¹ * x) - α x‖ < (c ^ j)⁻¹ / 2 :=
    Metric.nhds_basis_closedBall.eventually_iff.1
      ((tendsto_integral_norm_translate_sub α.integrable).eventually_lt_const (by positivity))
  refine ⟨min r 1, by positivity, fun f T C g u h_cont h_bound h_fix hC h_growth h_near ↦ ?_⟩
  have h_fix_α : realConv α f = f := by
    simpa only [h_fix] using hα f (.of_continuous ⟨T, h_bound⟩ h_cont)
  have h_le (v : GInf E s) (hv : α (u⁻¹ * v) ≠ α v) : ‖f (g * (v, 1))‖ ≤ C * c ^ j := by
    suffices hvΩ : v ∈ Ω by grw [h_growth v, ← hc _ (mem_image_of_mem size hvΩ)]
    rcases hv.ne_or_ne 0 with h_left | h_right
    · exact ⟨u, h_near.trans inf_le_right, _, subset_closure h_left, mul_inv_cancel_left u v⟩
    · exact ⟨1, Metric.mem_closedBall_self zero_le_one, v, subset_closure h_right, one_mul v⟩
  calc ‖f (g * (u, 1)) - f g‖ = ‖realConv α f (g * (u, 1)) - realConv α f g‖ := by rw [h_fix_α]
    _ ≤ (∫ x : GInf E s, ‖α (u⁻¹ * x) - α x‖) * (C * c ^ j) :=
        norm_realConv_mul_sub_le (.of_continuous ⟨T, h_bound⟩ h_cont) α.integrable g u
          (by positivity) h_le
    _ ≤ (c ^ j)⁻¹ / 2 * (C * c ^ j) := by grw [h_translate (h_near.trans inf_le_left)]
    _ = C / 2 := by field_simp

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Rapid decay in a cusp. For a cusp kernel `e` and `j ≥ 0` there is `δ₀ > 0` with the following
property. Let `J` be a level, `W` a space, and let `A ≠ 0` be a rational isotropic subspace of it,
spanned by the columns of `X`, with `N_A g ⊆ (Γ ∩ N_A) g Z_δ J` (`New.Space.RadicalCovered`; `N_A`
is the unipotent radical, `Γ` the group of rational points, `Z_δ` the real ball of radius `δ` about
`1`). If a continuous function `f` bounded by `T` is left invariant under `Γ ∩ N_A` and fixed by
`J` and by `e`, then `|f g| ≤ (δ / δ₀) ^ j T`. -/
theorem exists_norm_le_of_radicalCovered (he : IsCuspKernel B e) [Nonempty n] (j : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ (J : Subgroup (Gf E n)) [IsLevel J] (W : Space E n s) (g : G E s) (δ : ℝ) (X : Matrix n n E)
      (_hδ : 0 ≤ δ) (_hX_ne : X ≠ 0) (_hX_iso : Xᴴ * (W.J * X) = 0)
      (_h_cover : (W.move g).RadicalCovered X δ J) (f : G E s → ℂ) (T : ℝ) (_h_cont : Continuous f)
      (_h_bound : ∀ x : G E s, ‖f x‖ ≤ T) (_h_fix : realConv e f = f) (_h_level : HasLevel f J)
      (_h_inv : ∀ ν : U W.J, (ν, 1) ∈ dilationGroup (m := n) X →
        ∀ x : G E s, f (W.ratEmbed ν * x) = f x),
      ‖f g‖ ≤ (δ / δ₀) ^ j * T := by
  -- The mean of `f` along the radical vanishes, so `f (g z)` is bounded by an oscillation, which is
  -- small as long as `δ ‖z‖ ^ 2` is; the other real `z` get a small weight. So every bound for
  -- `|f (g z)| ‖z‖ ^ (-2 j)` can be halved until it reaches `(δ / δ₀) ^ j T`.
  let size (z : GInf E s) : ℝ := ∏ w : InfinitePlace E, ‖(z w : Matrix n n ℂ)‖
  have one_le_size (z : GInf E s) : 1 ≤ size z := (le_prod_opNorm z).1
  have size_mul_le (z v : GInf E s) : size (z * v) ≤ size z * size v := prod_opNorm_mul_le z v
  have weight_pos (z : GInf E s) : 0 < size z ^ (2 * j) := by positivity [one_le_size z]
  obtain ⟨δ₀, hδ₀, h_osc⟩ := exists_norm_sub_le_half he (2 * j)
  refine ⟨δ₀, hδ₀, fun J _ W g δ X hδ hX_ne hX h_cover f T h_cont h_bound h_fix h_level h_inv ↦ ?_⟩
  have hT_nonneg : 0 ≤ T := (norm_nonneg _).trans (h_bound 1)
  suffices h_weighted : ∀ z : GInf E s, ‖f (g * (z, 1))‖ / size z ^ (2 * j) ≤ (δ / δ₀) ^ j * T by
    simpa [Prod.mk_one_one, size] using h_weighted 1
  refine le_of_halving (B := T)
    (fun z ↦ (div_le_self (norm_nonneg _) (one_le_pow₀ (one_le_size z))).trans (h_bound _))
    (by positivity) fun C hC₀ hC z ↦ ?_
  rcases le_total (size z ^ 2 * δ) δ₀ with h_small | h_large
  · -- Halving: `g x z = g z u` with `u = z⁻¹ x z` in `Z_{δ₀}`.
    refine .inl ((div_le_iff₀ (weight_pos z)).2 (norm_le_of_oscillation he hX_ne hX h_cover
      h_cont h_bound h_fix h_level h_inv z fun x hx ↦ ?_))
    have h_near : dist (z⁻¹ * x * z) 1 ≤ δ₀ :=
      ((dist_conj_one_le z x).trans (by gcongr)).trans h_small
    have h_conj : g * (x * z, 1) = g * (z, 1) * (z⁻¹ * x * z, 1) := by simp [mul_assoc]
    have h_growth (v : GInf E s) :
        ‖f (g * (z, 1) * (v, 1))‖ ≤ C * size z ^ (2 * j) * size v ^ (2 * j) :=
      calc _ = ‖f (g * (z * v, 1))‖ := by rw [mul_assoc, Prod.mk_mul_mk z, one_mul]
        _ ≤ C * size (z * v) ^ (2 * j) := (div_le_iff₀ (weight_pos _)).1 (hC _)
        _ ≤ C * (size z * size v) ^ (2 * j) := by grw [size_mul_le z v]
        _ = C * size z ^ (2 * j) * size v ^ (2 * j) := by rw [mul_pow, mul_assoc]
    rw [h_conj, div_mul_eq_mul_div]
    exact h_osc f T _ (g * (z, 1)) _ h_cont h_bound h_fix (by positivity) h_growth h_near
  · -- For the other `z` the weight is at most `(δ / δ₀) ^ j`.
    have h_weight : 1 ≤ (δ / δ₀) ^ j * size z ^ (2 * j) := by
      rw [pow_mul, ← mul_pow]
      exact one_le_pow₀ (by rwa [div_mul_eq_mul_div, one_le_div hδ₀, mul_comm])
    refine .inr ((div_le_iff₀ (weight_pos z)).2 ?_)
    grw [h_bound, mul_right_comm, ← h_weight, one_mul]

/-- For an open subgroup `J` there is `κ > 0` such that for every space `V` and point `g` there is
`δ > 0` with `δ ^ n = κ / V.height g` and, if `δ ≤ 1` (the height is at least `κ`), a cusp `A` of
size `δ` at `g` whose radical satisfies `N_A g ⊆ (Γ ∩ N_A) g Z_δ J` (`New.Space.RadicalCovered`). -/
theorem exists_cuspFrame_of_height [Nonempty n] (J : OpenSubgroup (Gf E n)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (V : Space E n s) (g : G E s), ∃ δ : ℝ, 0 < δ ∧
      δ ^ Fintype.card n * V.height g = κ ∧
      (δ ≤ 1 → ∃ A : (V.move g).CuspFrame δ, (V.move g).RadicalCovered A.isotropicCols δ J) := by
  obtain ⟨M, hM, hMJ⟩ := exists_principalLevel_subset J.mem_nhds_one
  let N : ℕ := absNorm (differentIdeal ℤ (𝓞 E))
  let c : ℝ := M * cuspConst E n N ^ 2
  have hc : 0 < c := by positivity [one_le_cuspConst E n N]
  refine ⟨2 * c ^ Fintype.card n, by positivity, fun V g ↦ ?_⟩
  have h_pos : 0 < V.height g := V.height_pos g
  obtain ⟨δ, hδ_pos, hδ⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ ^ Fintype.card n = 2 * c ^ Fintype.card n / V.height g :=
    ⟨_, by positivity, Real.rpow_inv_natCast_pow (by positivity) Fintype.card_ne_zero⟩
  refine ⟨δ, hδ_pos, by rw [hδ, div_mul_cancel₀ _ h_pos.ne'], fun hδ_le ↦ ?_⟩
  have h_short : (V.move g).firstMinimum < (δ / c) ^ Fintype.card n :=
    calc _ < 2 * (V.move g).firstMinimum := lt_two_mul_self (V.move g).firstMinimum_pos
      _ = (δ / c) ^ Fintype.card n := by simp [div_pow, hδ, height, field]
  obtain ⟨A, h_cover⟩ := (V.move g).exists_cuspFrame (absNorm_mem _) hM hδ_pos hδ_le h_short
  exact ⟨A, fun u hu ↦ (h_cover u hu).imp fun γ ⟨hγ, h_inf, h_fin⟩ ↦ ⟨hγ, h_inf, hMJ h_fin⟩⟩

/-- Forms of a fixed level decay uniformly against every power of the height. Let `e` be a cusp
kernel of order `B` (a minimal idempotent on `G_∞` with ‖x‖^(B+1) e(x) integrable, ‖x‖^B e(x)
bounded, and α ∗ e = e for some continuous compactly supported α), `K` an open subgroup of `G_f`,
and `A : ℕ`. Then there is `R` such that every form `F` of type `e` (bounded automorphic, fixed by
right convolution with `e`) that is right `K`-invariant and bounded by `c` has
`‖F g‖ * V.height g ^ A ≤ c * R` for all `g`, where `V.height g` is the reciprocal of the first
minimum, cut off at 1, of `V.move g`. -/
theorem exists_norm_mul_height_pow_le (he : IsCuspKernel B e) (K : OpenSubgroup (Gf E n)) (A : ℕ) :
    ∃ R : ℝ, ∀ {F : G E s → ℂ} {c : ℝ} (_h_form : V.IsForm e F) (_h_level : HasLevel F K)
      (_h_bound : ∀ g : G E s, ‖F g‖ ≤ c) (g : G E s), ‖F g‖ * V.height g ^ A ≤ c * R := by
  -- High in the cusp use rapid decay with `δ ^ n = κ / V.height g`; elsewhere the height is at most
  -- `κ`.
  cases isEmpty_or_nonempty n
  · -- If `n` is empty the lattice has no nonzero vector, so the height is `1`.
    exact ⟨1, by simp +contextual [height, firstMinimum, funext_iff]⟩
  let J : OpenSubgroup (Gf E n) := K ⊓ ⟨stdLevel E n, isOpen_stdLevel⟩
  have : IsLevel J.toSubgroup := ⟨inf_le_right, J.isOpen⟩
  obtain ⟨δ₀, hδ₀, h_decay⟩ := exists_norm_le_of_radicalCovered he (Fintype.card n * A)
  obtain ⟨κ, hκ, h_cusp⟩ := exists_cuspFrame_of_height (s := s) J
  refine ⟨(κ / (δ₀ ⊓ 1) ^ Fintype.card n) ^ A, fun {F c} hF h_level hc g ↦ ?_⟩
  obtain ⟨δ, hδ_pos, hδ, h_frame⟩ := h_cusp V g
  have hc₀ : 0 ≤ c := (norm_nonneg _).trans (hc 1)
  have h_bound : ‖F g‖ ≤ (δ / (δ₀ ⊓ 1)) ^ (Fintype.card n * A) * c := by
    rcases le_total δ 1 with hδ_le | hδ_ge
    · obtain ⟨cusp, h_cover⟩ := h_frame hδ_le
      have h_cusp_bound : ‖F g‖ ≤ (δ / δ₀) ^ (Fintype.card n * A) * c :=
        h_decay J V g δ cusp.isotropicCols hδ_pos.le cusp.ne_zero cusp.isotropic h_cover F c
          hF.continuous hc
          (hF.realConv_eq he.integrable) (fun k hk ↦ h_level k hk.1) fun ν _ ↦ hF.rat_mul _ ⟨ν, rfl⟩
      grw [h_cusp_bound, (inf_le_left : δ₀ ⊓ 1 ≤ δ₀)]
    · refine (hc g).trans (le_mul_of_one_le_left hc₀ (one_le_pow₀ ?_))
      exact (one_le_div (by positivity)).2 (inf_le_right.trans hδ_ge)
  calc ‖F g‖ * V.height g ^ A ≤ (δ / (δ₀ ⊓ 1)) ^ (Fintype.card n * A) * c * V.height g ^ A :=
        mul_le_mul_of_nonneg_right h_bound (pow_nonneg (V.height_pos g).le A)
    _ = c * ((δ ^ Fintype.card n * V.height g) / (δ₀ ⊓ 1) ^ Fintype.card n) ^ A := by ring
    _ = c * (κ / (δ₀ ⊓ 1) ^ Fintype.card n) ^ A := by rw [hδ]

/-- Let `V` be a hermitian space over the CM field `E`, and let `e` be a cusp kernel of order `B` on
`G_∞`. Such a kernel is a minimal idempotent `e` such that (a) `‖x‖^(B+1) e(x)` is integrable, (b)
`α ∗ e = e` for some continuous compactly supported `α`, and (c) `‖x‖^B e(x)` is bounded, where
`‖x‖ = ∏_w ‖x_w‖`. Then every form `F` of type `e` for `V` (a bounded automorphic function on `G`
fixed by right convolution with `e`) lies in `V.rapidFunctions`, i.e. decays rapidly: `|F|` times
any power of the height is bounded. -/
theorem IsForm.mem_rapidFunctions (he : IsCuspKernel B e) (hF : V.IsForm e F) :
    F ∈ V.rapidFunctions := by
  obtain ⟨K, h_level⟩ := hF.exists_level
  obtain ⟨c, hc⟩ := hF.bounded
  refine ⟨hF.toIsAutomorphic, fun A ↦ ?_⟩
  obtain ⟨R, h_decay⟩ := V.exists_norm_mul_height_pow_le he K A
  exact ⟨c * R, h_decay hF h_level hc⟩

/-- Let `e` be a cusp kernel of order `B` on the archimedean unitary group `G_∞`: a minimal
idempotent with ‖x‖^(B+1) e(x) integrable, ‖x‖^B e(x) bounded, and α ∗ e = e for some continuous
compactly supported α. Let `K` be an open subgroup of the finite adelic unitary group `G_f`. Then
the forms of type `e` for `V` (bounded automorphic functions fixed by right convolution with `e`)
that are right invariant under `K` make up a finite-dimensional complex vector space. -/
theorem finite_levelSpace (he : IsCuspKernel B e) (K : OpenSubgroup (Gf E n)) :
    Module.Finite ℂ (levelSpace (V.formRep e) K.toSubgroup) := by
  -- A form of level `K` exceeds half its bound only at height at most `2 * R`, so inside `Γ * C`
  -- with `C` compact (`mahler_criterion`). Cover `C` by neighbourhoods of finitely many
  -- points `a⁻¹`, `a ∈ t`, on which such a form is within half its bound of `F a⁻¹`. If it
  -- vanishes at all `a⁻¹`, every bound can be halved, so it is zero.
  obtain ⟨R, h_decay⟩ := V.exists_norm_mul_height_pow_le he K 1
  obtain ⟨C, C_compact, hC⟩ := V.mahler_criterion (2 * R)
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates C_compact
    ⟨1, mem_interior_iff_mem_nhds.2 (eventually_norm_realConv_sub_le K he.integrable one_half_pos)⟩
  have h_vanish {F : G E s → ℂ} (hF : V.IsForm e F) (h_level : HasLevel F K)
      (h_zero : ∀ a ∈ t, F a⁻¹ = 0) (g : G E s) : ‖F g‖ ≤ 0 := by
    obtain ⟨M₀, hM₀⟩ := hF.bounded
    refine le_of_halving hM₀ le_rfl (fun M hM_nonneg hM g ↦ .inl ?_) g
    by_contra! h_big
    -- From `M / 2 < ‖F g‖` and `‖F g‖ * V.height g ≤ M * R`.
    have h_height : V.height g ≤ 2 * R := by nlinarith [V.height_pos g, h_decay hF h_level hM g]
    obtain ⟨γ, hγ, hγg⟩ : ∃ γ ∈ V.Γ, γ * g ∈ C := hC g h_height
    obtain ⟨a, ha, h_near⟩ := mem_iUnion₂.1 (ht hγg)
    have h_close : ‖realConv e F (a⁻¹ * (a * (γ * g))) - realConv e F a⁻¹‖ ≤ 1 / 2 * ‖M‖ :=
      h_near M hF.isBoundedMeasurable h_level a⁻¹ fun x _ ↦ hM _
    rw [hF.realConv_eq he.integrable, inv_mul_cancel_left, hF.rat_mul γ hγ, h_zero a ha, sub_zero,
      Real.norm_of_nonneg hM_nonneg] at h_close
    linarith
  -- So evaluation at the points `a⁻¹`, `a ∈ t`, is an injective linear map into `t → ℂ`.
  let ev : levelSpace (V.formRep e) K.toSubgroup →ₗ[ℂ] t → ℂ :=
    .pi fun a : t ↦ .proj (a : G E s)⁻¹ ∘ₗ (Submodule.subtype _).domRestrict _
  refine .of_injective ev ((injective_iff_map_eq_zero ev).2 ?_)
  rintro ⟨⟨F, hF⟩, h_level⟩ h_ev
  obtain rfl : F = 0 := funext fun g ↦ norm_le_zero_iff.1
    (h_vanish hF (mem_levelSpace_formRep_iff.1 h_level) (fun a ha ↦ congrFun h_ev ⟨a, ha⟩) g)
  rfl

/-- Let `e` be a cusp kernel of order `B` on `G_∞`: a minimal idempotent with ‖x‖^(B+1) e(x)
integrable, ‖x‖^B e(x) bounded, and α ∗ e = e for some continuous compactly supported α. Let `F` be
automorphic for `V` (continuous, left `Γ`-invariant, right invariant under an open subgroup of
`G_f`), with `x ↦ e(x) F(g (x, 1))` integrable for every `g`. Then the convolution `realConv e F`,
`g ↦ ∫ e(x) F(g x) dx`, is a form of type `e`: automorphic, bounded, and fixed by right convolution
with `e`. -/
theorem isForm_realConv (he : IsCuspKernel B e) (hF : V.IsAutomorphic F)
    (h_int : ∀ g : GInf E s × Gf E n, Integrable fun x : GInf E s ↦ e x * F (g * (x, 1))) :
    V.IsForm e (realConv e F) := by
  -- Truncate `F` to the set where `‖F‖ ≤ t`. The averages of the truncations are forms of level `K`
  -- and tend pointwise to `realConv e F`. The forms of level `K` make up a finite-dimensional,
  -- hence closed, space `W` of functions, so `realConv e F` lies in it.
  obtain ⟨h_cont, h_rat, K, h_level⟩ := hF
  let trunc (t : ℝ) : G E s → ℂ := indicator {g : G E s | ‖F g‖ ≤ t} F
  let W : Submodule ℂ (G E s → ℂ) :=
    (Submodule.subtype _ ∘ₗ (levelSpace (V.formRep e) K).subtype).range
  have : Module.Finite ℂ (levelSpace (V.formRep e) K.toSubgroup) := V.finite_levelSpace he K
  have trunc_mem (t : ℝ) : realConv e (trunc t) ∈ W := by
    have h_bound (g : G E s) : ‖trunc t g‖ ≤ |t| := by grind [indicator, norm_zero]
    refine exists_form_eq_realConv K
      ⟨h_cont.stronglyMeasurable.indicator (h_cont.norm.measurable measurableSet_Iic), |t|, h_bound⟩
      (fun γ hγ g ↦ ?_) (fun k hk g ↦ ?_) he.toIsIdempotentKernel
    · simp only [trunc, indicator, mem_ofPred_eq, h_rat γ hγ g]
    · simp only [trunc, indicator, mem_ofPred_eq, h_level k hk g]
  have tendsto_avg :
      Filter.Tendsto (fun t : ℝ ↦ realConv e (trunc t)) .atTop (nhds (realConv e F)) := by
    refine tendsto_pi_nhds.2 fun g ↦ ?_
    -- The sets where `‖F (g * (x, 1))‖ ≤ t` exhaust the group, and the integrand is integrable.
    have h_cover : AECover volume .atTop fun t : ℝ ↦ {x : GInf E s | ‖F (g * (x, 1))‖ ≤ t} :=
      ⟨.of_forall fun x ↦ Filter.eventually_ge_atTop _, by measurability⟩
    refine (h_cover.integral_tendsto_of_countably_generated (h_int g)).congr fun t ↦ ?_
    simp [trunc, realConv, indicator, ← integral_indicator (h_cover.measurableSet t)]
  obtain ⟨⟨⟨Φ, hΦ_form⟩, hΦ_level⟩, rfl : Φ = realConv e F⟩ : realConv e F ∈ W :=
    W.closed_of_finiteDimensional.mem_of_tendsto tendsto_avg (.of_forall trunc_mem)
  exact hΦ_form

end New.Space

end FiniteDimension

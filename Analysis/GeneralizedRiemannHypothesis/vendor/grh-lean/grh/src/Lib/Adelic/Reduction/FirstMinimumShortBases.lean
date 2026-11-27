import Lib.Adelic.Unitary.RationalPoints
import Lib.General.NumberTheory.SUnitsAndClassNumber

/-!
# Transference, first minima and short bases of lattices of hermitian spaces

Minkowski's bound and weak transference in a Euclidean space `E` of dimension `m` give short vectors
and a covering radius for a subgroup `Λ` whose dual has no nonzero vectors shorter than `ρ > 0`. For
a hermitian space `V` with a point, the lattice of `V` defines a first minimum, cut off at `1`, and
a height on the adelic unitary group, against which growth and decay are measured.

## Main definitions and results

* `New.weak_transference`: if `m ≥ 1`, `Λ` has a nonzero vector shorter than `2 m / ρ`.
* `New.weak_transference_covering_radius`: every vector is within `m ^ 2 / ρ` of `Λ`.
* `New.Space.archCoords`, `New.Space.firstMinimum`, `New.Space.height`: the archimedean coordinates
  of a rational vector, the first minimum of the lattice cut off at `1`, and the inverse of the
  first minimum of the moved space `V.move g`, the height at `g`.
* `New.Space.IsModerate`, `New.Space.IsRapid`: moderate growth and rapid decay against the height.
* `New.Space.form_eq_zero_of_norm_mul_lt_one`, `New.Space.firstMinimum_move_eq_one`,
  `New.Space.firstMinimum_pos`: lattice vectors whose lengths have product below `1` are orthogonal;
  the minimum is `1` in a definite space, and positive in any space as the lattice is discrete. The
  comparison of heights on `Γ g Ξ` for compact `Ξ` is `New.Space.exists_height_le_mul` in
  `Lib.Adelic.AutomorphicForms.Basic`.
* `New.Space.exists_short_basis`: the lattice contains a basis of vectors of length at most a
  constant over the first minimum.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over a CM field E (class
  `CMType E`) and x in GL_n(𝔸) with xᴴJx equal to diag(s) at the infinite places and 1 at the finite
  places; `V.move g` is (J, xg).
* `New.G`: the adelic unitary group G = G_∞ × G_f for signs s at the infinite places and the
  identity matrix at the finite places.
* `New.Space.vecAtPoint`: for a space (J, x), the adelic coordinates x⁻¹y of a vector y in E^n.
* `New.Space.baseLattice`: for a space (J, x), the lattice E^n ∩ x_f Ô^n, as an additive subgroup of
  E^n.
* `New.Space.sum`: for spaces V, W with signs s, t, the space with concatenated signs whose matrix
  and point are the block diagonal sums of those of V and W.

## Relation to the literature

Known result: Transference theorem for the covering radius of a lattice against its dual's first
minimum. The constant here is m squared in dimension m, where the sharp forms have a constant linear
in m. The result holds for any subgroup of a Euclidean space whose dual has no short nonzero vector,
and is proved by projecting along a short vector. Source: Lagarias-Lenstra-Schnorr, Korkin-Zolotarev
bases and successive minima of a lattice and its reciprocal lattice, Combinatorica 10 (1990); sharp
forms in Banaszczyk, Math. Ann. 296 (1993), and Miller-Stephens-Davidowitz, Kissing numbers and
transference theorems from generalized tail bounds, SIAM J. Discrete Math. 33 (2019).

See also `Lib.Adelic.AutomorphicForms.Cuspidality` and `Lib.Adelic.Reduction.FiniteVolume`.
-/

noncomputable section

/-!
## Weak transference: Minkowski's bound and the covering radius

Geometry of numbers in a Euclidean space `E` of dimension `m`, for a subgroup `Λ` whose dual has no
nonzero vectors shorter than `ρ > 0`. This hypothesis forces `Λ` to span `E`, but `Λ` need not be
discrete.
-/

section Transference

open Module Submodule MeasureTheory LinearMap.BilinForm Matrix

namespace New

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Minkowski's bound. If the nonzero vectors of the lattice spanned by a basis `b` of a Euclidean
space of dimension `m ≥ 1` have length at least `ρ > 0`, then its covolume `|det b|`, in the
coordinates of an orthonormal basis `o`, is at least `(ρ / √m) ^ m`. -/
lemma minkowski_pow_le_abs_det [Module.Finite ℝ E] {ρ : ℝ} (hρ : 0 < ρ) {m : ℕ} (hm : 0 < m)
    {o : OrthonormalBasis (Fin m) ℝ E} {b : Basis (Fin m) ℝ E}
    (h_long : ∀ y ∈ span ℤ (Set.range b), y ≠ 0 → ρ ≤ ‖y‖) :
    (ρ / √m) ^ m ≤ |det (of fun i : Fin m ↦ o.repr (b i))| := by
  -- In the coordinates of `o`, the open cube of half-side `ρ / √m` (a ball for the sup norm) has no
  -- nonzero lattice point.
  let c : Basis (Fin m) ℝ (Fin m → ℝ) := b.map o.toBasis.equivFun
  have sup_norm_ge (x : E) (hx : x ∈ span ℤ (Set.range b)) (hx_ne : x ≠ 0) :
      ρ / √m ≤ ‖(o.repr x).ofLp‖ := by
    grw [h_long x hx hx_ne, ← o.repr.norm_map, PiLp.norm_eq_of_L2, norm_le_pi_norm]
    simp [field]
  have no_point : ¬∃ x : (span ℤ (Set.range c)).toAddSubgroup,
      x ≠ 0 ∧ (x : Fin m → ℝ) ∈ Metric.ball 0 (ρ / √m) := by
    simpa [c, ← ZSpan.map] using fun x hx_ne hx ↦ sup_norm_ge x hx hx_ne
  -- So by Minkowski's theorem its volume `(2 * ρ / √m) ^ m` is at most `2 ^ m` times the covolume.
  have : Countable (span ℤ (Set.range c)).toAddSubgroup := countable_of_Lindelof_of_discrete
  have vol_le : volume (Metric.ball (0 : Fin m → ℝ) (ρ / √m)) ≤
      volume (ZSpan.fundamentalDomain c) * 2 ^ finrank ℝ (Fin m → ℝ) :=
    not_lt.1 fun h_lt ↦ no_point <| exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (ZSpan.isAddFundamentalDomain' c volume) (by simp) (convex_ball 0 _) h_lt
  have vol_cube : volume (Metric.ball (0 : Fin m → ℝ) (ρ / √m)) =
      ENNReal.ofReal ((ρ / √m) ^ m) * 2 ^ m := by
    simp [Real.volume_pi_ball, hρ, hm, mul_pow, mul_comm]
  have covolume : volume (ZSpan.fundamentalDomain c) =
      ENNReal.ofReal |det (of fun i : Fin m ↦ o.repr (b i))| :=
    ZSpan.volume_fundamentalDomain c
  simpa [vol_cube, covolume, ENNReal.mul_le_mul_iff_left] using vol_le

/-- A subgroup `Λ` of a Euclidean space spans the space if the nonzero vectors of its dual (the `y`
with `⟪y, x⟫ ∈ ℤ` for all `x ∈ Λ`) have length at least `ρ > 0`. -/
lemma span_eq_top_of_le_norm_dual (Λ : Submodule ℤ E) [Module.Finite ℝ E] {ρ : ℝ} (hρ : 0 < ρ)
    (h_dual : ∀ y ∈ dualSubmodule (innerₗ E) Λ, y ≠ 0 → ρ ≤ ‖y‖) :
    span ℝ (Λ : Set E) = ⊤ := by
  -- The orthogonal complement lies in the dual, so it is discrete; being connected, it is zero.
  have h_mem (u : (span ℝ (Λ : Set E))ᗮ) : (u : E) ∈ dualSubmodule (innerₗ E) Λ :=
    fun y hy ↦ by simp [real_inner_comm, u.2 y (subset_span hy)]
  have : DiscreteTopology (span ℝ (Λ : Set E))ᗮ :=
    .of_forall_le_norm hρ fun u hu ↦ h_dual u (h_mem u) (by simpa using hu)
  exact orthogonal_eq_bot_iff.1 (subsingleton_iff_eq_bot.1 PreconnectedSpace.trivial_of_discrete)

/-- Weak transference. Let `Λ` be a subgroup of a Euclidean space of dimension `m ≥ 1`. If the
nonzero vectors of its dual (the `y` with `⟪y, x⟫ ∈ ℤ` for all `x ∈ Λ`) have length at least
`ρ > 0`, then `Λ` has a nonzero vector of length less than `2 m / ρ`.

A consequence of Minkowski's convex body theorem. -/
lemma weak_transference (Λ : Submodule ℤ E) [Module.Finite ℝ E] {ρ : ℝ} (hρ : 0 < ρ)
    (h_dual : ∀ y ∈ dualSubmodule (innerₗ E) Λ, y ≠ 0 → ρ ≤ ‖y‖) (hm : 0 < finrank ℝ E) :
    ∃ b ∈ Λ, b ≠ 0 ∧ ‖b‖ < 2 * finrank ℝ E / ρ := by
  -- Otherwise `Λ` is a lattice, and Minkowski's bounds for `Λ` and its dual contradict each other.
  by_contra! h_long
  have h_pos : 0 < 2 * finrank ℝ E / ρ := by positivity
  have : DiscreteTopology Λ := .of_forall_le_norm h_pos fun u hu ↦ h_long u u.2 (by simpa using hu)
  have : IsZLattice ℝ Λ := ⟨span_eq_top_of_le_norm_dual Λ hρ h_dual⟩
  obtain ⟨b, rfl⟩ : ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, span ℤ (Set.range b) = Λ :=
    ⟨_, (finBasisOfFinrankEq ℤ Λ (ZLattice.rank ℝ Λ)).ofZLatticeBasis_span ℝ⟩
  have h_nondeg : LinearMap.BilinForm.Nondegenerate (innerₗ E) := by
    simp +contextual [nondegenerate_iff', isSymm_inner]
  -- The dual basis `b'` spans the dual lattice.
  let b' : Basis (Fin (finrank ℝ E)) ℝ E := dualBasis (innerₗ E) h_nondeg b
  rw [dualSubmodule_span_of_basis _ h_nondeg] at h_dual
  -- The covolumes of the lattice and of its dual have product 1, while the product of the two
  -- lower bounds `minkowski_pow_le_abs_det` is `2 ^ m`, `m` the dimension.
  let o : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  let A : Matrix _ _ ℝ := of fun i j ↦ o.repr (b i) j
  let A' : Matrix _ _ ℝ := of fun i j ↦ o.repr (b' i) j
  have h_inverse : A * A'ᵀ = 1 := by
    ext i j
    calc (A * A'ᵀ) i j = innerₗ E (b' j) (b i) := by
          simp [A, A', mul_apply, ← o.repr.inner_map_map (b' j), PiLp.inner_apply,
            -LinearIsometryEquiv.inner_map_map]
      _ = (1 : Matrix _ _ ℝ) i j := by rw [apply_dualBasis_left h_nondeg b j i, one_apply]
  have det_mul_det : |det A'| * |det A| = 1 := by
    rw [← det_transpose, ← abs_mul, mul_comm, ← det_mul, h_inverse, det_one, abs_one]
  have two_pow_le : (ρ / √(finrank ℝ E) * (2 * finrank ℝ E / ρ / √(finrank ℝ E))) ^ finrank ℝ E
      ≤ 1 := by
    grw [mul_pow, minkowski_pow_le_abs_det hρ hm (o := o) (b := b') h_dual,
      minkowski_pow_le_abs_det h_pos hm (o := o) h_long, det_mul_det]
  have h_two : ρ / √(finrank ℝ E) * (2 * finrank ℝ E / ρ / √(finrank ℝ E)) = 2 := by simp [field]
  rw [h_two] at two_pow_le
  exact two_pow_le.not_gt (one_lt_pow₀ one_lt_two hm.ne')

/-- Covering radius. Let `Λ` be a subgroup of a Euclidean space of dimension `m`. If the nonzero
vectors of its dual (the `y` with `⟪y, x⟫ ∈ ℤ` for all `x ∈ Λ`) have length at least `ρ > 0`, then
every vector `u` lies within distance `m ^ 2 / ρ` of some vector of `Λ`.

Known result: the Lagarias–Lenstra–Schnorr transference theorem for the covering radius of a
lattice against its dual's first minimum, here with a weaker constant. -/
lemma weak_transference_covering_radius (Λ : Submodule ℤ E) [Module.Finite ℝ E] {ρ : ℝ}
    (hρ : 0 < ρ) (h_dual : ∀ y ∈ dualSubmodule (innerₗ E) Λ, y ≠ 0 → ρ ≤ ‖y‖) (u : E) :
    ∃ x ∈ Λ, ‖u - x‖ ≤ finrank ℝ E ^ 2 / ρ := by
  -- Induction on the dimension: each step along a short vector `b ∈ Λ` costs at most `‖b‖ / 2`.
  induction hn : finrank ℝ E generalizing E with
  | zero => exact ⟨0, zero_mem Λ, by simp [finrank_zero_iff_forall_zero.1 hn u]⟩
  | succ n ih =>
    obtain ⟨b, hb, hb_ne, norm_b⟩ := weak_transference Λ hρ h_dual (by lia)
    -- Project `Λ` and `u` to the hyperplane orthogonal to `b`. The dual of the image `Λ'` lies in
    -- the dual of `Λ`, so the induction hypothesis applies to it.
    let Λ' : Submodule ℤ (ℝ ∙ b)ᗮ :=
      Λ.map ((ℝ ∙ b)ᗮ.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ)
    have h_dual' (y : (ℝ ∙ b)ᗮ) (hy : y ∈ dualSubmodule (innerₗ _) Λ') (hy_ne : y ≠ 0) : ρ ≤ ‖y‖ :=
      h_dual y (fun z hz ↦ by simpa using hy _ ⟨z, hz, rfl⟩) (by simpa using hy_ne)
    have : Fact (finrank ℝ E = n + 1) := ⟨hn⟩
    obtain ⟨_, ⟨x, hx, rfl⟩, norm_x⟩ :=
      ih Λ' h_dual' ((ℝ ∙ b)ᗮ.orthogonalProjectionOnto u) (finrank_orthogonal_span_singleton hb_ne)
    -- The projection of `u - x` is `u - x - t • b` for a real `t`; round `t` to an integer.
    obtain ⟨t, ht⟩ : ∃ t : ℝ, ‖u - x - t • b‖ ≤ n ^ 2 / ρ :=
      ⟨inner ℝ b u / ‖b‖ ^ 2 - inner ℝ b x / ‖b‖ ^ 2, by
        simpa [starProjection_singleton, sub_sub_sub_comm u, ← sub_smul] using norm_x⟩
    refine ⟨x + round t • b, add_mem hx (smul_mem _ _ hb), ?_⟩
    calc ‖u - (x + round t • b)‖
      _ ≤ ‖u - x - t • b‖ + |t - round t| * ‖b‖ := by
        grw [← sub_sub, norm_sub_le_norm_sub_add_norm_sub _ (t • b), ← Int.cast_smul_eq_zsmul ℝ,
          ← sub_smul, norm_smul, Real.norm_eq_abs]
      _ ≤ n ^ 2 / ρ + 1 / 2 * (2 * (n + 1 : ℕ) / ρ) := by grw [ht, abs_sub_round, norm_b, hn]
      _ ≤ (n + 1 : ℕ) ^ 2 / ρ := by
        field_simp
        push_cast
        linarith [n.cast_nonneg (α := ℝ)]

/-- Short vectors span. If every vector of a finite-dimensional Euclidean space lies within distance
`r > 0` of a set `S`, then the vectors of `S` of length at most `3 r` span the space. -/
lemma span_norm_le_eq_top_of_covering [Module.Finite ℝ E] {S : Set E} {r : ℝ} (hr : 0 < r)
    (h_cover : ∀ u : E, ∃ x ∈ S, ‖u - x‖ ≤ r) :
    span ℝ {x ∈ S | ‖x‖ ≤ 3 * r} = ⊤ := by
  -- A vector `x` of `S` within `r` of a vector `u` of length `2 r` has length at most `3 r` and is
  -- not orthogonal to `u`. So no nonzero vector is orthogonal to all short vectors.
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro y hy
  by_contra hy_ne
  let u : E := (2 * r / ‖y‖) • y
  have hu_norm : ‖u‖ = 2 * r := by simp [u, norm_smul, abs_of_pos hr, hy_ne]
  obtain ⟨x, hx_mem, hx_near⟩ := h_cover u
  have hx_norm : ‖x‖ ≤ 3 * r := by linarith [norm_sub_norm_le x u, norm_sub_rev x u]
  have hx_span : x ∈ span ℝ {x ∈ S | ‖x‖ ≤ 3 * r} := subset_span ⟨hx_mem, hx_norm⟩
  have h_orth : inner ℝ u x = 0 := inner_left_of_mem_orthogonal hx_span (smul_mem _ _ hy)
  have h_sq : ‖u - x‖ ^ 2 ≤ r ^ 2 := by gcongr
  rw [norm_sub_sq_real, h_orth, hu_norm] at h_sq
  nlinarith [sq_nonneg ‖x‖]

end New

end Transference

/-!
## Dilations, first minimum, height, moderate and rapid functions

* `New.dilationGroup`: pairs `(g, c)` of a unitary matrix `g` and a unit `c` such that `g` scales
  the columns of a matrix `A` by `c` and satisfies `wᴴ J (g v) = wᴴ J v` for `v`, `w` orthogonal to
  `A`, that is, acts trivially on the orthogonal complement modulo its radical.
-/

section Height

open NumberField Matrix

namespace New

variable {n : Type _} [Fintype n] [DecidableEq n]
  {R : Type _} [CommRing R] [StarRing R] {m : Type _} (A : Matrix n m R)
  {E : Type*} [Field E] [CMType E]

/-- The dilations along the columns of `A` for the form `J` (implicit, read from the type of the
unitary group `U J`): the pairs `(g, c)` in `U J × Rˣ` such that `g` is the scalar `c` on the
columns of `A` and `wᴴ J g v = wᴴ J v` whenever `Aᴴ J v = 0` and `Aᴴ J w = 0`. The test objects `v`,
`w` are square matrices, standing for families of vectors orthogonal to the columns of `A`. -/
def dilationGroup {J : Matrix n n R} : Subgroup (U J × Rˣ) :=
  Subgroup.ofDiv
    {g : U J × Rˣ |
      ((g.1 : GL n R) : Matrix n n R) * A = g.2 • A ∧
      ∀ v w : Matrix n n R, Aᴴ * (J * v) = 0 → Aᴴ * (J * w) = 0 →
        wᴴ * (J * (((g.1 : GL n R) : Matrix n n R) * v)) = wᴴ * (J * v)}
    ⟨1, by simp⟩ <| by
      rintro ⟨g, c⟩ ⟨hg_scale, hg_form⟩ ⟨k, d⟩ ⟨hk_scale, hk_form⟩
      let M (u : U J) : Matrix n n R := (u : GL n R)
      have M_mul (u u' : U J) : M (u * u') = M u * M u' := rfl
      change M g * A = c • A at hg_scale
      change M k * A = d • A at hk_scale
      refine ⟨?_, fun v w hv hw ↦ ?_⟩
      · -- Multiply by the scalar `d` and use `k * A = d • A`.
        change M (g * k⁻¹) * A = (c * d⁻¹) • A
        rw [← smul_left_cancel_iff d, ← Matrix.mul_smul, ← hk_scale, ← Matrix.mul_assoc, ← M_mul,
          inv_mul_cancel_right, hg_scale, smul_smul, mul_comm c, mul_inv_cancel_left]
      · -- `k⁻¹ * v` is again orthogonal to `A`, because `k` preserves `J` and scales `A`.
        have h_cancel : M k * (M k⁻¹ * v) = v := by simp [M, ← mul_assoc]
        have h_orth : Aᴴ * (J * (M k⁻¹ * v)) = 0 := by
          -- Replace `Aᴴ * J` by `(k * A)ᴴ * J * k` and cancel.
          rw [← Matrix.mul_assoc, ← U.gram_invariant k A]
          simp [M, hk_scale, Matrix.mul_assoc, Units.smul_def, hv]
        -- So neither `k⁻¹` nor `g` changes the pairing with `w`.
        change wᴴ * (J * (M (g * k⁻¹) * v)) = wᴴ * (J * v)
        rw [M_mul, mul_assoc, hg_form _ w h_orth hw, ← hk_form _ w h_orth hw, h_cancel]

namespace Space

variable {s : n → ℤˣ} (V : Space E n s)

/-- The additive map sending y ∈ E^n to the archimedean components of x⁻¹y (`V.vecAtPoint y`), with
x the point of V, as a vector in a Euclidean space indexed by the infinite places and `n`. Its norm
is the length of y. -/
def archCoords : (n → E) →+ EuclideanSpace ℂ (InfinitePlace E × n) :=
  AddMonoidHom.mk'
    (fun y : n → E ↦ WithLp.toLp 2 fun p : InfinitePlace E × n ↦ (V.vecAtPoint y p.2).1 p.1)
    (by aesop)

/-- The set of vectors `y` of the lattice `V.baseLattice` whose length `‖V.archCoords y‖` is at most
`r`. -/
abbrev latticeBall (r : ℝ) : Set (n → E) := {y ∈ V.baseLattice | ‖V.archCoords y‖ ≤ r}

/-- The first minimum cut off at 1: `λ = min(1, inf ‖y‖)`, where `y` runs over the nonzero vectors
of the lattice `V.baseLattice` and `‖y‖` is the norm of `V.archCoords y`. -/
def firstMinimum : ℝ :=
  sInf (insert 1 ((fun y : n → E ↦ ‖V.archCoords y‖) '' {y ∈ V.baseLattice | y ≠ 0}))

/-- The height `ht(g) = 1 / λ`, with `λ` the first minimum cut off at 1 (`New.Space.firstMinimum`)
of the moved space `V.move g`. -/
def height (g : G E s) : ℝ := (V.move g).firstMinimum⁻¹

/-- A function `F` on the adelic unitary group has moderate growth: `|F g| ≤ C * ht(g) ^ B` for all
`g`, for some real `C` and natural number `B`, where `ht` is the height `V.height`. -/
def IsModerate (F : G E s → ℂ) : Prop :=
  ∃ (C : ℝ) (B : ℕ), ∀ g : G E s, ‖F g‖ ≤ C * V.height g ^ B

/-- A function `F` on the adelic unitary group has rapid decay: `|F g| * ht(g) ^ B` is bounded for
every natural number `B`, where `ht` is the height `V.height`. -/
def IsRapid (F : G E s → ℂ) : Prop := ∀ B : ℕ, ∃ C : ℝ, ∀ g : G E s, ‖F g‖ * V.height g ^ B ≤ C

end Space

end New

end Height

/-!
## The first minimum: bounds, positivity, orthogonality of short vectors

A space `V` (`New.Space`) with point `x` gives a lattice `New.Space.baseLattice` in `E ^ n` and a
length `‖V.archCoords y‖` (`New.Space.archCoords`), from the finite and the infinite part of the
coordinates `x⁻¹ y` (`New.Space.vecAtPoint`) respectively.

* `New.Space.form_eq_zero_of_norm_mul_lt_one`: lattice vectors with product of lengths below `1` are
  orthogonal, as the value of the form is an algebraic integer (`New.Space.isIntegral_form`) that
  is small at every infinite place (`New.Space.norm_form_le_norm_archCoords_mul`).
-/

section FirstMinimum

open EuclideanSpace Matrix Finset ComplexOrder Norms.L2Operator Prod

namespace New.Space

variable {E : Type*} [Field E] [CMType E] {n : Type _} [Fintype n] [DecidableEq n]
variable {s : n → ℤˣ} {V : Space E n s}
variable {m : Type*} [Fintype m]

/-- At an infinite place `w`, the standard adelic form `stdForm E s` is the complex hermitian form
with the diagonal matrix `signMatrix s` of the signs `s`. Here `z.1 w` is the complex component at
`w` of an adele `z : 𝔸 E`. -/
lemma stdForm_dotProduct_fst (a b : n → 𝔸 E) (w : NumberField.InfinitePlace E) :
    (star a ⬝ᵥ stdForm E s *ᵥ b).1 w =
      star (fun i : n ↦ (a i).1 w) ⬝ᵥ signMatrix s *ᵥ fun i : n ↦ (b i).1 w := by
  simp [dotProduct, stdForm, mulVec_diagonal, fst_sum, signMatrix]

/-- A rational vector `a` is zero if its adelic coordinates `V.vecAtPoint a = x⁻¹ a` (`x` the point
of `V`) vanish at one infinite place `w`; `z.1 w` is the component at `w` of an adele `z`. -/
lemma eq_zero_of_vecAtPoint_fst_eq_zero {a : n → E} {w : NumberField.InfinitePlace E}
    (h : (fun i : n ↦ (V.vecAtPoint a i).1 w) = 0) :
    a = 0 := by
  -- Multiply by the point `V.x`, which takes `V.vecAtPoint a` back to the rational vector `a`.
  have h_vec : V.x.val *ᵥ V.vecAtPoint a = toAdele ∘ a := by simp [vecAtPoint]
  ext i
  have h_place := congrArg (fun v : n → 𝔸 E ↦ (v i).1 w) h_vec
  simpa [mulVec, dotProduct, fst_sum, fun j ↦ congrFun h j] using h_place.symm

/-- Moving the point `x` of `V` to `x g`, for `g` in the adelic unitary group, multiplies the adelic
coordinates `x⁻¹ ξ` of a rational vector `ξ` by the matrix of `g⁻¹`. -/
lemma vecAtPoint_move (g : G E s) (ξ : n → E) :
    (V.move g).vecAtPoint ξ = g⁻¹.adeleMatrix *ᵥ V.vecAtPoint ξ := by
  change (g⁻¹.adeleMatrix * V.x⁻¹.val) *ᵥ (toAdele ∘ ξ) = g⁻¹.adeleMatrix *ᵥ V.x⁻¹.val *ᵥ
    (toAdele ∘ ξ)
  rw [mulVec_mulVec]

/-- For a rational isometry `γ` of `V` and `g` in `G`, the coordinates of `γ y` at `γ g` are the
coordinates of `y` at `g`. Here `γ` enters `G` as x⁻¹γx, with x the point of `V`
(`New.Space.ratEmbed`), and the coordinates at `g` are those in the moved space `V.move g`. -/
lemma move_ratEmbed_mul_vecAtPoint_mulVec (γ : U V.J) (g : G E s) (y : n → E) :
    (V.move (V.ratEmbed γ * g)).vecAtPoint ((γ : Matrix n n E) *ᵥ y) =
      (V.move g).vecAtPoint y :=
  calc (V.move (V.ratEmbed γ * g)).vecAtPoint ((γ : Matrix n n E) *ᵥ y)
    _ = (V.ratEmbed γ * g)⁻¹.adeleMatrix *ᵥ (V.ratEmbed γ).adeleMatrix *ᵥ V.vecAtPoint y := by
      rw [vecAtPoint_move, ratEmbed_mulVec_vecAtPoint]
    _ = g⁻¹.adeleMatrix *ᵥ V.vecAtPoint y := by
      rw [mulVec_mulVec, ← G.adeleMatrix_mul, _root_.mul_inv_rev, inv_mul_cancel_right]
    _ = (V.move g).vecAtPoint y := (vecAtPoint_move g y).symm

/-- For a space `V` = (J, x), a rational isometry `γ` of J (an element of `U V.J`), and `g` in the
adelic unitary group `G E s` of the standard form (diag(s) at the infinite places, 1 at the finite
places), we have L_{γg} = γ L_g. Here L_g = E^n ∩ x_f g_f Ô^n is the base lattice of the moved space
`V.move g`, and `γ` enters `G E s` as x⁻¹γx (`New.Space.ratEmbed`). -/
lemma baseLattice_move_ratEmbed_mul (γ : U V.J) (g : G E s) :
    ((V.move (V.ratEmbed γ * g)).baseLattice : Set (n → E)) =
      (fun y : n → E ↦ (γ : Matrix n n E) *ᵥ y) '' (V.move g).baseLattice := by
  -- Membership of `γ y` on the left and of `y` on the right read the same coordinates.
  have h_mem_iff (y : n → E) :
      (γ : Matrix n n E) *ᵥ y ∈ (V.move (V.ratEmbed γ * g)).baseLattice ↔
        y ∈ (V.move g).baseLattice := by
    simp [baseLattice, move_ratEmbed_mul_vecAtPoint_mulVec]
  ext z
  refine ⟨fun hz ↦ ⟨((γ⁻¹ : U V.J) : Matrix n n E) *ᵥ z, ?_, by simp [mulVec_mulVec]⟩, ?_⟩
  · exact (h_mem_iff _).1 (by simpa [mulVec_mulVec] using hz)
  · rintro ⟨y, hy, rfl⟩
    exact (h_mem_iff y).2 hy

/-- For a space `V` = (J, x), a rational isometry `γ` of J (an element of `U V.J`), `g` in the
adelic unitary group `G E s` of the standard form (diag(s) at the infinite places, 1 at the finite
places), and `y` in E^n, we have ‖γy‖_{γg} = ‖y‖_g. Here ‖y‖_g is the norm of the archimedean
coordinates of `y` in the moved space `V.move g`, and `γ` enters `G E s` as x⁻¹γx
(`New.Space.ratEmbed`), since x carries the form J to the standard one. -/
lemma norm_archCoords_move_ratEmbed_mul_mulVec (γ : U V.J) (g : G E s) (y : n → E) :
    ‖(V.move (V.ratEmbed γ * g)).archCoords ((γ : Matrix n n E) *ᵥ y)‖ =
      ‖(V.move g).archCoords y‖ := by
  simp [archCoords, move_ratEmbed_mul_vecAtPoint_mulVec]

/-- Every rational vector has a nonzero integer multiple in the lattice `V.baseLattice` of the
vectors whose adelic coordinates are integral at the finite places. -/
lemma exists_smul_mem_baseLattice (ξ : n → E) : ∃ N : ℕ, N ≠ 0 ∧ N • ξ ∈ V.baseLattice := by
  simpa [← nsmul_eq_mul, baseLattice] using
    exists_forall_mul_mem_Ô fun i : n ↦ (V.vecAtPoint ξ i).2

/-! ### The first minimum and comparison of lengths -/

/-- A number `l` is at most the first minimum of `V`, cut off at `1`, iff it is at most `1` and at
most the length `‖V.archCoords y‖` of every nonzero vector `y` of the lattice `V.baseLattice`. -/
lemma le_firstMinimum_iff {l : ℝ} :
    l ≤ V.firstMinimum ↔
      l ≤ 1 ∧ ∀ y : n → E, y ∈ V.baseLattice → y ≠ 0 → l ≤ ‖V.archCoords y‖ := by
  have h_bdd : BddBelow
      (insert 1 ((fun y : n → E ↦ ‖V.archCoords y‖) '' {y | y ∈ V.baseLattice ∧ y ≠ 0})) :=
    BddBelow.insert 1 ⟨0, Set.forall_mem_image.2 fun _ _ ↦ norm_nonneg _⟩
  rw [firstMinimum, le_csInf_iff h_bdd (Set.insert_nonempty _ _)]
  simp only [Set.forall_mem_insert, Set.forall_mem_image, Set.mem_ofPred_eq, and_imp]

lemma firstMinimum_le {y : n → E} (hy : y ∈ V.baseLattice) (hy_ne : y ≠ 0) :
    V.firstMinimum ≤ ‖V.archCoords y‖ :=
  (le_firstMinimum_iff.mp le_rfl).2 y hy hy_ne

@[simp]
lemma firstMinimum_le_one : V.firstMinimum ≤ 1 := (le_firstMinimum_iff.mp le_rfl).1

/-- Let the adelic coordinates `V.vecAtPoint ξ` of `ξ` be `N • k` times those of `η` in a second
space `W`. If `N * k` is integral at the finite places (`z.2` is the finite part of an adele `z`,
`Ô E` the ring of integral finite adeles) and `η` lies in the lattice of `W`, then `ξ` lies in the
lattice of `V`. -/
lemma mem_baseLattice_of_vecAtPoint_eq [DecidableEq m] {ξ : n → E}
    {t : m → ℤˣ} {W : Space E m t} {η : m → E} {k : Matrix n m (𝔸 E)} {N : ℕ}
    (h_crd : V.vecAtPoint ξ = N • k *ᵥ W.vecAtPoint η)
    (hk_int : ∀ (i : n) (j : m), N * (k i j).2 ∈ Ô E) (hη : η ∈ W.baseLattice) :
    ξ ∈ V.baseLattice := by
  -- A finite coordinate of `ξ` is a sum of products `(N * k i j) * (coordinate of η)` in `Ô E`.
  intro i
  have h_coord : (V.vecAtPoint ξ i).2 = ∑ j : m, N * (k i j).2 * (W.vecAtPoint η j).2 := by
    simp [h_crd, mulVec, dotProduct, mul_sum, mul_assoc, snd_sum]
  rw [h_coord]
  exact sum_mem fun j _ ↦ mul_mem (hk_int i j) (hη j)

/-- Let the adelic coordinates `V.vecAtPoint ξ` of `ξ` be `N • k` times those of `η` in a second
space `W`, with `k` of operator norm at most `c` at each infinite place `w` (`z.1 w` is the
component at `w` of an adele `z`). Then the length `‖V.archCoords ξ‖` is at most `N * c` times the
length of `η` in `W`. -/
lemma norm_archCoords_le_of_vecAtPoint_eq [DecidableEq m] {ξ : n → E}
    {t : m → ℤˣ} {W : Space E m t} {η : m → E} {k : Matrix n m (𝔸 E)} {N : ℕ} {c : ℝ}
    (hk_norm : ∀ w : NumberField.InfinitePlace E, ‖k.map fun a : 𝔸 E ↦ a.1 w‖ ≤ c)
    (h_crd : V.vecAtPoint ξ = N • k *ᵥ W.vecAtPoint η) :
    ‖V.archCoords ξ‖ ≤ N * c * ‖W.archCoords η‖ := by
  have hc : 0 ≤ c := (norm_nonneg _).trans (hk_norm Classical.ofNonempty)
  -- At each infinite place, `‖k v‖ ≤ ‖k‖ * ‖v‖` for the operator norm.
  have h_place (w : NumberField.InfinitePlace E) :
      ∑ i, ‖(V.vecAtPoint ξ i).1 w‖ ^ 2 ≤ N ^ 2 * c ^ 2 * ∑ j, ‖(W.vecAtPoint η j).1 w‖ ^ 2 := by
    let A : Matrix n m ℂ := k.map fun a : 𝔸 E ↦ a.1 w
    let v : EuclideanSpace ℂ m := .toLp 2 fun j ↦ (W.vecAtPoint η j).1 w
    calc ∑ i, ‖(V.vecAtPoint ξ i).1 w‖ ^ 2
      _ = N ^ 2 * ‖(WithLp.toLp 2 (A *ᵥ v.ofLp) : EuclideanSpace ℂ n)‖ ^ 2 := by
        simp [A, v, h_crd, mulVec, norm_sq_eq, ← mul_sum, mul_pow, dotProduct, fst_sum]
      _ ≤ N ^ 2 * (c * ‖v‖) ^ 2 := by
        grw [← hk_norm w]
        gcongr
        exact l2_opNorm_mulVec A v
      _ = N ^ 2 * c ^ 2 * ∑ j, ‖(W.vecAtPoint η j).1 w‖ ^ 2 := by
        rw [mul_pow, norm_sq_eq, mul_assoc]
  -- Square both sides and sum over the places.
  refine le_of_sq_le_sq ?_ (by positivity)
  simpa [mul_pow, norm_sq_eq, Fintype.sum_prod_type, ← mul_sum, archCoords] using
    sum_le_sum fun w (_ : w ∈ univ) ↦ h_place w

/-- If the coordinates of `ξ` in `V` are `N • k` times those of `η` in `W`, with `k` of operator
norm at most `c` at each infinite place, then `ξ` is a lattice vector if `η` is one and `N * k` is
integral at the finite places, and the length of `ξ` is at most `N * c` times that of `η`. -/
lemma mem_and_norm_le_of_vecAtPoint [DecidableEq m] (ξ : n → E)
    {t : m → ℤˣ} (W : Space E m t) (η : m → E) (k : Matrix n m (𝔸 E)) (N : ℕ) {c : ℝ}
    (hk_norm : ∀ w : NumberField.InfinitePlace E, ‖k.map fun a : 𝔸 E ↦ a.1 w‖ ≤ c)
    (h_crd : V.vecAtPoint ξ = N • k *ᵥ W.vecAtPoint η) :
    ((∀ (i : n) (j : m), N * (k i j).2 ∈ Ô E) → η ∈ W.baseLattice → ξ ∈ V.baseLattice) ∧
    ‖V.archCoords ξ‖ ≤ N * c * ‖W.archCoords η‖ :=
  ⟨mem_baseLattice_of_vecAtPoint_eq h_crd, norm_archCoords_le_of_vecAtPoint_eq hk_norm h_crd⟩

/-- Let Ω be a compact subset of G_f, the finite part of the adelic unitary group. There is a
natural number c ≠ 0 with the following property. For γ in the rational unitary group, g and g' in G
and a real R, suppose that g⁻¹γg' (γ embedded by `V.ratEmbed`) has finite part in Ω and operator
norm at most R at every infinite place. If y lies in the lattice of `V.move g'`, then cγy lies in
the lattice of `V.move g` and its length there is at most cR times the length of y in
`V.move g'`. -/
lemma exists_smul_mulVec_mem_latticeBall {Ω : Set (Gf E n)} (hΩ : IsCompact Ω) :
    ∃ c ≠ (0 : ℕ), ∀ {γ : U V.J} {g g' : G E s} {R : ℝ},
      (g⁻¹ * V.ratEmbed γ * g').2 ∈ Ω →
      (∀ w : NumberField.InfinitePlace E,
        ‖(((g⁻¹ * V.ratEmbed γ * g').1 w).val.val : Matrix n n ℂ)‖ ≤ R) →
      ∀ y : n → E, y ∈ (V.move g').baseLattice →
        (c : E) • γ *ᵥ y ∈ (V.move g).latticeBall (c * R * ‖(V.move g').archCoords y‖) := by
  -- One integer `c` clears the denominators of all matrices in `Ω`.
  obtain ⟨c, hc, h_integral⟩ := exists_natCast_smul_mem_of_isCompact E
    (hΩ.image_of_continuous fun k : Gf E n ↦ (k.val.val : Matrix n n (𝔸f E)))
    (isOpen_Ô.matrix.mem_nhds (Ô E).matrix.zero_mem)
  refine ⟨c, hc, fun {γ g g' R} h_mem h_norm y hy ↦ ?_⟩
  -- The matrix of `g⁻¹ γ g'` takes the coordinates of `y` at `g'` to those of `γ y` at `g`.
  have h_crd : (V.move g).vecAtPoint ((c : E) • γ *ᵥ y) =
      c • (g⁻¹ * V.ratEmbed γ * g').adeleMatrix *ᵥ (V.move g').vecAtPoint y := by
    simp [vecAtPoint_move, ← ratEmbed_mulVec_vecAtPoint, ← G.adeleMatrix_mul, funext_iff]
  have h_entries : ∀ i j : n, (c : 𝔸f E) * ((g⁻¹ * V.ratEmbed γ * g').adeleMatrix i j).2 ∈ Ô E :=
    h_integral _ ⟨_, h_mem, rfl⟩
  exact ⟨mem_baseLattice_of_vecAtPoint_eq h_crd h_entries hy,
    norm_archCoords_le_of_vecAtPoint_eq (k := (g⁻¹ * V.ratEmbed γ * g').adeleMatrix) h_norm h_crd⟩

variable (V) in
/-- The hermitian form `V.J` takes algebraic integer values on pairs of vectors of the lattice
`V.baseLattice`. -/
lemma isIntegral_form {a b : n → E} (ha : a ∈ V.baseLattice) (hb : b ∈ V.baseLattice) :
    IsIntegral ℤ (star a ⬝ᵥ V.J *ᵥ b) := by
  -- The finite adelic image of the value is a sum of products of integral coordinates.
  have h_fin : (toAdele (star a ⬝ᵥ V.J *ᵥ b)).2 =
      ∑ i : n, star (V.vecAtPoint a i).2 * (V.vecAtPoint b i).2 := by
    rw [← stdForm_vecAtPoint]
    simp [dotProduct, stdForm, mulVec_diagonal, snd_sum]
  rw [← algebraMap_mem_Ô, ← toAdele_apply_snd, h_fin]
  exact sum_mem fun i _ ↦ mul_mem (star_mem_Ô (ha i)) (hb i)

variable (V) in
/-- The coordinates of the rational vector `a` in the basis `V.x` at the infinite place `w`, as a
vector in the Euclidean space `ℂ^n`. -/
def coordsAt (w : NumberField.InfinitePlace E) (a : n → E) : EuclideanSpace ℂ n :=
  .toLp 2 fun i : n ↦ (V.vecAtPoint a i).1 w

variable (V) in
/-- The length of `a` at one infinite place, in the coordinates of `V`, is at most its length
`‖V.archCoords a‖` over all infinite places. -/
lemma norm_coordsAt_le (w : NumberField.InfinitePlace E) (a : n → E) :
    ‖V.coordsAt w a‖ ≤ ‖V.archCoords a‖ := by
  rw [norm_eq, norm_eq, Fintype.sum_prod_type]
  -- The summand at `w` is at most the sum over all infinite places.
  exact Real.sqrt_le_sqrt <| single_le_sum (f := fun v ↦ ∑ i : n, ‖V.archCoords a (v, i)‖ ^ 2)
    (fun v _ ↦ by positivity) (mem_univ w)

variable (V) in
/-- The Cauchy–Schwarz inequality for the form at one infinite place `w`: in the embedding `Φ w`,
the value of the hermitian form `V.J` on `a` and `b` has absolute value at most the product of the
lengths of `a` and `b` at `w`. -/
lemma norm_form_le (w : NumberField.InfinitePlace E) (a b : n → E) :
    ‖Φ w (star a ⬝ᵥ V.J *ᵥ b)‖ ≤ ‖V.coordsAt w a‖ * ‖V.coordsAt w b‖ := by
  -- At `w` the value is `∑ ± star (a i) * b i` in coordinates.
  have h_place : Φ w (star a ⬝ᵥ V.J *ᵥ b) =
      ∑ i : n, star (V.coordsAt w a i) * (((s i : ℤ) : ℂ) * V.coordsAt w b i) := by
    rw [← toAdele_apply_fst, ← stdForm_vecAtPoint]
    simp [dotProduct, stdForm, mulVec_diagonal, fst_sum, coordsAt]
  calc ‖Φ w (star a ⬝ᵥ V.J *ᵥ b)‖
    _ ≤ ∑ i : n, ‖V.coordsAt w a i‖ * ‖V.coordsAt w b i‖ := by
      rw [h_place]
      exact norm_sum_le_of_le _ fun i _ ↦ by simp [abs_unit_intCast]
    _ ≤ ‖V.coordsAt w a‖ * ‖V.coordsAt w b‖ := by
      rw [norm_eq, norm_eq]
      exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

variable (V) in
/-- At each infinite place `w`, the value of the hermitian form `V.J` on `a` and `b`, embedded by
`Φ w`, has absolute value at most the product of the lengths of `a` and `b` over all infinite
places. -/
lemma norm_form_le_norm_archCoords_mul (w : NumberField.InfinitePlace E) (a b : n → E) :
    ‖Φ w (star a ⬝ᵥ V.J *ᵥ b)‖ ≤ ‖V.archCoords a‖ * ‖V.archCoords b‖ := by
  grw [V.norm_form_le w a b, V.norm_coordsAt_le w a, V.norm_coordsAt_le w b]

/-- Two vectors of the lattice of `V` whose lengths have product less than `1` are orthogonal for
the hermitian form `V.J`. -/
lemma form_eq_zero_of_norm_mul_lt_one {a b : n → E} (ha : a ∈ V.baseLattice)
    (hb : b ∈ V.baseLattice) (h_short : ‖V.archCoords a‖ * ‖V.archCoords b‖ < 1) :
    star a ⬝ᵥ V.J *ᵥ b = 0 := by
  -- The value of the form is an algebraic integer whose conjugates have norm less than `1`.
  exact eq_zero_of_forall_norm_lt_one (V.isIntegral_form ha hb) fun w ↦
    (V.norm_form_le_norm_archCoords_mul w a b).trans_lt h_short

/-- A definite space has no nonzero isotropic vector. Let `V` be a hermitian space with a point over
the CM field `E`: a matrix `J = V.J` over `E` and an invertible adelic matrix `x` with `xᴴJx` equal
to `diag(s)` at the infinite places and `1` at the finite places, for signs `s i = ±1` indexed by
the finite type `n`. If all signs are equal and `ξ ∈ E^n` has `ξᴴJξ = 0`, then `ξ = 0`. -/
lemma eq_zero_of_isotropic_of_definite {s : n → ℤˣ} {V : Space E n s}
    (h_definite : ∀ i j : n, s i = s j) (ξ : n → E) (h_iso : star ξ ⬝ᵥ V.J *ᵥ ξ = 0) :
    ξ = 0 := by
  -- Let `v` be the coordinates `x⁻¹ξ` at an infinite place `w`. There the value of the form is
  -- `vᴴ diag(s) v`, which is `± vᴴ v` as all signs are equal.
  ext i
  let w : NumberField.InfinitePlace E := Classical.ofNonempty
  let v : n → ℂ := fun j : n ↦ (V.vecAtPoint ξ j).1 w
  have h_form : star v ⬝ᵥ signMatrix s *ᵥ v = 0 := by
    rw [← stdForm_dotProduct_fst, V.stdForm_vecAtPoint, h_iso]
    simp
  have h_sign : signMatrix s *ᵥ v = ((s i : ℤ) : ℂ) • v := by
    ext j
    simp [signMatrix, mulVec_diagonal, h_definite j i]
  have h_norm : star v ⬝ᵥ v = 0 := by
    rw [h_sign, dotProduct_smul] at h_form
    simpa using h_form
  have h_vec : v = 0 := dotProduct_star_self_eq_zero.1 h_norm
  exact congrFun (eq_zero_of_vecAtPoint_fst_eq_zero h_vec) i

/-! ### Lower bounds for the first minimum -/

/-- If all signs are equal, so that `V` is definite, then its first minimum is at least `1`: every
nonzero lattice vector has length at least `1`. -/
lemma one_le_firstMinimum (h_definite : ∀ i j : n, s i = s j) : 1 ≤ V.firstMinimum := by
  -- A lattice vector of length less than `1` is isotropic, hence zero.
  refine le_firstMinimum_iff.2 ⟨le_rfl, fun y hy hy_ne ↦ le_of_not_gt fun h_short ↦ ?_⟩
  have h_iso : star y ⬝ᵥ V.J *ᵥ y = 0 := form_eq_zero_of_norm_mul_lt_one hy hy
    ((mul_le_of_le_one_right (norm_nonneg _) h_short.le).trans_lt h_short)
  exact hy_ne (eq_zero_of_isotropic_of_definite h_definite y h_iso)

/-- Let `V` be a hermitian space with a point over the CM field `E`: a matrix `J` and an adelic `x`
with `xᴴJx = diag(s)` at the infinite places and `1` at the finite places. If all signs `s i` are
equal, so that `V` is definite, then for every `g` in the adelic unitary group `G E s` the moved
space `V.move g`, with point `xg`, has `firstMinimum` equal to `1`. Here `firstMinimum` is
`min(1, inf ‖y‖)`, with `y` running over the nonzero vectors of `baseLattice` and `‖y‖` the norm of
`archCoords y`. -/
lemma firstMinimum_move_eq_one (h_definite : ∀ i j : n, s i = s j) (g : G E s) :
    (V.move g).firstMinimum = 1 :=
  le_antisymm firstMinimum_le_one (one_le_firstMinimum h_definite)

variable (V) in
/-- The lattice of `V` is discrete: only finitely many of its vectors have length at most `r`. -/
lemma finite_latticeBall (r : ℝ) : (V.latticeBall r).Finite := by
  -- The coordinates of these vectors lie in a compact box, and `E ^ n` is discrete in `𝔸 ^ n`.
  let box : Set (n → 𝔸 E) := Set.univ.pi fun _ ↦ Metric.closedBall 0 r ×ˢ Ô E
  have h_box : IsCompact box :=
    isCompact_univ_pi fun _ ↦ (isCompact_closedBall 0 r).prod isCompact_Ô
  have h_finite : (V.vecAtPoint ⁻¹' box).Finite :=
    isCovolOneLattice_ratVectors.finite_preimage (h_box.preimage_smul V.x⁻¹)
  refine h_finite.subset fun y ⟨h_mem, h_le⟩ i _ ↦ ⟨?_, h_mem i⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonempty]
  exact fun w ↦ (PiLp.norm_apply_le (V.archCoords y) (w, i)).trans h_le

/-- A nonzero rational vector has positive length. -/
lemma norm_archCoords_pos {y : n → E} (hy_ne : y ≠ 0) : 0 < ‖V.archCoords y‖ := by
  refine norm_pos_iff.2 fun h_zero ↦ hy_ne ?_
  exact eq_zero_of_vecAtPoint_fst_eq_zero (w := Classical.ofNonempty)
    (funext fun i ↦ show V.archCoords y (Classical.ofNonempty, i) = 0 by simp [h_zero])

/-- The first minimum of `V`, cut off at `1`, is positive. -/
lemma firstMinimum_pos : 0 < V.firstMinimum := by
  -- By discreteness only finitely many lengths are at most `1`. Let `l` be the least of `1` and
  -- the nonzero ones among them.
  let S : Set ℝ := insert 1 ((fun y : n → E ↦ ‖V.archCoords y‖) '' {y ∈ V.latticeBall 1 | y ≠ 0})
  have hS : S.Finite := (((V.finite_latticeBall 1).sep _).image _).insert 1
  obtain ⟨l, hl_mem, hl_least⟩ := Set.exists_min_image S id hS (Set.insert_nonempty _ _)
  have hl_pos : 0 < l := by
    obtain rfl | ⟨y, ⟨-, hy_ne⟩, rfl⟩ := hl_mem
    exacts [one_pos, norm_archCoords_pos hy_ne]
  have hl_one : l ≤ 1 := hl_least 1 (Set.mem_insert _ _)
  refine hl_pos.trans_le (le_firstMinimum_iff.2 ⟨hl_one, fun y hy hy_ne ↦ ?_⟩)
  obtain h_short | h_long := le_total ‖V.archCoords y‖ 1
  · exact hl_least _ (Set.mem_insert_of_mem _ ⟨y, ⟨⟨hy, h_short⟩, hy_ne⟩, rfl⟩)
  · exact hl_one.trans h_long

end New.Space

end FirstMinimum

/-!
## Short bases of lattices by transference

The lattice `L` of a hermitian space `V` contains a basis of `E ^ n` whose lengths are bounded by a
constant over the first minimum. For a nonzero `d` in the different, the dual of `2 d⁻¹ L` has no
nonzero vector shorter than the first minimum, as `L` is unimodular. So transference applies to
`2 d⁻¹ L`.
-/

section ShortBasis

open NumberField Matrix Submodule Fintype Finset RealInnerProductSpace Prod

namespace New.Space

variable {E n : Type*} [Field E] [CMType E]
variable [Fintype n] [DecidableEq n] {s : n → ℤˣ} (V : Space E n s)
variable {N : ℕ} [NeZero N]

/-- Let `V` be a hermitian space over the CM field `E`, given by a matrix `V.J` over `E` and a point
`x`, and let `V.baseLattice = E^n ∩ x_f Ô^n` be the `y` with `x⁻¹ y` integral at the finite places.
Let `d` be in the different of `E` and `a ∈ E ^ n`. If the trace from `E` to `ℚ` of `ξᴴ V.J a` is an
integer for every `ξ` in `V.baseLattice`, then `d • a` lies in `V.baseLattice`. -/
lemma smul_mem_baseLattice_of_trace_int {d : 𝓞 E} (h_diff : d ∈ differentIdeal ℤ (𝓞 E))
    {a : n → E} (h_trace : ∀ ξ : n → E, ξ ∈ V.baseLattice →
      ∃ k : ℤ, (Algebra.trace ℚ E (star ξ ⬝ᵥ V.J *ᵥ a) : ℝ) = k) :
    d.val • a ∈ V.baseLattice := by
  intro i
  change (V.vecAtPoint (d.val • a) i).2 ∈ Ô E
  -- The character `ψf` kills the pairing of `a` with every integral finite adelic vector `y`: the
  -- condition is closed, so the dense rational vectors suffice.
  have h_dense : DenseRange fun (ξ : n → E) (i : n) ↦ (V.vecAtPoint ξ i).2 := by
    have h_factor : (fun (ξ : n → E) (i : n) ↦ (V.vecAtPoint ξ i).2) =
        (fun y : n → 𝔸f E ↦ V.xFin⁻¹ • y) ∘ Pi.map fun _ : n ↦ algebraMap E (𝔸f E) := by
      funext ξ i
      -- `-coe_units_inv` keeps the inverse of the point in the form that `map_inv` produces.
      simp [-coe_units_inv, xFin, ← map_inv, mulVec, vecAtPoint, dotProduct, snd_sum,
        Units.smul_def]
    rw [h_factor]
    exact (MulAction.surjective V.xFin⁻¹).denseRange.comp
      (.piMap fun _ ↦ denseRange_algebraMap_finAdele) (by fun_prop)
  have h_char : ∀ y : n → 𝔸f E, (∀ i ∈ Set.univ, y i ∈ (Ô E : Set (𝔸f E))) →
      ψf E (star y ⬝ᵥ snd ∘ V.vecAtPoint a) = 1 := by
    refine isClosed_property h_dense
      (isClosed_imp (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ô)
        (isClosed_eq (by fun_prop) continuous_one)) fun ξ hξ ↦ ?_
    obtain ⟨k, hk⟩ := h_trace ξ fun j ↦ hξ j trivial
    have h_pair : (star fun j : n ↦ (V.vecAtPoint ξ j).2) ⬝ᵥ snd ∘ V.vecAtPoint a =
        algebraMap E (𝔸f E) (star ξ ⬝ᵥ V.J *ᵥ a) := by
      rw [← toAdele_apply_snd, ← stdForm_vecAtPoint]
      simp [dotProduct, stdForm, mulVec_diagonal, snd_sum]
    rw [h_pair, ψf_coe]
    exact fourierChar_eq_one_iff.2 ⟨k, hk⟩
  -- So the finite part of each coordinate of `V.vecAtPoint a` lies in the inverse different.
  have h_inv_diff (u : 𝔸f E) (hu : u ∈ Ô E) : ψf E (u * (V.vecAtPoint a i).2) = 1 := by
    simpa using h_char (Pi.single i (star u)) (by simp [star_mem_Ô, hu, Pi.single_apply, apply_ite])
  simpa [↓map_smulₛₗ] using forall_ψf_mul_eq_one_iff.1 h_inv_diff d h_diff

/-- For `d` in `E` and a vector `x` of the archimedean coordinate space, the real inner product of
`x` with the coordinates of `(2 / d) ξ`, written with the components `(V.vecAtPoint ξ i).1 w` at the
infinite places `w` and the embeddings `Φ w` of `E`: the factor `1 / d` moves onto `x` as division
by the conjugate of `Φ w d`. -/
lemma inner_archCoords_two_div_smul (d : E) (x : EuclideanSpace ℂ (InfinitePlace E × n))
    (ξ : n → E) : ⟪x, V.archCoords ((2 / d) • ξ)⟫ = ∑ w : InfinitePlace E,
      2 * (∑ i : n, star ((V.vecAtPoint ξ i).1 w) * (x ⟨w, i⟩ / star (Φ w d))).re := by
  have h_term (z v e : ℂ) : ⟪z, 2 / e * v⟫ = 2 * (star v * (z / star e)).re := by
    simp [inner, div_eq_mul_inv]
    ring
  have h_smul : V.archCoords ((2 / d) • ξ) =
      WithLp.toLp 2 fun p : InfinitePlace E × n ↦ 2 / Φ p.1 d * (V.vecAtPoint ξ p.2).1 p.1 := by
    simp [archCoords, map_ofNat]
  simp only [h_smul, PiLp.inner_apply, sum_prod_type, h_term, mul_sum, Complex.re_sum]

/-- Let `V` be a hermitian space with a point, `d` a nonzero element of the different of `E`, and
`x` a nonzero vector of the Euclidean space indexed by the infinite places and `n`. Suppose the
real inner product of `x` with `V.archCoords ((2 / d) ξ)` is an integer for every `ξ` in
`V.baseLattice = E^n ∩ x_f Ô^n`. Here `V.archCoords` sends a vector to the archimedean components of
its image under the inverse of the point. Then `‖x‖ ≥ V.firstMinimum`, which is
`min(1, least length of a nonzero lattice vector)`. -/
lemma firstMinimum_le_norm_of_inner_int {d : 𝓞 E} (hd : d ≠ 0)
    (h_diff : d ∈ differentIdeal ℤ (𝓞 E)) {x : EuclideanSpace ℂ (InfinitePlace E × n)}
    (hx_ne : x ≠ 0)
    (h_int : ∀ ξ : n → E, ξ ∈ V.baseLattice →
      ∃ k : ℤ, ⟪x, V.archCoords ((2 / d.val) • ξ)⟫ = k) :
    V.firstMinimum ≤ ‖x‖ := by
  -- With `t = (x_V⁻¹)ᴴ (x / star d)` at the infinite places (x_V the point of `V`), pairing with
  -- `x` becomes a dot product with `t`. It will turn out that `t = J a` at the infinite places,
  -- with `d • a` in the lattice and as long as `x`.
  let t : n → 𝔸 E := V.x⁻¹.1ᴴ *ᵥ fun i : n ↦
    (fun w : InfinitePlace E ↦ x ⟨w, i⟩ / star (Φ w d), 0)
  have h_pair (ξ : n → E) :
      ⟪x, V.archCoords ((2 / d.val) • ξ)⟫ =
        ∑ w : InfinitePlace E, 2 * ((star (toAdele ∘ ξ) ⬝ᵥ t).1 w).re := by
    rw [inner_archCoords_two_div_smul]
    simp [t, ↓← star_mulVec_dotProduct, vecAtPoint, dotProduct, fst_sum]
  -- Every rational vector has a multiple in the lattice, so the coordinates of `t` pair rationally
  -- with `E`. Hence they come from `E`: `t` is `V.J *ᵥ a` at the infinite places.
  have h_rat (i : n) (b : E) : ∃ q : ℚ, ∑ w : InfinitePlace E, 2 * (Φ w b * (t i).1 w).re = q := by
    obtain ⟨M, hM, h_mem⟩ := V.exists_smul_mem_baseLattice (Pi.single i (star b))
    obtain ⟨k, hk⟩ := h_int _ h_mem
    have h_eq : (M : ℝ) * ∑ w : InfinitePlace E, 2 * (Φ w b * (t i).1 w).re = k := by
      rw [smul_comm, map_nsmul, inner_smul_right_eq_smul, h_pair, nsmul_eq_mul] at hk
      simpa [dotProduct, Pi.single_apply, apply_ite] using hk
    exact ⟨k / M, by simp [← h_eq, hM]⟩
  choose c hc using fun i : n ↦ exists_eq_Φ_of_forall_sum_re_rat (h_rat i)
  obtain ⟨a, rfl⟩ : ∃ a : n → E, V.J *ᵥ a = c := mulVec_surjective_iff_isUnit.2 V.isUnit_J c
  -- Apply `(x_V)ᴴ` to `t = J a` at `w`: by `map_J` the sides agree up to the factor `d` and the
  -- signs `s`.
  have h_abs (w : InfinitePlace E) (i : n) :
      ‖x ⟨w, i⟩‖ = ‖Φ w d.val * (V.vecAtPoint a i).1 w‖ := by
    have h_left : ((V.x.1ᴴ *ᵥ t) i).1 w = x ⟨w, i⟩ / star (Φ w d) := by
      simp [t, ← conjTranspose_mul]
    have h_right : ((V.x.1ᴴ *ᵥ t) i).1 w = (s i : ℤ) * (V.vecAtPoint a i).1 w := by
      trans ((V.x.1ᴴ *ᵥ V.J.map toAdele *ᵥ toAdele ∘ a) i).1 w
      · simp [mulVec, hc, dotProduct, fst_sum]
      · simp [map_J, ← mul_assoc, ← conjTranspose_mul, ← (diagonal _).mulVec_mulVec, vecAtPoint,
          stdForm, mulVec_diagonal]
    rw [h_left, div_eq_iff (by simp [hd])] at h_right
    simp [h_right, abs_unit_intCast, mul_comm]
  have h_norm : ‖x‖ = ‖V.archCoords (d.val • a)‖ := by
    simp [PiLp.norm_eq_of_L2, archCoords, h_abs, -algebraMap_smul]
  rw [h_norm]
  refine V.firstMinimum_le (fun i ↦ ?_) fun h0 ↦ hx_ne (by simpa [h0] using h_norm)
  -- It remains to see that `d • a` is in the lattice, which holds as ξᴴJa has integral trace for
  -- ξ in the lattice.
  refine V.smul_mem_baseLattice_of_trace_int h_diff (fun ξ hξ ↦ ?_) i
  obtain ⟨k, hk⟩ := h_int ξ hξ
  refine ⟨k, ?_⟩
  calc (Algebra.trace ℚ E (star ξ ⬝ᵥ V.J *ᵥ a) : ℝ)
    _ = ∑ w : InfinitePlace E, 2 * (Φ w (star ξ ⬝ᵥ V.J *ᵥ a)).re := trace_eq_sum_Φ _
    _ = ⟪x, V.archCoords ((2 / d.val) • ξ)⟫ := by simp [h_pair, hc, dotProduct, fst_sum]
    _ = k := hk

/-- Approximation by lattice vectors. Let `d` be a nonzero element of the different of `E`. Every
point `u` of the archimedean coordinate space lies within `(2 f n)² / λ` of the archimedean
coordinates of `(2 / d) a` for some `a` in the lattice `V.baseLattice`. Here `n` in the bound means
`Fintype.card n`, and `f` is the number of infinite places. `λ` is the first minimum
`V.firstMinimum` of `V`, cut off at `1`. -/
lemma exists_norm_sub_archCoords_le {d : 𝓞 E} (hd : d ≠ 0) (h_diff : d ∈ differentIdeal ℤ (𝓞 E))
    (u : EuclideanSpace ℂ (InfinitePlace E × n)) :
    ∃ a ∈ V.baseLattice, ‖u - V.archCoords ((2 / d.val) • a)‖ ≤
      (2 * (Core.numInfPlaces E * Fintype.card n)) ^ 2 / V.firstMinimum := by
  -- Transference for `2 d⁻¹ L` in the coordinate space, of real dimension `2 f n`; a nonzero
  -- vector of its dual has length at least `V.firstMinimum`.
  let Λ : Submodule ℤ (EuclideanSpace ℂ (InfinitePlace E × n)) :=
    (V.baseLattice.map
      (.mk' (fun ξ : n → E ↦ V.archCoords ((2 / d.val) • ξ)) (by simp))).toIntSubmodule
  have h_dual (x : EuclideanSpace ℂ (InfinitePlace E × n))
      (hx : x ∈ LinearMap.BilinForm.dualSubmodule (innerₗ _) Λ) (hx_ne : x ≠ 0) :
      V.firstMinimum ≤ ‖x‖ :=
    V.firstMinimum_le_norm_of_inner_int hd h_diff hx_ne fun ξ hξ ↦
      let ⟨k, hk⟩ := hx _ ⟨ξ, hξ, rfl⟩
      ⟨k, by simpa using hk.symm⟩
  simpa [Λ, ← mem_toAddSubgroup, finrank_real_of_complex] using
    weak_transference_covering_radius Λ V.firstMinimum_pos h_dual u

/-- A set `S` of rational vectors spans `E ^ n` over `E` if the archimedean coordinates
`V.archCoords ξ` (the components of `x⁻¹ ξ` at the infinite places, `x` the point of `V`) of its
members span their space over `ℝ`. -/
lemma span_eq_top_of_span_archCoords {S : Set (n → E)}
    (h_span : span ℝ (V.archCoords '' S) = ⊤) : span E S = ⊤ := by
  -- A linear form `φ` on `E ^ n` extends at a place `w` to a real linear map `ψ` on the
  -- coordinate space. If `φ` vanishes on `S`, then `ψ = 0`, so `φ = 0`.
  by_contra h_ne
  obtain ⟨φ, hφ_ne, hφ⟩ := (span E S).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 h_ne)
  let w : InfinitePlace E := Classical.arbitrary _
  let ψ : EuclideanSpace ℂ (InfinitePlace E × n) →ₗ[ℝ] ℂ :=
    { toFun u := ∑ i : n, (∑ j : n, (V.x.val i j).1 w * u (w, j)) * Φ w (φ (Pi.single i 1))
      map_add' u v := by simp [mul_add, add_mul, sum_add_distrib]
      map_smul' t u := by simp [mul_sum, sum_mul, mul_assoc, mul_left_comm] }
  have h_extend (ξ : n → E) : ψ (V.archCoords ξ) = Φ w (φ ξ) := by
    have h_frame (i : n) : ∑ j : n, (V.x.val i j).1 w * V.archCoords ξ (w, j) = Φ w (ξ i) := by
      simpa [mulVec, dotProduct, fst_sum, archCoords] using congrArg (fun v : n → 𝔸 E ↦ (v i).1 w)
        (show V.x.val *ᵥ V.vecAtPoint ξ = toAdele ∘ ξ by simp [vecAtPoint])
    have h_sum : φ ξ = ∑ i : n, ξ i * φ (Pi.single i 1) := by
      simpa using congrArg φ (pi_eq_sum_univ' ξ)
    simp [ψ, h_frame, h_sum]
  have hψ : ψ = 0 := LinearMap.ext_on h_span <| Set.forall_mem_image.2 fun ξ hξ ↦ by
    simp [h_extend, LinearMap.mem_ker.1 (hφ (subset_span hξ))]
  exact hφ_ne (LinearMap.ext fun ξ ↦ by simpa [hψ] using (h_extend ξ).symm)

section

variable {E n : Type*} [Field E] [NumberField E] [Fintype n]

instance : NeZero (differentIdeal ℤ (𝓞 E)).absNorm :=
  ⟨mt Ideal.absNorm_eq_zero_iff.mp differentIdeal_ne_bot⟩

variable (E n) in
/-- The constant `6 N (f n)²` in the bound for short bases, where `f` is the number of infinite
places of `E` and `n` is the rank. -/
noncomputable abbrev shortBasisConst (N : ℕ) : ℕ :=
  6 * N * (Core.numInfPlaces E * Fintype.card n) ^ 2

end

/-- Short bases. `V` is a hermitian space with a point: a matrix `J` over `E` and `x ∈ GL_n(𝔸)` with
`xᴴJx` equal to `diag(s)` at the infinite places and `1` at the finite places. Let `N ≠ 0` be a
natural number in the different of `E`. The lattice `V.baseLattice` contains a basis of `E ^ n`, the
columns of `Y`, whose vectors `y` have length `‖V.archCoords y‖` at most `6 N (f n)² / λ`. Here `n`
in the bound means `Fintype.card n`, `f` is the number of infinite places and `λ` the first minimum
of `V`, cut off at `1`. The constant `shortBasisConst E n N` is `N / 2` times the transference bound
`3 (2 f n)²` in real dimension `2 f n`. -/
lemma exists_short_basis (h_diff : (N : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E)) :
    ∃ Y : GL n E, ∀ j : n,
      Y.val.col j ∈ V.latticeBall (shortBasisConst E n N / V.firstMinimum) := by
  -- The vectors `(2 / N) a`, for `a` in the lattice, come within `r` of every point. So those of
  -- length at most `3 r` span, and then `a` has length at most `3 r N / 2`.
  suffices h_top : span E (V.latticeBall (shortBasisConst E n N / V.firstMinimum)) = ⊤ from
    exists_GL_col_mem_of_span _ h_top.ge
  cases isEmpty_or_nonempty n
  · exact Subsingleton.elim _ _
  let r : ℝ := (2 * (Core.numInfPlaces E * card n)) ^ 2 / V.firstMinimum
  have hr : 0 < r := div_pos (by positivity) V.firstMinimum_pos
  have h_scale (a : n → E) :
      V.archCoords ((2 / (N : 𝓞 E).val) • a) = (2 / N : ℝ) • V.archCoords a := by
    simp [div_eq_inv_mul, mul_smul, map_inv_natCast_smul _ E ℝ, two_smul]
  have hN : (0 : ℝ) < N := mod_cast NeZero.pos N
  have h_span : span ℝ {x ∈ (fun a : n → E ↦ (2 / N : ℝ) • V.archCoords a) '' V.baseLattice |
      ‖x‖ ≤ 3 * r} = ⊤ :=
    span_norm_le_eq_top_of_covering hr fun u ↦
      let ⟨a, ha, h_near⟩ := V.exists_norm_sub_archCoords_le NeZero.out h_diff u
      ⟨_, ⟨a, ha, (h_scale a).symm⟩, h_near⟩
  refine V.span_eq_top_of_span_archCoords (top_unique (h_span.ge.trans (span_le.2 ?_)))
  rintro _ ⟨⟨a, ha, rfl⟩, h_short⟩
  rw [norm_smul, Real.norm_of_nonneg (by positivity)] at h_short
  refine smul_mem _ _ (subset_span ⟨a, ⟨ha, ?_⟩, rfl⟩)
  calc ‖V.archCoords a‖
    _ ≤ (2 / N : ℝ)⁻¹ * (3 * r) := (le_inv_mul_iff₀ (by positivity)).2 h_short
    _ = shortBasisConst E n N / V.firstMinimum := by
      simp [r, shortBasisConst]
      field

/-- Short bases in the standard space `New.stdSpace`, which has all signs `1` and so is definite.
Let `N ≠ 0` be a natural number in the different of `E` and `g` a finite adelic unitary matrix. Some
`Y` in `GL n E` has `g⁻¹ Y` integral (all entries in `Ô E`, `New.IsIntMatrix`) and entries of
absolute value at most `6 N (f n)²` at every complex embedding, where `f` is the number of infinite
places. -/
lemma exists_short_basis_stdSpace (h_diff : (N : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E)) (g : Gf E n) :
    ∃ Y : GL n E,
      IsIntMatrix (Ô E)
        ((g⁻¹.val.val : Matrix n n (𝔸f E)) * Y.val.map (algebraMap E (𝔸f E))) ∧
      ∀ (φ : E →+* ℂ) (i j : n), ‖φ (Y i j)‖ ≤ shortBasisConst E n N := by
  -- Take a short basis at the point `(1, g)` of the standard space, which is definite.
  let P : Space E n (fun _ : n ↦ 1) := (stdSpace E n).move (1, g)
  obtain ⟨Y, hY⟩ : ∃ Y : GL n E, ∀ j : n,
      Y.val.col j ∈ P.latticeBall (shortBasisConst E n N / P.firstMinimum) :=
    P.exists_short_basis h_diff
  choose h_mem h_norm using hY
  refine ⟨Y, fun i j ↦ ?_, fun φ i j ↦ ?_⟩
  · -- An entry of `g⁻¹ Y` is a finite coordinate of a column of `Y` at the point `(1, g)`.
    have h_entry : (g⁻¹.val.val * Y.val.map (algebraMap E (𝔸f E))) i j =
        (P.vecAtPoint (Y.val.col j) i).2 := by
      simp [P, ↓vecAtPoint_move, Matrix.mul_apply, Matrix.mulVec, dotProduct, vecAtPoint, snd_sum]
    rw [h_entry]
    exact h_mem j i
  -- Here `1 ≤ firstMinimum`, and the norm of a column bounds its coordinate at the place of `φ`.
  have h_min : 1 ≤ P.firstMinimum := one_le_firstMinimum fun _ _ ↦ rfl
  have h_abs : ‖φ (Y i j)‖ = ‖P.archCoords (Y.val.col j) (.mk φ, i)‖ := by
    simp [P, archCoords, ↓vecAtPoint_move, Matrix.mulVec, dotProduct, ← InfinitePlace.apply,
      vecAtPoint, fst_sum, Matrix.one_apply]
  calc ‖φ (Y i j)‖
    _ ≤ ‖P.archCoords (Y.val.col j)‖ := h_abs.trans_le (PiLp.norm_apply_le _ _)
    _ ≤ shortBasisConst E n N / P.firstMinimum := h_norm j
    _ ≤ shortBasisConst E n N := div_le_self (Nat.cast_nonneg _) h_min

end New.Space

end ShortBasis

/-! ## The first minimum of the lattice of an orthogonal sum of spaces -/

section FirstMinimumSum

open Function New Space EuclideanSpace

/-- The shortest vector length, cut off at 1 (`New.Space.firstMinimum`), of the lattice of V ⊕ W
(`New.Space.sum`) moved by the block sum `G.sum (g, h)` is at least the minimum of those of V moved
by g and W moved by h. -/
lemma New.Rows.inf_le_firstMinimum_sum {E n n' : Type*} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] [Fintype n'] [DecidableEq n'] {s : n → ℤˣ} {s' : n' → ℤˣ} {g : G E s}
    {h : G E s'} {V : Space E n s} {W : Space E n' s'} :
    (V.move g).firstMinimum ⊓ (W.move h).firstMinimum ≤
      ((V.sum W).move (G.sum (g, h))).firstMinimum := by
  refine le_firstMinimum_iff.2 ⟨by simp [firstMinimum_le_one], fun y hy hy₀ ↦ ?_⟩
  -- both components of `y` are lattice vectors, and their squared lengths add up
  obtain ⟨h_inl, h_inr⟩ :
      y ∘ .inl ∈ (V.move g).baseLattice ∧ y ∘ .inr ∈ (W.move h).baseLattice := by
    simpa [baseLattice, ↓vecAtPoint_move, vecAtPoint, sum, comp_def, ← map_inv,
      Matrix.fromBlocks_mulVec] using hy
  have h_sq : ‖((V.sum W).move (.sum (g, h))).archCoords y‖ ^ 2 =
      ‖(V.move g).archCoords (y ∘ .inl)‖ ^ 2 + ‖(W.move h).archCoords (y ∘ .inr)‖ ^ 2 := by
    simp [norm_sq_eq, archCoords, ↓vecAtPoint_move, vecAtPoint, sum, comp_def, ← map_inv,
      Fintype.sum_prod_type, Matrix.fromBlocks_mulVec, Finset.sum_add_distrib]
  -- one of the components is nonzero, and it is not longer than `y`
  obtain h_left | h_right := Sum.exists.1 (ne_iff.1 hy₀)
  · exact inf_le_left.trans <| (firstMinimum_le h_inl (ne_iff.2 h_left)).trans <|
      le_of_sq_le_sq (by simp [h_sq]) (norm_nonneg _)
  · exact inf_le_right.trans <| (firstMinimum_le h_inr (ne_iff.2 h_right)).trans <|
      le_of_sq_le_sq (by simp [h_sq]) (norm_nonneg _)

end FirstMinimumSum

end

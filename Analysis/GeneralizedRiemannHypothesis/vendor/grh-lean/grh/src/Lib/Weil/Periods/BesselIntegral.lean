import Lib.Adelic.QuotientMeasure.UnfoldingInStages
import Lib.Weil.DualPair.WeilAction

/-!
# Integrals over the Bessel subgroup and the orbits surviving unipotent twists

A hermitian space `V` is graded by `Y`, which presents it as `X` plus a string of `s` vectors, and
`B` is its Bessel (Fourier–Jacobi) subgroup. For a second space `V'` graded by `Y'` with a string of
length `s - 1`, the file determines which terms of a Fourier expansion over rational maps
`w : V → V'` survive the unipotent twists. Each such `w` can be moved to a map of type
`New.Grading.AgreesWithStringMap`, and if that map also survives with degrees `Y'.gradeOf`, then
that map minus `Y.stringMap Y'` has degree `≥ 0`.

## Main definitions and results

* `New.Grading.isCocompact_ratBessel`: the adelic group `B` is compact modulo its rational points.
* `New.Grading.besselMeasure`: the measure that integrates over `B` modulo its rational points.
* `New.Grading.integral_besselMeasure_eq_of_mean`: such an integral is a fixed multiple of an
  integral over `U(X)` modulo its rational points, after averaging over the row of the unipotent
  part.
* `New.Grading.Survives`: no unipotent twist kills the term at `w`.
* `New.Grading.exists_agreesWithStringMap`: a rational `w` that is not killed can be moved by a
  rational unitary element of `V'` to a map of type `New.Grading.AgreesWithStringMap`;
  `New.Grading.agreesWithStringMap_mul_iff`: that element is unique up to `Y'.besselGroup`.
* `New.Grading.hasDegreeGe_of_survives`: a map of type `New.Grading.AgreesWithStringMap` is killed
  unless `w - Y.stringMap Y'` has degree `≥ 0`.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.eichlerMap`: `eichlerMap J x u ς` is v ↦ v + h(u, v)x − h(x, v)(u + ςx), h the form of J.
* `New.Space.homBicharacter`: the phase `ψ ((j / 2) tr (y† x))` of two adelic maps `x`, `y`.

## Relation to the literature

Known; see `Lib.Weil.Periods.Unfolding` and `Lib.Adelic.Reduction.FiniteVolume` for sources.
-/

/-!
## The Bessel subgroup, Eichler maps and integrals over [B]

`Y : New.Grading V N X s` presents the hermitian space `V` as `X` plus a string of `s` vectors, with
Gram matrix `gradedGram` built from a nonzero scalar `N : E`, graded by `New.Grading.gradeOf` (0 on
`X`, `s - 1 - 2 i` on the string). `New.Grading.unipotent` is the unipotent group that raises
grades, `New.Grading.inclX` embeds `U(X)`, and `New.Grading.besselGroup` is the Bessel
(Fourier–Jacobi) subgroup `B` that contains both. `Y.genericConst` is a nonzero scalar of `E`
carried by `Y`; with `c` for this scalar, the factors of `Y.shift` are `c`, `-N c` and `-N c²`.

`G E ε` is the adelic group containing the isometries of `V`; `U(X)` is `G E (1 : X → ℤˣ)`, the
group of the definite space `stdSpace E X`. `New.Space.ratCoordMatrix` is the matrix `x g x⁻¹` of
`g` in rational coordinates.

`Subgroup.quotMeasure` is the measure that integrates invariant functions over the quotient by a
subgroup (Haar measure times a cutoff). `New.IsContPeriodic` says that a function is continuous and
periodic under a subgroup of translations, and `New.quotMean` is its mean over the quotient.
-/

namespace New.Grading

open Space Matrix MeasureTheory Measure Subgroup Fintype

variable {E ι X : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
  {s : ℕ} {ε : ι → ℤˣ} {N : E} {V : Space E ι ε} (Y : Grading V N X s)

/-- A matrix over `E` can be defined by downward recursion on a level `w : ι → ℤ`. Let `n - 1`
strictly lower the level (its entry `(i, l)` vanishes unless `w i < w l`), and let `q : 𝔸 E → E`
be any map. Then some `Z` is the identity on and below the diagonal blocks of `w`, and each entry
of `Z` above them is `q` of the same entry of `(n - 1) * Z`. -/
private lemma exists_matrix_eq_ite_of_sub_one_lowers (w : ι → ℤ) (q : 𝔸 E → E)
    {n : Matrix ι ι (𝔸 E)} (hn : ∀ i l : ι, ¬w i < w l → (n - 1) i l = 0) :
    ∃ Z : Matrix ι ι E, ∀ i k : ι,
      Z i k = if w k ≤ w i then (1 : Matrix ι ι E) i k else q (((n - 1) * Z.map toAdele) i k) := by
  -- Row `i` of `Z` is computed from the rows `l` with `w i < w l`. This relation is well founded
  -- as `ι` is finite: use the preorder pulled back along `w`.
  have wf : WellFounded (fun l i : ι ↦ w i < w l) := by
    let := Preorder.lift w
    exact wellFounded_gt
  let step (k i : ι) (Z : ∀ l : ι, w i < w l → E) : E :=
    if w k ≤ w i then (1 : Matrix ι ι E) i k
    else q (∑ l : ι, (n - 1) i l * if h : w i < w l then toAdele (Z l h) else 0)
  let Z : Matrix ι ι E := fun i k ↦ wf.fix (step k) i
  refine ⟨Z, fun i k ↦ ?_⟩
  -- Only the rows `l` with `w i < w l` enter the sum, since `(n - 1) i l = 0` for the others.
  have h_sum : (∑ l : ι, (n - 1) i l * if h : w i < w l then toAdele (Z l k) else 0) =
      ((n - 1) * Z.map toAdele) i k := by
    rw [mul_apply]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    by_cases h : w i < w l
    · rw [dite_eq_left h, Matrix.map_apply]
    · rw [dite_eq_right h, hn i l h, zero_mul, zero_mul]
  rw [← h_sum]
  exact wf.fix_eq (step k) i

/-- A rational unitriangular matrix moves `n` to bounded entries. Let `q a` be a rational shift of
each adele `a` into `A` (`toAdele (q a) + a ∈ A`), and let `n - 1` strictly lower the level `w`.
Then some rational `r`, unitriangular for `w`, makes every entry of `n * r` equal to `0`, `1` or an
element of `A`. -/
private lemma exists_unitriangular_mul_map_mem_matrix (w : ι → ℤ) {A : Set (𝔸 E)} {q : 𝔸 E → E}
    (hq : ∀ a : 𝔸 E, toAdele (q a) + a ∈ A) (n : Matrix ι ι (𝔸 E))
    (hn : ∀ i l : ι, ¬w i < w l → (n - 1) i l = 0) :
    ∃ r ∈ unitriangular w E,
      n * (r : Matrix ι ι E).map toAdele ∈ (insert 0 (insert 1 A)).matrix := by
  -- `Z` is the identity on and below the diagonal blocks, and above them each entry of `Z` is the
  -- rational shift of the entry of `(n - 1) * Z`; so `n * Z = Z + (n - 1) * Z` has entries in `A`
  -- above the diagonal blocks, and those of `1` on and below them.
  obtain ⟨Z, hZ⟩ := exists_matrix_eq_ite_of_sub_one_lowers w q hn
  have Z_tri (i k : ι) (h : w k ≤ w i) : Z i k = (1 : Matrix ι ι E) i k :=
    (hZ i k).trans (ite_eq_left h)
  have Z_det : IsUnit Z.det := by
    rw [det_eq_one_of_unitriangular Z_tri]
    exact isUnit_one
  obtain ⟨r, rfl⟩ : IsUnit Z := (isUnit_iff_isUnit_det Z).mpr Z_det
  refine ⟨r, mem_agreeWithOneOn.mpr Z_tri, fun i k ↦ ?_⟩
  have h_entry_eq : (n * (r : Matrix ι ι E).map toAdele) i k =
      toAdele ((r : Matrix ι ι E) i k) + ((n - 1) * (r : Matrix ι ι E).map toAdele) i k := by
    simp [sub_mul]
  rw [h_entry_eq, hZ i k]
  split_ifs with h
  · -- On and below the diagonal blocks `(n - 1) * r` vanishes, and `n * r` has the entries of `1`.
    have h_sub_one_mul_eq_zero : ((n - 1) * (r : Matrix ι ι E).map toAdele) i k = 0 := by
      rw [mul_apply]
      refine Finset.sum_eq_zero fun l _ ↦ ?_
      by_cases hl : w i < w l
      · have hlk : l ≠ k := by grind
        rw [Matrix.map_apply, Z_tri l k (h.trans hl.le), one_apply_ne hlk, map_zero, mul_zero]
      · rw [hn i l hl, zero_mul]
    simp [h_sub_one_mul_eq_zero, apply_ite, one_apply]
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (hq _))

open scoped Pointwise in
/-- The rational points are cocompact in the adelic Bessel subgroup B of Y: there is a compact C ⊆ B
such that every g ∈ B has a rational γ ∈ B with γg ∈ C. -/
lemma isCocompact_ratBessel : (Y.ratBessel.subgroupOf Y.besselGroup).IsCocompact := by
  -- Reduce first the image of `g` in `U(X)`, which is compact modulo rational points, and then the
  -- unipotent part, whose entries are moved into a compact set by a rational unitriangular matrix.
  -- Adding the rational `q a` moves an adele `a` into the compact set `A`.
  obtain ⟨A, hA, adele_cover⟩ : ∃ A : Set (𝔸 E), IsCompact A ∧
      ∀ a : 𝔸 E, ∃ γ ∈ ratAdeles E, γ + a ∈ A :=
    IsCovolOneLattice.exists_compact_cover (ratAdeles E)
  have rational_shift (a : 𝔸 E) : ∃ x : E, toAdele x + a ∈ A := by
    obtain ⟨γ, γ_rat, γ_mem⟩ := adele_cover a
    obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp γ_rat
    exact ⟨x, γ_mem⟩
  choose q hq using rational_shift
  -- `U(X)` is definite: the rational point `δ a` moves `a` into the compact set `D`.
  obtain ⟨D, hD, definite_cover⟩ : ∃ D : Set (G E (1 : X → ℤˣ)), IsCompact D ∧
      ∀ a : G E (1 : X → ℤˣ), ∃ γ ∈ (stdSpace E X).Γ, γ * a ∈ D :=
    (stdSpace E X).isCocompact_of_definite
  choose δ hδ δ_mem using definite_cover
  -- The unipotent part raises grades, so it strictly lowers the level `w = -grade`.
  let w (i : ι) : ℤ := -Y.gradeOf i
  -- If `m⁻¹` in rational coordinates times a rational unitriangular matrix has entries in
  -- `A ∪ {0, 1}`, a rational unitriangular isometry `β` moves `m` into the compact set `K`.
  obtain ⟨K, hK, exists_unitriangular_mul_mem_K⟩ : ∃ K : Set (G E ε), IsCompact K ∧
      ∀ (m : G E ε) (r : unitriangular w E),
        V.ratCoordMatrix m⁻¹ * ((r : GL ι E) : Matrix ι ι E).map toAdele ∈
          (insert 0 (insert 1 A)).matrix →
        ∃ β : U V.J, V.ratEmbed β * m ∈ K ∧ (β : GL ι E) ∈ unitriangular w E :=
    V.exists_isCompact_of_bounded_frame ((hA.insert 1).insert 0).matrix (unitriangular w E)
  -- `p` is the projection to `U(X)`: `r * (Y.inclX (p r))⁻¹` is unipotent and `p ∘ Y.inclX = id`.
  obtain ⟨p, -, p_unipotent, p_section, -⟩ := Y.exists_besselGroup_proj
  refine ⟨Subtype.val ⁻¹' (K * Y.inclX '' D),
    (hK.mul (hD.image_of_continuous Y.inclX)).preimage_val,
    fun g ↦ ?_⟩
  -- The rational point `γ` moves the `U(X)` part of `g` into `D`, and a rational unitriangular
  -- `β` moves the unipotent part `m` of `γ * g` into `K`.
  let γ : Y.besselGroup := ⟨Y.inclX (δ (p g)), Y.inclX_mem_besselGroup (δ (p g))⟩
  have γ_rat : (γ : G E ε) ∈ Y.ratBessel := Y.inclX_mem_ratBessel (hδ (p g))
  let m : G E ε := ↑(γ * g) * (Y.inclX (p (γ * g)))⁻¹
  have m_unipotent : m ∈ Y.unipotent := p_unipotent (γ * g)
  have m_inv_raises : ∀ i l : ι, ¬w i < w l → (V.ratCoordMatrix m⁻¹ - 1) i l = 0 := by
    intro i l h_not_lt
    have h_grade : Y.gradeOf i < Y.gradeOf l + 1 := by lia
    exact Y.mem_unipotent.mp (inv_mem m_unipotent) i l h_grade
  obtain ⟨r, hr, r_mem⟩ := exists_unitriangular_mul_map_mem_matrix w hq _ m_inv_raises
  obtain ⟨β, β_mem, β_uni⟩ := exists_unitriangular_mul_mem_K m ⟨r, hr⟩ r_mem
  -- `β` agrees with `1` wherever the grade does not rise, so it lies in the Bessel group.
  have β_bessel : V.ratEmbed β ∈ Y.besselGroup := by
    have h_matrix :
        V.ratCoordMatrix (V.ratEmbed β) = ((β : GL ι E) : Matrix ι ι E).map toAdele := by
      simp [ratEmbed, U.map, ratCoordMatrix]
    rw [mem_besselGroup_iff]
    intro i k h_grade_le _
    have β_ik : ((β : GL ι E) : Matrix ι ι E) i k = (1 : Matrix ι ι E) i k :=
      mem_agreeWithOneOn.mp β_uni i k (neg_le_neg h_grade_le)
    rw [h_matrix, Matrix.map_apply, β_ik]
    simp [one_apply, apply_ite]
  have β_rat : V.ratEmbed β ∈ Y.ratBessel := Subgroup.mem_inf.mpr ⟨⟨β, rfl⟩, β_bessel⟩
  let βB : Y.besselGroup := ⟨V.ratEmbed β, β_bessel⟩
  have βγ_rat : βB * γ ∈ Y.ratBessel.subgroupOf Y.besselGroup :=
    Subgroup.mem_subgroupOf.mpr (Y.ratBessel.mul_mem β_rat γ_rat)
  -- `β * γ * g` is the moved unipotent part `β * m` times `Y.inclX (δ (p g) * p g)`.
  have h_factor : ((βB * γ * g : Y.besselGroup) : G E ε) =
      V.ratEmbed β * m * Y.inclX (δ (p g) * p g) := by
    simp [βB, m, γ, p_section, mul_assoc]
  refine ⟨βB * γ, βγ_rat, ?_⟩
  rw [Set.mem_preimage, h_factor]
  exact Set.mul_mem_mul β_mem (Set.mem_image_of_mem Y.inclX (δ_mem (p g)))

/-- Let `J` be the Gram matrix of `V` mapped to the adeles, and `h(v, w) = vᴴ J w` its form. Let
`x` be supported in grades above `max 0 k` (hypothesis `hx`) and `y` in grade `-k` (hypothesis
`hy`). Then the Eichler map of `x`, `y` and `h(y, y) / 2` is the matrix, in rational coordinates,
of an element of the unipotent group `Y.unipotent`. -/
lemma exists_ratCoordMatrix_eq_eichlerMap (x y : ι → 𝔸 E) (k : ℤ)
    (hx : ∀ p : ι, Y.gradeOf p ≤ 0 ⊔ k → x p = 0)
    (hy : ∀ q : ι, Y.gradeOf q ≠ -k → y q = 0) :
    let J : Matrix ι ι (𝔸 E) := V.J.map toAdele
    ∃ u ∈ Y.unipotent, V.ratCoordMatrix u = eichlerMap J x y (toAdele 2⁻¹ * star y ⬝ᵥ J *ᵥ y) := by
  intro J
  have herm : Jᴴ = J := V.isHermitian_J.map _ fun a ↦ (star_toAdele a).symm
  -- `J` pairs the grades `a` and `-a`: entry `a` of `z* J` is `z̄` at the dual index `σ a`, of
  -- grade `-grade a`, times an entry of the Gram matrix.
  have h_vecMul (z : ι → 𝔸 E) (a : ι) : (star z ᵥ* J) a =
      star z (Y.stringReversal a) * gradedGram Y.indexEquiv N (Y.stringReversal a) a :=
    Y.vecMul_J_apply (star z) a
  -- A vector `z` that vanishes at the duals of the grades above `max 0 k` (where `x` lives) is
  -- orthogonal to `x`. This applies to `x` itself, of positive grades, and to `y`, of grade `-k`.
  have orth_x (z : ι → 𝔸 E) (hz : ∀ a : ι, ¬Y.gradeOf a ≤ 0 ⊔ k → z (Y.stringReversal a) = 0) :
      star z ⬝ᵥ J *ᵥ x = 0 := by
    rw [dotProduct_mulVec, dotProduct]
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    by_cases ha : Y.gradeOf a ≤ 0 ⊔ k
    · rw [hx a ha, mul_zero]
    · rw [h_vecMul, Pi.star_apply, hz a ha, star_zero, zero_mul, zero_mul]
  have h_iso : star x ⬝ᵥ J *ᵥ x = 0 := orth_x x fun a ha ↦ hx _ (by grind [gradeOf_stringReversal])
  have h_orth : star y ⬝ᵥ J *ᵥ x = 0 := orth_x y fun a ha ↦ hy _ (by grind [gradeOf_stringReversal])
  -- The form is hermitian, so `h(y, y)` is fixed by `star` and is the trace of its half.
  have half : toAdele 2⁻¹ * star y ⬝ᵥ J *ᵥ y + star (toAdele 2⁻¹ * star y ⬝ᵥ J *ᵥ y) =
      star y ⬝ᵥ J *ᵥ y := by
    norm_num [star_mul', star_dotProduct_mulVec_comm herm y y, star_toAdele, ← add_mul, ← map_add]
  obtain ⟨u, hu⟩ : ∃ u : G E ε,
      V.ratCoordMatrix u = eichlerMap J x y (toAdele 2⁻¹ * star y ⬝ᵥ J *ᵥ y) :=
    V.toRatCoords.surjective.exists.mp (New.exists_unitary_eq_eichlerMap herm h_iso h_orth half)
  refine ⟨u, ?_, hu⟩
  -- `u - 1 = x (y* J) - (y + ς x) (x* J)`. Its entry `(i, l)` needs `x i ≠ 0` and `y (σ l) ≠ 0`, or
  -- `(y + ς x) i ≠ 0` and `x (σ l) ≠ 0`; either forces `grade i > grade l`.
  have h_sub (ς : 𝔸 E) : eichlerMap J x y ς - 1 =
      vecMulVec x (star y ᵥ* J) - vecMulVec (y + ς • x) (star x ᵥ* J) := by
    rw [eichlerMap]
    abel
  rw [Y.mem_unipotent, hu, h_sub, HasDegreeGe]
  intro i l h_grade
  have dual_grade : Y.gradeOf (Y.stringReversal l) = -Y.gradeOf l := Y.gradeOf_stringReversal l
  have first_term : x i * (star y ᵥ* J) l = 0 := by
    by_cases hi : Y.gradeOf i ≤ 0 ⊔ k
    · rw [hx i hi, zero_mul]
    · rw [h_vecMul, Pi.star_apply, hy _ (by omega), star_zero, zero_mul, mul_zero]
  have second_term (ς : 𝔸 E) : (y + ς • x) i * (star x ᵥ* J) l = 0 := by
    by_cases hl : Y.gradeOf (Y.stringReversal l) ≤ 0 ⊔ k
    · rw [h_vecMul, Pi.star_apply, hx _ hl, star_zero, zero_mul, mul_zero]
    · rw [Pi.add_apply, Pi.smul_apply, hy i (by omega), hx i (by omega), smul_zero, add_zero,
        zero_mul]
  rw [Matrix.sub_apply, vecMulVec_apply, vecMulVec_apply, first_term, second_term, sub_zero]

/-- The measure on the Bessel (Fourier–Jacobi) subgroup B of Y that computes integrals over the
quotient of B by its rational points: Haar measure times a chosen cutoff. -/
noncomputable abbrev besselMeasure : Measure Y.besselGroup :=
  (Y.ratBessel.subgroupOf Y.besselGroup).quotMeasure haar

/-- The measure `New.Grading.besselMeasure` is finite, since the rational points are cocompact in
`B`. -/
instance isFiniteMeasure_besselMeasure : IsFiniteMeasure Y.besselMeasure :=
  isFiniteMeasure_quotMeasure_of_cocompact _ Y.isCocompact_ratBessel

/-- The left Haar measure of the adelic Bessel group `B` is right invariant, that is, `B` is
unimodular, since its rational points have finite covolume. -/
instance isMulRightInvariant_haar_besselGroup : IsMulRightInvariant (G := Y.besselGroup) haar :=
  isMulRightInvariant_of_finite_covolume Y.isFiniteMeasure_besselMeasure

/-- The row of `n` over which the integral over the Bessel group is averaged: at `(j, x)` it is
`Y.genericConst` times the entry of `n - 1`, in rational coordinates, in the row of the grade-1
index `v j` and the column of the basis vector `x` of `X`. -/
private noncomputable def besselRow {q : Type*} (v : q ↪ {l : ι // Y.gradeOf l = 1}) (n : G E ε)
    (p : q × X) : 𝔸 E :=
  ↑Y.genericConst * (V.ratCoordMatrix n - 1) (v p.fst) (Y.indexEquiv (.inl p.snd))

omit [Fintype X] in
/-- On the unipotent group the row adds: the row of `n * m` is the row of `n` plus that of `m`.
The cross term `(n - 1) (m - 1)` raises grades by at least `2`, while the row has entries from
grade `0` to grade `1`. -/
private lemma besselRow_mul_of_mem_unipotent {q : Type*} (v : q ↪ {l : ι // Y.gradeOf l = 1})
    {n m : G E ε} (hn : n ∈ Y.unipotent) (hm : m ∈ Y.unipotent) :
    Y.besselRow v (n * m) = Y.besselRow v n + Y.besselRow v m := by
  funext p
  have cross : HasDegreeGe Y.gradeOf Y.gradeOf (1 + 1)
      ((V.ratCoordMatrix n - 1) * (V.ratCoordMatrix m - 1)) :=
    (Y.mem_unipotent.mp hn).mul (Y.mem_unipotent.mp hm) le_rfl
  have h_expand : V.ratCoordMatrix (n * m) - 1 = (V.ratCoordMatrix n - 1) +
      (V.ratCoordMatrix m - 1) + (V.ratCoordMatrix n - 1) * (V.ratCoordMatrix m - 1) := by
    rw [map_mul]
    noncomm_ring
  have h_grade : Y.gradeOf (v p.fst) < Y.gradeOf (Y.indexEquiv (.inl p.snd)) + (1 + 1) := by
    simp [(v p.fst).property]
  have h_cross_entry : ((V.ratCoordMatrix n - 1) * (V.ratCoordMatrix m - 1))
      (v p.fst) (Y.indexEquiv (.inl p.snd)) = 0 := cross _ _ h_grade
  simp only [besselRow, h_expand, Matrix.add_apply, h_cross_entry, add_zero, mul_add, Pi.add_apply]

/-- The Eichler map of `x`, the indicator of the grade-1 indices, and of `y`, which on each basis
vector `x'` of `X` is `Y.genericConst⁻¹` times the sum of the conjugates `b̄ (j, x')` and vanishes
on the string, has row `b`, whatever its last argument `ς`. -/
private lemma besselRow_eq_of_ratCoordMatrix_eq_eichlerMap {q : Type*} [Fintype q]
    (v : q ↪ {l : ι // Y.gradeOf l = 1}) (b : q × X → 𝔸 E) (ς : 𝔸 E) {u : G E ε}
    (hu : V.ratCoordMatrix u = eichlerMap (V.J.map toAdele) (Pi.single 1 1 ∘ Y.gradeOf)
      (fun l : ι ↦ ∑ k : q × X,
        (if l = Y.indexEquiv (.inl k.snd) then ↑(Y.genericConst : E)⁻¹ else 0) * star (b k)) ς) :
    Y.besselRow v u = b := by
  funext ⟨j, x'⟩
  -- There is at most one index of grade `1`, as the grades `s - 1 - 2 i` of the string differ.
  have string_grade_inj (a₁ : Fin s) (h₁ : (s : ℤ) - 1 - 2 * (a₁ : ℕ) = 1) (a₂ : Fin s)
      (h₂ : (s : ℤ) - 1 - 2 * (a₂ : ℕ) = 1) : a₁ = a₂ := Fin.ext (by omega)
  have grade_one_subsingleton : Subsingleton {l : ι // Y.gradeOf l = 1} := by
    constructor
    simpa [reindex_equiv Y.indexEquiv] using string_grade_inj
  have q_subsingleton : Subsingleton q := v.injective.subsingleton
  set x : ι → 𝔸 E := Pi.single 1 1 ∘ Y.gradeOf
  set y : ι → 𝔸 E := fun l ↦ ∑ k : q × X,
    (if l = Y.indexEquiv (.inl k.snd) then ↑(Y.genericConst : E)⁻¹ else 0) * star (b k)
  -- The row at `(j, x')` is `Y.genericConst` times
  -- `x (v j) (ȳ J) x' - (y + ς x) (v j) (x̄ J) x'`, where:
  have h_x : x (v j) = 1 := by simp [x, (v j).property]
  have h_xJ : (star x ᵥ* V.J.map toAdele) (Y.indexEquiv (.inl x')) = 0 := by
    simp [x, Y.vecMul_J_apply, stringReversal]
  have h_yJ : (star y ᵥ* V.J.map toAdele) (Y.indexEquiv (.inl x')) = ↑(Y.genericConst : E)⁻¹ * b
    (j, x') := by
    simp [y, Y.vecMul_J_apply, stringReversal, gradedGram, Y.genericConst.property, sum_prod_type,
      sum_subsingleton _ j]
  simp [besselRow, hu, eichlerMap, vecMulVec_apply, h_x, h_xJ, h_yJ, ← mul_assoc, ← map_mul,
    Y.genericConst.property]

/-- Eichler maps translate the row. There is a continuous family `u b` of elements of the unipotent
group, indexed by the row vectors `b`, such that the row of `n * u b` is `b` plus the row of `n`
for every unipotent `n`; `u b` is the Eichler map of
`New.Grading.besselRow_eq_of_ratCoordMatrix_eq_eichlerMap`. -/
private lemma exists_continuous_unipotent_besselRow_mul {q : Type*} [Fintype q]
    (v : q ↪ {l : ι // Y.gradeOf l = 1}) :
    ∃ u : (q × X → 𝔸 E) → G E ε, Continuous u ∧ (∀ b : q × X → 𝔸 E, u b ∈ Y.unipotent) ∧
      ∀ n : G E ε, n ∈ Y.unipotent → ∀ b : q × X → 𝔸 E,
        Y.besselRow v (n * u b) = b + Y.besselRow v n := by
  -- `x` is the indicator of grade `1`, and `y b` lives on `X`, in grade `0`.
  let J : Matrix ι ι (𝔸 E) := V.J.map toAdele
  let x : ι → 𝔸 E := Pi.single 1 1 ∘ Y.gradeOf
  let y (b : q × X → 𝔸 E) (l : ι) : 𝔸 E := ∑ k : q × X,
    (if l = Y.indexEquiv (.inl k.snd) then ↑(Y.genericConst : E)⁻¹ else 0) * star (b k)
  have x_supp (p : ι) (hp : Y.gradeOf p ≤ 0 ⊔ 0) : x p = 0 :=
    Pi.single_eq_of_ne (by omega : Y.gradeOf p ≠ 1) 1
  have y_supp (b : q × X → 𝔸 E) (l : ι) (hl : Y.gradeOf l ≠ -0) : y b l = 0 := by
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    have l_ne : l ≠ Y.indexEquiv (.inl k.snd) := by
      rintro rfl
      exact hl (Y.gradeOf_inl k.snd)
    rw [ite_eq_right l_ne, zero_mul]
  have exists_u (b : q × X → 𝔸 E) : ∃ u ∈ Y.unipotent,
      V.ratCoordMatrix u = eichlerMap J x (y b) (toAdele 2⁻¹ * star (y b) ⬝ᵥ J *ᵥ y b) :=
    Y.exists_ratCoordMatrix_eq_eichlerMap x (y b) 0 x_supp (y_supp b)
  choose u u_mem u_mat using exists_u
  have u_cont : Continuous u :=
    V.isEmbedding_ratCoordMatrix.continuous_iff.mpr
      ((continuous_congr u_mat).mpr (by fun_prop [eichlerMap]))
  refine ⟨u, u_cont, u_mem, fun n hn b ↦ ?_⟩
  have h_add : Y.besselRow v (n * u b) = Y.besselRow v n + Y.besselRow v (u b) :=
    Y.besselRow_mul_of_mem_unipotent v hn (u_mem b)
  have row_u : Y.besselRow v (u b) = b :=
    Y.besselRow_eq_of_ratCoordMatrix_eq_eichlerMap v b _ (u_mat b)
  rw [h_add, row_u, add_comm]

/-- Haar measure on the preimage `S` of the rational points of `U(X)` under a homomorphism `pr`
from the Bessel group is right invariant, when `S` is closed and `pr` keeps rational points
rational: the rational points of the Bessel group then lie in `S` and are cocompact in it. -/
private lemma isMulRightInvariant_haar_comap_Gamma {pr : Y.besselGroup →* G E (1 : X → ℤˣ)}
    [S_closed : IsClosed ((stdSpace E X).Γ.comap pr).carrier]
    (pr_rat : ∀ r : Y.besselGroup, (r : G E ε) ∈ Y.ratBessel → pr r ∈ (stdSpace E X).Γ) :
    (haar : Measure ((stdSpace E X).Γ.comap pr)).IsMulRightInvariant := by
  obtain ⟨C, hC, cover⟩ : ∃ C : Set Y.besselGroup, IsCompact C ∧
      ∀ g : Y.besselGroup, ∃ γ ∈ Y.ratBessel.subgroupOf Y.besselGroup, γ * g ∈ C :=
    Y.isCocompact_ratBessel
  refine isMulRightInvariant_of_finite_covolume
    (isFiniteMeasure_quotMeasure_of_cocompact haar
      (Γ := (Y.ratBessel.subgroupOf Y.besselGroup).subgroupOf ((stdSpace E X).Γ.comap pr))
      ⟨_, hC.preimage_val S_closed, fun g ↦ ?_⟩)
  -- A rational `γ` with `γ * g ∈ C` lies in `S`, since `pr γ` is rational.
  obtain ⟨γ, γ_rat, hγ⟩ := cover g
  exact ⟨⟨γ, pr_rat γ γ_rat⟩, γ_rat, hγ⟩

omit [DecidableEq X] in
/-- A continuous function `F` on the adelic vectors that is periodic under the rational vectors
differs from its mean by a function of integral `0` modulo the rational vectors, also after a
translation by any `c`. -/
private lemma integral_add_sub_quotMean_eq_zero {q : Type*} [Fintype q] {F : (q × X → 𝔸 E) → ℂ}
    (hF : IsContPeriodic (ratVectors E (q × X)) F) (c : q × X → 𝔸 E) :
    ∫ b : q × X → 𝔸 E, F (b + c) - quotMean (ratVectors E (q × X)) F
      ∂(ratVectors E (q × X)).quotMeasure = 0 := by
  -- The translate of `F` by `c` is periodic with the same mean.
  have periodic : IsContPeriodic (ratVectors E (q × X)) (fun b ↦ F (b + c)) :=
    hF.imp (by fun_prop) (by simp +contextual [add_assoc])
  rw [← quotMean_translate hF, ← average_quotMeasure_eq_quotMean _ volume periodic,
    integral_sub_average]

/-- Integration over `B = Y.besselGroup` modulo its rational points reduces to `U(X)`. Let `v`
embed `q` into the basis indices of grade `1` (there is at most one, so `q` has at most one
element), and let `row n` be the adelic vector with entry `Y.genericConst` times `(n - 1) (v j, x)`
at `(j, x)`, for `n` in rational coordinates and `x` a basis vector of `X`. There is one constant
`κ` such that `∫ φ = κ * ∫ M` for all `φ`, `f`, `M` with
(a) `φ : B → ℂ` continuous and left invariant under the rational points `Y.ratBessel` of `B`;
(b) `φ (n * a) = f a (row n)` for `n` unipotent and `a` in `U(X)`;
(c) each `f a` continuous and periodic under the rational vectors, with mean `M a` over the
adelic vectors modulo the rational ones;
(d) `M` continuous and left invariant under the rational points of `U(X)`. -/
lemma integral_besselMeasure_eq_of_mean {q : Type*} [Fintype q]
    (v : q ↪ {l : ι // Y.gradeOf l = 1}) :
    let row (n : G E ε) (p : q × X) : 𝔸 E :=
      ↑Y.genericConst * (V.ratCoordMatrix n - 1) (v p.fst) (Y.indexEquiv (.inl p.snd))
    ∃ κ : ℂ, ∀ {φ : Y.besselGroup → ℂ} {f : G E (1 : X → ℤˣ) → (q × X → 𝔸 E) → ℂ}
      {M : G E (1 : X → ℤˣ) → ℂ},
      (φ_inv : (Y.ratBessel.subgroupOf Y.besselGroup).FixesLeft φ) → (φ_cont : Continuous φ) →
      (φ_eq : ∀ (n : G E ε) (hn : n ∈ Y.unipotent) (a : G E (1 : X → ℤˣ)),
        φ (⟨n, Y.unipotent_le_besselGroup hn⟩ * ⟨Y.inclX a, Y.inclX_mem_besselGroup a⟩) =
          f a (row n)) →
      (f_mean : ∀ a : G E (1 : X → ℤˣ), IsContPeriodic (ratVectors E (q × X)) (f a) ∧
        quotMean (ratVectors E (q × X)) (f a) = M a) →
      (M_cont : Continuous M) → (M_inv : (stdSpace E X).Γ.FixesLeft M) →
      ∫ r : Y.besselGroup, φ r ∂Y.besselMeasure =
        κ * ∫ a : G E (1 : X → ℤˣ), M a ∂(stdSpace E X).quotMeasure := by
  -- Let `pr : Y.besselGroup → U(X)` be the projection. Averaging `φ - M ∘ pr` over the Eichler maps
  -- `u b` gives 0, so its integral for `Y.besselMeasure` vanishes; and `M ∘ pr` integrates to a
  -- multiple of `∫ M`.
  intro row
  obtain ⟨pr, pr_cont, unip_part, pr_section, mem_unip, pr_rat⟩ :
      ∃ pr : Y.besselGroup →* G E (1 : X → ℤˣ), Continuous pr ∧
        (∀ r : Y.besselGroup, (r : G E ε) * (Y.inclX (pr r))⁻¹ ∈ Y.unipotent) ∧
        (∀ a : G E (1 : X → ℤˣ), pr ⟨Y.inclX a, Y.inclX_mem_besselGroup a⟩ = a) ∧
        (∀ r : Y.besselGroup, (r : G E ε) ∈ Y.unipotent ↔ pr r = 1) ∧
        ∀ r : Y.besselGroup, (r : G E ε) ∈ Y.ratBessel → pr r ∈ (stdSpace E X).Γ :=
    Y.exists_besselGroup_proj
  obtain ⟨u, u_cont, u_mem, row_mul⟩ : ∃ u : (q × X → 𝔸 E) → G E ε, Continuous u ∧
      (∀ b : q × X → 𝔸 E, u b ∈ Y.unipotent) ∧
      ∀ n : G E ε, n ∈ Y.unipotent → ∀ b : q × X → 𝔸 E, row (n * u b) = b + row n :=
    Y.exists_continuous_unipotent_besselRow_mul v
  let S : Subgroup Y.besselGroup := (stdSpace E X).Γ.comap pr
  have S_closed : IsClosed S.carrier := isClosed_of_discreteTopology.preimage pr_cont
  have unimodular : (haar : Measure S).IsMulRightInvariant :=
    Y.isMulRightInvariant_haar_comap_Gamma pr_rat
  -- `∫ M ∘ pr = κ • ∫ M`, so it remains to see `∫ φ = ∫ M ∘ pr`.
  obtain ⟨κ, push⟩ : ∃ κ : ℝ, ∀ F : G E (1 : X → ℤˣ) → ℂ, Measurable F →
      (stdSpace E X).Γ.FixesLeft F →
      ∫ r : Y.besselGroup, F (pr r) ∂Y.besselMeasure = κ • ∫ a, F a ∂(stdSpace E X).quotMeasure :=
    exists_integral_comp_quotMeasure_eq_smul (V := ℂ) (Γ := (stdSpace E X).Γ)
      (Y.ratBessel.subgroupOf Y.besselGroup) volume haar
      pr_cont (fun a ↦ ⟨⟨Y.inclX a, Y.inclX_mem_besselGroup a⟩, pr_section a⟩) pr_rat
  refine ⟨κ, fun {φ f M} φ_inv φ_cont φ_eq f_mean M_cont M_inv ↦
    .trans ?_ (push M M_cont.measurable M_inv)⟩
  have M_comp_pr_inv : (Y.ratBessel.subgroupOf Y.besselGroup).FixesLeft (fun r ↦ M (pr r)) := by
    intro γ hγ r
    show M (pr (γ * r)) = M (pr r)
    rw [map_mul, M_inv _ (pr_rat γ hγ)]
  rw [← sub_eq_zero, ← integral_sub (integrable_of_isCocompact Y.isCocompact_ratBessel φ_cont φ_inv)
    (integrable_of_isCocompact Y.isCocompact_ratBessel (by fun_prop) M_comp_pr_inv)]
  -- At `r`, average over the elements `j r b = u b * (r * (Y.inclX (pr r))⁻¹)⁻¹` of `S`. Right
  -- translation keeps the Haar measure of `S` (factor 1), while the average is 0 (factor 0); as the
  -- factors differ, the integral vanishes (`integral_quotMeasure_eq_zero_of_mean`).
  let j₀ (r : Y.besselGroup) (b : q × X → 𝔸 E) : Y.besselGroup :=
    ⟨u b, Y.unipotent_le_besselGroup (u_mem b)⟩ * ⟨_, Y.unipotent_le_besselGroup (unip_part r)⟩⁻¹
  have pr_j₀ (r : Y.besselGroup) (b : q × X → 𝔸 E) : pr (j₀ r b) = 1 := by
    have pr_u : pr ⟨u b, Y.unipotent_le_besselGroup (u_mem b)⟩ = 1 := (mem_unip _).mp (u_mem b)
    have pr_unip : pr ⟨_, Y.unipotent_le_besselGroup (unip_part r)⟩ = 1 :=
      (mem_unip _).mp (unip_part r)
    simp only [j₀, map_mul, map_inv, pr_u, pr_unip, inv_one, mul_one]
  have j_mem (r : Y.besselGroup) (b : q × X → 𝔸 E) : j₀ r b ∈ S := by
    show pr (j₀ r b) ∈ (stdSpace E X).Γ
    rw [pr_j₀ r b]
    exact one_mem _
  let j (r : Y.besselGroup) (b : q × X → 𝔸 E) : S := ⟨j₀ r b, j_mem r b⟩
  have diff_inv : (Y.ratBessel.subgroupOf Y.besselGroup).FixesLeft (fun r ↦ φ r - M (pr r)) :=
    fun γ hγ r ↦ congrArg₂ HSub.hSub (φ_inv γ hγ r) (M_comp_pr_inv γ hγ r)
  have translate_one (r : Y.besselGroup) (b : q × X → 𝔸 E) :
      (haar : Measure S).map (· * j r b) = (1 : NNReal) • haar := by
    rw [one_smul]
    exact unimodular.map_mul_right_eq_self (j r b)
  have j_meas (r : Y.besselGroup) : Measurable (j r) := by fun_prop
  refine integral_quotMeasure_eq_zero_of_mean _ diff_inv (by fun_prop)
    (fun γ hγ ↦ mem_comap.mpr (pr_rat γ hγ)) (ratVectors E (q × X)).quotMeasure j j_meas 1
    translate_one zero_ne_one fun g r ↦ ?_
  -- Write `g = Y.inclX (pr g) * n` with `pr g` rational and `n` unipotent.
  let n : G E ε := (Y.inclX (pr g))⁻¹ * g
  have n_mem : n ∈ Y.unipotent := by simpa [n] using inv_mem (unip_part g⁻¹)
  -- Here `g * (j r b * r) = Y.inclX (pr g) * (n * u b * Y.inclX (pr r))`.
  have value (b : q × X → 𝔸 E) : φ (g * (j r b * r)) = f (pr r) (b + row n) := by
    have h_factor : (g : Y.besselGroup) * (j r b * r) =
        ⟨Y.inclX (pr g), Y.inclX_mem_besselGroup (pr g)⟩ *
          (⟨n * u b, Y.unipotent_le_besselGroup (mul_mem n_mem (u_mem b))⟩ *
            ⟨Y.inclX (pr r), Y.inclX_mem_besselGroup (pr r)⟩) := by
      ext1
      simp [j, j₀, n, mul_assoc]
    rw [h_factor, φ_inv ⟨Y.inclX (pr g), Y.inclX_mem_besselGroup (pr g)⟩
        (Y.inclX_mem_ratBessel g.property),
      φ_eq _ (mul_mem n_mem (u_mem b))]
    exact congrArg (f (pr r)) (row_mul n n_mem b)
  have pr_value (b : q × X → 𝔸 E) : M (pr (g * (j r b * r))) = M (pr r) := by
    simp only [map_mul, j, pr_j₀, one_mul, M_inv _ g.property]
  suffices ∫ b, f (pr r) (b + row n) - M (pr r) ∂(ratVectors E (q × X)).quotMeasure = 0 by
    simpa only [coe_mul, mul_assoc, value, pr_value, zero_smul, zero_mul]
  obtain ⟨f_periodic, f_quotMean⟩ := f_mean (pr r)
  rw [← f_quotMean]
  exact integral_add_sub_quotMean_eq_zero f_periodic (row n)

end New.Grading

/-!
## Rational maps surviving unipotent twists

`New.Grading.gradeOf` is the weight of a basis vector and `New.Grading.stringReversal` the dual
index. `New.HasDegreeGe w' w d x` says that `x` raises weights by at least `d`.
`New.Space.formAdjoint` is the adjoint `†`. `New.Grading.stringMap` is the standard map `T` of
degree `-1`. `New.Grading.AgreesWithStringMap` is agreement with `T` in negative degree on the
vectors of positive weight.
-/

section SurvivingOrbit

namespace New.Grading

open Matrix WeilData Finset Space Finite

variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']
  {s : ℕ} {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {N : E} {V : Space E ι ε} {V' : Space E ι' ε'}
  (Y : Grading V N X s) (Y' : Grading V' N X' (s - 1)) [WeilData E]

/-- The term at the rational map `w` survives the unipotent twists, for target weights `D`. Let `T`
be `Y.stringMap Y'`, and take any `u` in `Y.unipotent` such that `u - 1` has degree at least `2` and
`w (u - 1)` has degree at least `1` (weights `D` on the target), with `u` written in rational
coordinates. Then `New.Space.homBicharacter` takes the same value at `(T u, T)` and at
`(w u, w)`. -/
abbrev Survives (D : ι' → ℤ) (w : Matrix ι' ι (𝔸 E)) : Prop :=
  ∀ u ∈ Y.unipotent,
    HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix u - 1) ∧
    HasDegreeGe D Y.gradeOf 1 (w * (V.ratCoordMatrix u - 1)) →
    V.homBicharacter V' (Y.stringMap Y' * V.ratCoordMatrix u) (Y.stringMap Y') =
      V.homBicharacter V' (w * V.ratCoordMatrix u) w

omit [Fintype X'] in
/-- Let `T` be `Y.stringMap Y'`, the rational map V → V' that kills `X` and the last string vector
and sends each other string vector to a multiple of the string vector of `V'` with the same number.
Suppose that `w` survives the unipotent twists for target weights `D` (`New.Grading.Survives`:
`homBicharacter` agrees at (T u, T) and (w u, w) for the relevant u in `Y.unipotent`). Then `T† T v`
and `w† w v` (with † the form adjoint) have the same coordinate `k`, provided that `v p = 0` unless
the weight of `p` is at least `1` and at least that of `k` plus `2` (`hv`); `(w v) p = 0` unless
`D p` is nonnegative and above the weight of `k` (`hwv`); and the entry of `w` in row `p` and the
column dual to `k` vanishes, or `v q = 0`, whenever `D p` plus the weight of `q` is at most `0`
(`hw_col`). -/
lemma formAdjoint_mul_self_mulVec_apply_eq_of_survives {w : Matrix ι' ι (𝔸 E)} {D : ι' → ℤ}
    (survives : Y.Survives Y' D w) (v : ι → 𝔸 E) (k : ι)
    (hv : ∀ p : ι, Y.gradeOf p < 1 ⊔ (2 + Y.gradeOf k) → v p = 0)
    (hwv : ∀ p : ι', D p ≤ Y.gradeOf k ⊔ -1 → (w *ᵥ v) p = 0)
    (hw_col : ∀ (p : ι') (q : ι), D p + Y.gradeOf q ≤ 0 → w p (Y.stringReversal k) = 0 ∨ v q = 0) :
    ((V.formAdjoint V' (Y.stringMap Y') * Y.stringMap Y') *ᵥ v) k =
      ((V.formAdjoint V' w * w) *ᵥ v) k := by
  -- Test with the Eichler map `u` of `v` and a multiple `x` of the basis vector dual to `k`: the
  -- phases of `u` at `Y.stringMap Y'` and at `w` agree, and `stdAddChar` is nondegenerate.
  refine sub_eq_zero.mp (eq_zero_of_forall_stdAddChar_eq_one fun t ↦ ?_)
  let x : ι → 𝔸 E :=
    Pi.single (Y.stringReversal k) (star (↑(j⁻¹ * V.J⁻¹ k (Y.stringReversal k)) * t))
  have v_supp (p : ι) (hp : Y.gradeOf p ≤ 0 ⊔ Y.gradeOf k) : v p = 0 := hv p (by omega)
  have x_supp (q : ι) (hq : Y.gradeOf q ≠ -Y.gradeOf k) : x q = 0 := by
    have q_ne : q ≠ Y.stringReversal k := by
      rintro rfl
      exact hq (Y.gradeOf_stringReversal k)
    exact Pi.single_eq_of_ne q_ne _
  obtain ⟨u, u_mem, u_mat⟩ : ∃ u ∈ Y.unipotent, V.ratCoordMatrix u =
      eichlerMap (V.J.map toAdele) v x (toAdele 2⁻¹ * star x ⬝ᵥ V.J.map toAdele *ᵥ x) :=
    Y.exists_ratCoordMatrix_eq_eichlerMap v x (Y.gradeOf k) v_supp x_supp
  -- `stdAddChar a` depends only on `a + star a` (`stdAddChar_inv_two_mul_add_star`); compare these
  -- sums.
  have phase (y : Matrix ι' ι (𝔸 E)) :
      V.homBicharacter V' (y * V.ratCoordMatrix u) y =
        stdAddChar E (toAdele j * star x ⬝ᵥ (yᴴ * V'.J.map toAdele * y) *ᵥ v) := by
    suffices h_sum : toAdele ((j : E) / 2) * (V.formAdjoint V' y * (y * V.ratCoordMatrix u)).trace +
          star (toAdele ((j : E) / 2) * (V.formAdjoint V' y * (y * V.ratCoordMatrix u)).trace) =
        toAdele (j : E) * star x ⬝ᵥ (yᴴ * V'.J.map toAdele * y) *ᵥ v +
          star (toAdele (j : E) * star x ⬝ᵥ (yᴴ * V'.J.map toAdele * y) *ᵥ v) by
      rw [homBicharacter_eq, ← stdAddChar_inv_two_mul_add_star,
        ← stdAddChar_inv_two_mul_add_star (toAdele j * star x ⬝ᵥ (yᴴ * V'.J.map toAdele * y) *ᵥ v)]
      exact congrArg (fun z ↦ (stdAddChar E (toAdele 2⁻¹ * z) : ℂ)) h_sum
    simp [u_mat, formAdjoint, ← dotProduct_mulVec, dotProduct_comm _ (_ ᵥ* _), ← Matrix.mul_assoc,
      mul_eq_one_symm V.map_J_inv_mul_map_J, (isHermitian_J _).eq, ← trace_conjTranspose,
      conjTranspose_nonsing_inv, trace_mul_comm _ (map _ _), Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mul_add, eichlerMap, mul_sub, mul_vecMulVec,
        star_dotProduct_mulVec_comm]
    -- The trace terms and the terms in `star x ⬝ᵥ J *ᵥ x` cancel; the pairings of `x` with `v`
    -- add up.
    have h_half : toAdele ((j : E) / 2) + toAdele ((j : E) / 2) = toAdele (j : E) := by
      rw [← map_add, add_halves]
    rw [neg_div, map_neg, ← h_half]
    ring
  have u_deg :
      HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix u - 1) ∧
      HasDegreeGe D Y.gradeOf 1 (w * (V.ratCoordMatrix u - 1)) := by
    -- The entries are terms in `v`, `x` and `w *ᵥ v` at weights that `hv`, `hwv` and `hw_col`
    -- exclude.
    simp [u_mat, Y.vecMul_J_apply, vecMulVec_apply, x, -single_vecMul, Pi.single_apply,
      Matrix.one_apply, sub_eq_zero, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mul_sub,
      Matrix.mul_add, HasDegreeGe, eichlerMap, mul_vecMulVec, mulVec_neg]
    grind [gradeOf_stringReversal, star_zero]
  have h_phase : V.homBicharacter V' (Y.stringMap Y' * V.ratCoordMatrix u) (Y.stringMap Y') =
      V.homBicharacter V' (w * V.ratCoordMatrix u) w :=
    survives u u_mem u_deg
  rw [phase, phase] at h_phase
  simpa [x, AddChar.map_sub_eq_div, div_eq_one, Circle.ext_iff, ← mul_assoc, ← map_mul,
    formAdjoint, Y.J_inv_eq_gradedGram, map_gradedGram_mul_apply, mulVec_apply_eq_sum, mul_sum,
    mul_comm t (toAdele _), j_ne_zero, Matrix.mul_assoc, mul_sub] using h_phase

omit [WeilData E] [Fintype X] in
/-- Let `k` be an index of `Y'` whose weight is at least `0` if `k` is on the string and at least
`1` otherwise; as the weight off the string is `0`, `k` is on the string. Write `T` for
`Y.stringMap Y'`. There is an index `a` of `Y` with (a) weight one more than `k`; (b) `T k a` a
unit; (c) for every `w` of type `AgreesWithStringMap` and every row `m` that vanishes in weights
above that of `k`, the product of `m` with column `a` of `w` is `m k * T k a`. -/
lemma exists_gradeOf_succ_isUnit_stringMap (k : ι')
    (hk : (if (Y'.indexEquiv.symm k).isRight then 0 else 1) ≤ Y'.gradeOf k) :
    ∃ a : ι,
      Y.gradeOf a = Y'.gradeOf k + 1 ∧
      IsUnit (Y.stringMap Y' k a) ∧
      ∀ {w : Matrix ι' ι (𝔸 E)}, Y.AgreesWithStringMap Y' w → ∀ m : ι' → 𝔸 E,
        (∀ l : ι', Y'.gradeOf l ≤ Y'.gradeOf k ∨ m l = 0) →
        m ⬝ᵥ (fun l : ι' ↦ w l a) = m k * Y.stringMap Y' k a := by
  -- `k` lies on the string: off it the weight is `0` and the hypothesis asks for weight `≥ 1`.
  obtain ⟨x' | k', rfl⟩ := Y'.indexEquiv.surjective k
  · simp at hk
  -- Take for `a` the index at the same position of the longer string.
  refine ⟨Y.indexEquiv (.inr ⟨k', by omega⟩), ?_, ?_, ?_⟩
  · simp
    omega
  · simp [stringMap] at hk ⊢
    grind [Y.N_ne_zero_and_star_eq]
  · -- Up to the weight of `k`, column `a` of `w` is that of `stringMap`, whose only entry is in
    -- row `k`.
    intro w hw m hm
    simp [reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv, stringMap, dotProduct]
      at hk hw hm ⊢
    grind [sum_eq_single k', sum_eq_zero]

omit [WeilData E] in
/-- Let `w` be of type `New.Grading.AgreesWithStringMap` and let `γ` lie in `Y.besselGroup`. Then
`δ w γ` is again of type `AgreesWithStringMap` exactly when `δ` lies in `Y'.besselGroup`. Here `δ`
and `γ` are taken in rational coordinates. -/
lemma agreesWithStringMap_mul_iff {w : Matrix ι' ι (𝔸 E)} {γ : G E ε} (hγ : γ ∈ Y.besselGroup)
    (hw : Y.AgreesWithStringMap Y' w) (δ : G E ε') :
    Y.AgreesWithStringMap Y' (V'.ratCoordMatrix δ * (w * V.ratCoordMatrix γ)) ↔ δ ∈
      Y'.besselGroup := by
  -- Write `δ * (w * γ) - stringMap = δ * (w - stringMap) * γ + (δ * stringMap * γ - stringMap)`,
  -- with `δ` and `γ` of degree `≥ 0`; the last term has degree `≥ 0` by
  -- `hasDegreeGe_zero_mul_stringMap_mul_sub`.
  have of_mem {δ : G E ε'} (hδ : δ ∈ Y'.besselGroup) :
      Y.AgreesWithStringMap Y' (V'.ratCoordMatrix δ * (w * V.ratCoordMatrix γ)) := by
    grind [→ hasDegreeGe_zero_of_mem_besselGroup, → hasDegreeGe_zero_mul_stringMap_mul_sub,
      Matrix.mul_apply, Matrix.sub_apply, HasDegreeGe, hasDegreeGe_neg_one_stringMap]
  have agrees : Y.AgreesWithStringMap Y' (w * V.ratCoordMatrix γ) := by
    simpa using of_mem (one_mem _)
  refine ⟨fun hδ ↦ Y'.mem_besselGroup_iff_sub_one.mpr fun b ↦ ?_, of_mem⟩
  -- Show that the entry `(b, k)` of `δ - 1` vanishes, by downward induction on the weight of `k`.
  refine int_weight_induction (fun l : ι' ↦ -Y'.gradeOf l) fun k ih hk hbk ↦ ?_
  obtain ⟨a, ha, unit, col⟩ := Y.exists_gradeOf_succ_isUnit_stringMap Y' k hk
  -- By `ih`, row `b` of `δ - 1` vanishes in the weights above that of `k`.
  have h_row : ∀ l : ι', Y'.gradeOf l ≤ Y'.gradeOf k ∨ (V'.ratCoordMatrix δ - 1) b l = 0 := by
    grind
  -- The entry `(b, a)` of `(δ - 1) * (w * γ)` is this entry times a unit (`col`, using `ih`), and
  -- it vanishes because `δ * (w * γ)` and `w * γ` both agree with `stringMap` there.
  rw [← unit.mul_left_eq_zero, ← col agrees _ h_row, ← Matrix.mul_apply', Matrix.sub_mul]
  show (V'.ratCoordMatrix δ * (w * V.ratCoordMatrix γ) -
      (1 : Matrix ι' ι' (𝔸 E)) * (w * V.ratCoordMatrix γ)) b a = 0
  simp (disch := grind) [hδ b a, agrees b a]

/-- Let `T = Y.stringMap Y'` be the map that kills `X` and the last string vector of `V` and sends
each other string vector to a multiple of the same-numbered string vector of `V'`. Suppose `w`
agrees with `T` at every entry `(b, a)` where `a` has positive grade and `b` has grade below that
of `a`. Suppose also that `w` survives the unipotent twists with target weights `Y'.gradeOf`
(`New.Grading.Survives`): for every `u` in `Y.unipotent` with `u - 1` of degree at least `2` and
`w (u - 1)` of degree at least `1`, `New.Space.homBicharacter` takes the same value at `(T u, T)`
and at `(w u, w)`. Then `w - T` has degree at least `0`, i.e. its `(b, a)` entry vanishes whenever
the grade of `b` (`Y'.gradeOf`) is less than the grade of `a` (`Y.gradeOf`). -/
lemma hasDegreeGe_of_survives {w : Matrix ι' ι (𝔸 E)} (hw : Y.AgreesWithStringMap Y' w)
    (survives : Y.Survives Y' Y'.gradeOf w) :
    HasDegreeGe Y'.gradeOf Y.gradeOf 0 (w - Y.stringMap Y') := by
  -- Every entry `(b, a)` of negative degree of `w - stringMap` vanishes, by induction on the weight
  -- of `b`.
  refine int_weight_induction Y'.gradeOf fun b ih a hab ↦ ?_
  rw [Matrix.sub_apply, sub_eq_zero]
  -- Suppose that the entry `(b, a)` of `w` differs from that of `stringMap`.
  by_cases h_eq : w b a = Y.stringMap Y' b a
  · exact h_eq
  -- By `hw` a bad entry has `gradeOf b < gradeOf a ≤ 0`, so the index dual to `b` has positive
  -- weight.
  have h_rev_pos : (if (Y'.indexEquiv.symm (Y'.stringReversal b)).isRight then 0 else 1) ≤
      Y'.gradeOf (Y'.stringReversal b) := by
    grind [gradeOf_stringReversal]
  obtain ⟨i, hi, unit, col⟩ :=
    Y.exists_gradeOf_succ_isUnit_stringMap Y' (Y'.stringReversal b) h_rev_pos
  -- On the basis vector `i`, the coordinate dual to `a` of `w† w` is this entry of `w†` times a
  -- unit (`col`, using `ih`); likewise for `stringMap`.
  have adj_eq :
      V.formAdjoint V' (Y.stringMap Y') (Y.stringReversal a) (Y'.stringReversal b) =
        V.formAdjoint V' w (Y.stringReversal a) (Y'.stringReversal b) := by
    have h_entry :
        ((V.formAdjoint V' (Y.stringMap Y') * Y.stringMap Y') *ᵥ Pi.single i 1)
            (Y.stringReversal a) =
          ((V.formAdjoint V' w * w) *ᵥ Pi.single i 1) (Y.stringReversal a) := by
      refine Y.formAdjoint_mul_self_mulVec_apply_eq_of_survives Y' survives (Pi.single i 1)
        (Y.stringReversal a) ?_ ?_ ?_
      · grind [gradeOf_stringReversal]
      · simp only [mulVec_single_one, Matrix.col_apply]
        grind [HasDegreeGe, gradeOf_stringReversal, hasDegreeGe_neg_one_stringMap]
      · grind [HasDegreeGe, gradeOf_stringReversal, Matrix.sub_apply, hasDegreeGe_neg_one_stringMap]
    simpa (disch := grind [Y.formAdjoint_apply Y', HasDegreeGe, gradeOf_stringReversal, star_zero,
      Matrix.sub_apply, hasDegreeGe_neg_one_stringMap]) [Matrix.mul_apply', col,
      unit.mul_left_inj] using h_entry
  -- By `formAdjoint_apply` this entry of the adjoint determines the entry `(b, a)`.
  rw [← V.formAdjoint_formAdjoint _ w, Y'.formAdjoint_apply Y, ← adj_eq, ← formAdjoint_apply,
    formAdjoint_formAdjoint]

/-- Let the map `x` over `E` survive the unipotent twists (target weights `0`). Then `x` is
injective on the span of the basis vectors of positive weight: its restriction to them has a left
inverse. -/
private lemma hasLeftInv_submatrix_of_survives {x : Matrix ι' ι E}
    (hx : Y.Survives Y' 0 (x.map toAdele)) :
    HasLeftInv (k := univ.filter fun a : ι ↦ 0 < Y.gradeOf a) (x.submatrix id (↑)) := by
  set A : Finset ι := univ.filter fun a : ι ↦ 0 < Y.gradeOf a with hA
  -- A kernel vector `u` vanishes, by induction on the weight of the coordinate.
  refine .of_ker_le_bot fun u hu ↦ funext (int_weight_induction (fun a : A ↦ Y.gradeOf a) ?_)
  -- Indices of positive weight lie on the string; let `a` be the last one there with `u a ≠ 0`.
  simp [A, reindex_equiv Y.indexEquiv]
  show ∀ (b : Fin s) (hb : 2 * ((b : ℕ) : ℤ) < (s : ℤ) - 1),
    (∀ (b' : Fin s) (hb' : 2 * ((b' : ℕ) : ℤ) < (s : ℤ) - 1), b < b' →
      u ⟨Y.indexEquiv (.inr b'), _⟩ = 0) → u ⟨Y.indexEquiv (.inr b), _⟩ = 0
  by_contra! ⟨a, a_pos, ih, u_ne⟩
  -- `v` is `u` extended by zero, as an adelic vector.
  let v : ι → 𝔸 E := toAdele ∘ Finsupp.indicator A (u ⟨·, ·⟩)
  have v_ker : x.map toAdele *ᵥ v = 0 := by
    simpa [v, A, funext_iff, mulVec_apply_eq_sum, ← map_mul, ← map_sum, sum_dite] using hu
  -- At the next index `k`, the shift `T† T` agrees on `v` with `x† x`, which kills `v`; but
  -- `(Y.shift *ᵥ v) k` is a nonzero multiple of `u a`.
  let k : ι := Y.indexEquiv (.inr ⟨a + 1, by omega⟩)
  have shift_eq :
      (Y.shift *ᵥ v) k = ((V.formAdjoint V' (x.map toAdele) * x.map toAdele) *ᵥ v) k := by
    -- The three conditions of `formAdjoint_mul_self_mulVec_apply_eq_of_survives`: `v` lives in the
    -- weights at or above that of `a`.
    obtain ⟨hv, hwv, hw_col⟩ : (∀ p : ι, Y.gradeOf p < 1 ⊔ (2 + Y.gradeOf k) → v p = 0) ∧
        (∀ p : ι', (0 : ι' → ℤ) p ≤ Y.gradeOf k ⊔ -1 → (x.map toAdele *ᵥ v) p = 0) ∧
        ∀ (p : ι') (q : ι), (0 : ι' → ℤ) p + Y.gradeOf q ≤ 0 →
          x.map toAdele p (Y.stringReversal k) = 0 ∨ v q = 0 := by
      rw [v_ker]
      simp [v, k, A, reindex_equiv Y.indexEquiv]
      grind
    obtain ⟨h_shift, -⟩ : V.formAdjoint V' (Y.stringMap Y') * Y.stringMap Y' = Y.shift ∧
        (Y'.genericConst = Y.genericConst → Y.stringMap Y' * V.formAdjoint V' (Y.stringMap Y') =
          Y'.shift) :=
      Y.formAdjoint_stringMap_mul_stringMap (Y' := Y')
    rw [← h_shift, Y.formAdjoint_mul_self_mulVec_apply_eq_of_survives Y' hx v k hv hwv hw_col]
  rw [← mulVec_mulVec, v_ker, mulVec_zero] at shift_eq
  simp [shift, v, k, A, mulVec_apply_eq_sum, reindex_equiv Y.indexEquiv, -mul_dite, ← map_mul,
    ← map_sum, Fin.val_inj, a_pos] at shift_eq
  -- The factor `c`, `-N c` or `-N c²` of the shift, with `c = Y.genericConst`, is nonzero, and so
  -- is `u a`.
  split_ifs at shift_eq <;> simp [Y.N_ne_zero_and_star_eq.1, Y.genericConst.prop.1,
    u_ne] at shift_eq

/-- Let `w` be a rational map `V → V'`, meaning an adelic matrix coming from a matrix over `E`, that
survives the unipotent twists with target weights `0` (`New.Grading.Survives`). That is, for every
`u` in `Y.unipotent` with `u - 1` of degree at least `2` and `w (u - 1)` of degree at least `1`,
`New.Space.homBicharacter` takes the same value at `(T u, T)` and at `(w u, w)`. Here
`T = Y.stringMap Y'` is the rational map that kills `X` and the last string vector of `V` and sends
each other string vector to a multiple of the same-numbered string vector of `V'`. Then some
rational unitary `δ` of `V'` makes `δ w` (in rational coordinates) agree with `T` at every entry
`(b, a)` where `a` has positive grade and `b` has grade below that of `a`
(`New.Grading.AgreesWithStringMap`). -/
lemma exists_agreesWithStringMap (w : Matrix ι' ι (𝔸 E)) (hw : w ∈ ratMatrices E ι' ι)
    (survives : Y.Survives Y' 0 w) :
    ∃ δ ∈ V'.Γ, Y.AgreesWithStringMap Y' (V'.ratCoordMatrix δ * w) := by
  -- On the basis vectors of positive weight, `w` and `stringMap` are injective and have the same
  -- Gram matrix; Witt's theorem moves one to the other.
  obtain ⟨w, rfl⟩ := hw
  let A : Finset ι := univ.filter fun a : ι ↦ 0 < Y.gradeOf a
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Matrix ι' ι E, T₀.map toAdele = Y.stringMap Y' := ⟨_, rfl⟩
  let incl : A → ι := (↑)
  -- The Gram matrix of `w` is `V.J * (w† w)`, so `formAdjoint_mul_self_mulVec_apply_eq_of_survives`
  -- compares the entries.
  have h_gram : (w.submatrix id incl)ᴴ * V'.J * w.submatrix id incl =
      (T₀.submatrix id incl)ᴴ * V'.J * T₀.submatrix id incl := by
    refine ext fun k i ↦ toAdele.injective ?_
    have gram_adj (y : Matrix ι' ι (𝔸 E)) :
        yᴴ * V'.J.map toAdele * y = V.J.map toAdele * (V.formAdjoint V' y * y) := by
      simp [formAdjoint, ← Matrix.mul_assoc, mul_eq_one_symm V.map_J_inv_mul_map_J]
    have h_gram_entry : ((Y.stringMap Y')ᴴ * V'.J.map toAdele * Y.stringMap Y') k i =
        ((w.map toAdele)ᴴ * V'.J.map toAdele * w.map toAdele) k i := by
      rw [gram_adj, gram_adj]
      have h_adj :
          ((V.formAdjoint V' (Y.stringMap Y') * Y.stringMap Y') *ᵥ Pi.single i 1)
              (Y.stringReversal k) =
            ((V.formAdjoint V' (w.map toAdele) * w.map toAdele) *ᵥ Pi.single i 1)
              (Y.stringReversal k) := by
        -- Both `i` and `k` have positive weight, and the target weights are `0`.
        refine Y.formAdjoint_mul_self_mulVec_apply_eq_of_survives Y' survives (Pi.single i 1)
          (Y.stringReversal k) ?_ ?_ ?_
        · grind [gradeOf_stringReversal]
        · simp only [Pi.zero_apply]
          grind [gradeOf_stringReversal]
        · simp only [Pi.zero_apply]
          grind
      -- Row `k` of `V.J * M` is a multiple of the row of `M` dual to `k`.
      simpa [Y.gram_eq, map_gradedGram_mul_apply] using
        congrArg (fun z ↦ V.J.map toAdele k (Y.stringReversal k) * z) h_adj
    simpa [← hT₀, mul_apply, incl] using h_gram_entry.symm
  -- `T₀` survives trivially, as the two phases are the same.
  have hT₀_survives : Y.Survives Y' 0 (T₀.map toAdele) := fun u _ _ ↦ by rw [hT₀]
  obtain ⟨g, hg⟩ : ∃ g : U V'.J,
      (g : Matrix ι' ι' E) * w.submatrix id incl = T₀.submatrix id incl :=
    V'.witt (Y.hasLeftInv_submatrix_of_survives Y' survives)
      (Y.hasLeftInv_submatrix_of_survives Y' hT₀_survives) h_gram
  refine ⟨V'.ratEmbed g, ⟨g, rfl⟩, fun b a a_pos _ ↦ ?_⟩
  have ha_mem : a ∈ A := by simpa [A] using a_pos
  have h_entry : toAdele (((g : Matrix ι' ι' E) * w.submatrix id incl) b ⟨a, ha_mem⟩) =
      toAdele (T₀.submatrix id incl b ⟨a, ha_mem⟩) := by rw [hg]
  simpa [mul_apply, ratCoordMatrix, ratEmbed, ← hT₀, incl, U.map] using h_entry

end New.Grading

end SurvivingOrbit

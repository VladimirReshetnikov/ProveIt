import Lib.Adelic.Reduction.MinkowskiTheorems
import Lib.Adelic.Unitary.WeakApproximation
import Lib.General.NumberTheory.SUnitsAndClassNumber

/-!
# Adelic reduction theory, Mahler's criterion and finite volume of the arithmetic quotient

This file develops reduction theory for `GL_n` over the adeles: every adelic frame `y` has a
rational basis `Y` such that `y⁻¹ Y` lies in one fixed compact set after its columns are scaled by
powers of `2` at the infinite places. For a hermitian space `V` (`New.Space`), a weighted Haar
measure on the adelic unitary group `G` computes integrals over `[G] = V.Γ \ G`.

## Main definitions and results

* `New.Core.exists_isCompact_profileBases`: one compact set `M` bounds a reduced basis at every `y`.
* `New.exists_isBoundedDualBasis`: Mahler's criterion for frames of forms that may vary. The
  criterion for the unitary group of one space is `New.Space.mahler_criterion` in
  `Lib.Adelic.Reduction.DefiniteClassSums`.
* `New.Space.quotMeasure`: for a space `V` with rational points `New.Space.Γ`, the measure
  `Subgroup.quotMeasure` on `G` for counting measure on `Γ`. It integrates `Γ`-invariant functions
  over `[G] = Γ \ G`.
* `New.Space.lintegral_encard_ne_top`: the count of rational `n × t` matrices is integrable over
  `V.Γ \ G` if `2 t < n`.
* `New.Space.isFiniteMeasure_quotMeasure`: finite volume, the case `t = 0`.

Notions from other files:
* `New.𝔸`: the ring `ℂ ^ f × 𝔸_f`, one copy of `ℂ` for each infinite place of `E` times the finite
  adeles. It is the adele ring of `E` when `E` is totally complex; `New.toAdele` embeds `E` in it.
* `New.ideleAbs`: the module (adelic absolute value) of an idele.
* `New.Core.twoAtInfinity`: the idele of `E` that is `2` at all infinite places and `1` at the
  finite places.
* `New.Core.profileBases M x y`: the `Y` in `GL_n(E)` with `y⁻¹ Y (D x)⁻¹ ∈ M`, where
  `D x = New.Core.dyadicDiag x` is diagonal with entries `twoAtInfinity E ^ x i`. The integer vector
  `x` is called the profile of such a basis.
* `New.Space`: a matrix `J` over `E` and a point `x` in `GL_n(𝔸)` with `xᴴ J x` equal to `diag s` at
  the infinite places, for signs `s`, and `1` at the finite places.

## Relation to the literature

Known results: reduction theory for adele groups (the compactness criterion of Mahler and Godement,
finite covolume) and Weil's convergence criterion. Finite volume is proved here only for unitary
groups over CM fields, by counting reduced bases, and Weil's criterion only when twice the number of
vectors is below the rank. The adelic Minkowski theorems come from
`Lib.Adelic.Reduction.MinkowskiTheorems`, with crude explicit constants. Source: A. Borel, Some
finiteness properties of adele groups over number fields, Publ. IHES 16 (1963), 4.5-5.8; A. Weil,
Sur la formule de Siegel dans la théorie des groupes classiques, Acta Math. 113 (1965), Prop. 8;
Bombieri-Vaaler, On Siegel's lemma, Invent. Math. 73 (1983).

For the adelic points of unitary groups and their Haar measures, see
`Lib.Adelic.Unitary.WeakApproximation`.
-/

/-! ## Reduced rational bases in a compact set of adelic matrices -/

section CompactBases

open Matrix Set

namespace New.Core

variable {E : Type*} [Field E] [CMType E] {n : Type*} [Fintype n] [DecidableEq n]

/-- Minkowski's first theorem in rank one. Let `a` be an idele such that `a` times `2 ^ N` at the
infinite places has adelic absolute value greater than `(2 * rootDiscr E) ^ f`, with `rootDiscr E`
the root discriminant of `E`, where `f = numInfPlaces E` is the number of infinite places. Then this
product times some `b` in the closed unit box (absolute value at most `1` at the infinite places, in
the ring `Ô E` of integral finite adeles at the finite places) is a non-zero element `ξ` of `E`. -/
lemma exists_mul_twoAtInfinity_pow_mul_eq_toAdele {a : (𝔸 E)ˣ} {N : ℕ}
    (h_lt : (2 * NumberField.rootDiscr E) ^ numInfPlaces E <
      ideleAbs a * (2 ^ (2 * numInfPlaces E)) ^ N) :
    ∃ ξ : E, ξ ≠ 0 ∧ ∃ b ∈ (Metric.closedBall 0 1 ×ˢ Ô E : Set (𝔸 E)),
      a.val * (twoAtInfinity E ^ N).val * b = toAdele ξ := by
  let y : GL (Fin 1) (𝔸 E) := .scalar (Fin 1) a * dyadicDiag fun _ ↦ (N : ℤ)
  obtain ⟨ξ, h_box, hξ⟩ :=
    exists_ne_zero_inv_mulVec_mem y (by simpa [y, ideleAbs_det_dyadicDiag] using h_lt)
  obtain ⟨h_ball, h_integral⟩ := h_box 0
  refine ⟨ξ 0, by simpa [funext_iff] using hξ, (y⁻¹.val *ᵥ toAdele ∘ ξ) 0,
    ⟨Metric.ball_subset_closedBall h_ball, h_integral⟩, ?_⟩
  simp [y, dyadicDiag, mul_assoc]

open Pointwise in
/-- For a compact set `M` of adelic `n × n` matrices and `c > 0`, the invertible matrices `A` that
lie in `M` and whose determinant has adelic absolute value `ideleAbs A.det` at least `c` form a
compact subset of `GL n (𝔸 E)`, where `𝔸 E` is the ring of adeles of `E`. -/
lemma isCompact_setOf_le_ideleAbs_det {M : Set (Matrix n n (𝔸 E))} (hM : IsCompact M) {c : ℝ}
    (hc : 0 < c) : IsCompact {A : GL n (𝔸 E) | A.val ∈ M ∧ c ≤ ideleAbs A.det} := by
  -- Take `N` so large that Minkowski's theorem in rank one applies to `det A * 2 ^ N`. It gives a
  -- rational `ξ ≠ 0` with `ξ / (det A * 2 ^ N)` in the unit box `B`. As `det A` is bounded, `ξ`
  -- lies in a finite set `F`; so `(det A)⁻¹` is bounded, and then `A⁻¹` by the adjugate formula.
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      (2 * NumberField.rootDiscr E) ^ numInfPlaces E / c < (2 ^ (2 * numInfPlaces E)) ^ N :=
    pow_unbounded_of_one_lt _ (by simp [one_lt_pow₀])
  let t : 𝔸 E := (twoAtInfinity E ^ N).val
  let B : Set (𝔸 E) := Metric.closedBall 0 1 ×ˢ Ô E
  have hB : IsCompact B := isCompact_closedBall_prod_integral
  let F : Set E := {ξ | toAdele ξ ∈ (fun A ↦ det A * t) '' M * B}
  have hF : F.Finite := finite_setOf_toAdele_mem ((hM.image_of_continuous fun A ↦ det A * t).mul hB)
  let T : Set (𝔸 E) := B * (fun ξ ↦ toAdele ξ⁻¹) '' F
  -- The set is closed, so it is enough to bound the pairs `(A, A⁻¹)` by a compact set `K`.
  let K : Set (Matrix n n (𝔸 E) × (Matrix n n (𝔸 E))ᵐᵒᵖ) :=
    (fun (A, b) ↦ (A, MulOpposite.op ((t * b) • A.adjugate))) '' M ×ˢ T
  have hK : IsCompact K := (hM.prod (hB.mul (hF.image _).isCompact)).image_of_continuous _
  refine (Units.isClosedEmbedding_embedProduct.isCompact_preimage hK).of_isClosed_subset
    (.and hM.isClosed.preimage_of_continuous (.preimage_of_continuous isClosed_Ici)) ?_
  rintro (A : GL n (𝔸 E)) ⟨hA, hdet⟩
  have h_lt : (2 * NumberField.rootDiscr E) ^ numInfPlaces E <
      ideleAbs A.det * (2 ^ (2 * numInfPlaces E)) ^ N := by grw [← hdet, ← div_lt_iff₀' hc, hN]
  obtain ⟨ξ, hξ, b, hb, hbξ⟩ : ∃ ξ : E, ξ ≠ 0 ∧ ∃ b ∈ B, A.det.val * t * b = toAdele ξ :=
    exists_mul_twoAtInfinity_pow_mul_eq_toAdele h_lt
  have hξ_mem : ξ ∈ F := mem_mul.2 ⟨A.val.det * t, mem_image_of_mem _ hA, b, hb, hbξ⟩
  have h_det_inv : A.det.val * (t * (b * toAdele ξ⁻¹)) = 1 := by
    rw [← mul_assoc, ← mul_assoc, hbξ, ← map_mul, mul_inv_cancel₀ hξ, map_one]
  have h_inv : A⁻¹.val = (t * (b * toAdele ξ⁻¹)) • A.val.adjugate := by
    rw [coe_units_inv, inv_def, ← GeneralLinearGroup.val_det_apply, Ring.inverse_unit,
      Units.inv_eq_of_mul_eq_one_right h_det_inv]
  exact ⟨(A, b * toAdele ξ⁻¹), ⟨hA, mul_mem_mul hb (mem_image_of_mem _ hξ_mem)⟩,
    Prod.ext rfl (congrArg MulOpposite.op h_inv.symm)⟩

/-- Let `M` and `K` be compact. There is a compact set `B` of adeles such that, whenever the Gram
matrix `yᴴ J y` lies in `K` and `Y` is a rational basis with `y⁻¹ Y (dyadicDiag x)⁻¹ ∈ M` (that is,
`Y ∈ profileBases M x y`), every entry `(Yᴴ J Y) i j`, divided by `2 ^ (x i + x j)` at the infinite
places, lies in `B`. Here `dyadicDiag x` is diagonal with entries `2 ^ x i` at the infinite places
and `1` at the finite places, and `toAdele` embeds `E` in its adeles. -/
lemma exists_compact_gram_entry {M : Set (GL n (𝔸 E))} {K : Set (Matrix n n (𝔸 E))}
    (hM : IsCompact M) (hK : IsCompact K) :
    ∃ B : Set (𝔸 E), IsCompact B ∧
      ∀ {J : Matrix n n E} {y : GL n (𝔸 E)} {x : n → ℤ} {Y : GL n E},
        y.valᴴ * J.map toAdele * y.val ∈ K → Y ∈ profileBases M x y → ∀ i j : n,
          (twoAtInfinity E ^ (-(x i + x j))).val * toAdele ((Y.valᴴ * J * Y.val) i j) ∈ B := by
  -- Take for `B` the set of all entries of the matrices `Aᴴ * C * A` with `A ∈ M` and `C ∈ K`.
  let entry (i j : n) : GL n (𝔸 E) × Matrix n n (𝔸 E) → 𝔸 E :=
    fun (A, C) ↦ (A.valᴴ * C * A.val) i j
  refine ⟨⋃ (i : n) (j : n), entry i j '' M ×ˢ K,
    isCompact_iUnion fun i ↦ isCompact_iUnion fun j ↦ (hM.prod hK).image_of_continuous _,
    fun {J y x Y} hy hY i j ↦ ?_⟩
  let A : GL n (𝔸 E) := y⁻¹ * Y.map toAdele * (dyadicDiag x)⁻¹
  let C : Matrix n n (𝔸 E) := y.valᴴ * J.map toAdele * y.val
  refine mem_iUnion₂.2 ⟨i, j, (A, C), ⟨hY, hy⟩, ?_⟩
  -- In `Aᴴ * C * A` the factors `y` cancel.
  have h_cancel : A.valᴴ * C * A.val = (dyadicDiag x : GL n (𝔸 E))⁻¹.valᴴ *
      ((Y.map toAdele).valᴴ * J.map toAdele * (Y.map toAdele).val) * (dyadicDiag x)⁻¹.val :=
    gram_mul_of_gram_eq (gram_mul_of_gram_eq (gram_inv_of_gram_eq rfl) rfl) rfl
  -- The two copies of `(dyadicDiag x)⁻¹` scale the `(i, j)` entry; compare place by place.
  change (A.valᴴ * C * A.val) i j = _
  rw [h_cancel]
  ext <;>
    simp [dyadicDiag, twoAtInfinity, field, zpow_add₀, ← map_zpow, ← map_inv, ← Matrix.map_mul]

variable (E n) in
/-- For a CM field `E`, there are a compact set `M` of invertible adelic matrices and an integer `c`
such that every `y` in `GL n (𝔸 E)` has a profile `x : n → ℤ` and a rational basis `Y` with
`y⁻¹ Y (dyadicDiag x)⁻¹ ∈ M` (that is, `Y ∈ profileBases M x y`), where `dyadicDiag x` is diagonal
with entries `2 ^ x i` at the infinite places and `1` at the finite places. Moreover `∑ i, x i ≤ c`
whenever `ideleAbs y.det ≥ 1`. -/
lemma exists_isCompact_profileBases :
    ∃ (M : Set (GL n (𝔸 E))) (c : ℤ), IsCompact M ∧
      ∀ y : GL n (𝔸 E), ∃ x : n → ℤ, ∃ Y ∈ profileBases M x y,
        1 ≤ ideleAbs y.det → ∑ i : n, x i ≤ c := by
  -- Take the reduced basis of `exists_basis_frameLength_le_two_zpow` and let `C ≥ 1` bound the
  -- constant there. The matrix `y⁻¹ * Yᵀ * (dyadicDiag x)⁻¹` has entries in the unit box and
  -- determinant of module at least `C⁻¹`, so it stays in the compact set of
  -- `isCompact_setOf_le_ideleAbs_det`.
  let C : ℝ := max ((8 * (numInfPlaces E * Fintype.card n) * NumberField.rootDiscr E) ^
    (numInfPlaces E * Fintype.card n)) 1
  let M : Set (GL n (𝔸 E)) :=
    {A | A.val ∈ (Metric.closedBall 0 1 ×ˢ Ô E : Set (𝔸 E)).matrix ∧ C⁻¹ ≤ ideleAbs A.det}
  refine ⟨M, Int.log (2 ^ (2 * numInfPlaces E)) C,
    isCompact_setOf_le_ideleAbs_det isCompact_closedBall_prod_integral.matrix (by positivity),
    fun y ↦ ?_⟩
  obtain ⟨Y, x, hdet, h_integral, h_length, hvol⟩ := exists_basis_frameLength_le_two_zpow y
  replace hvol : ideleAbs y.det * (2 ^ (2 * numInfPlaces E)) ^ ∑ i, x i ≤ C :=
    hvol.trans (le_max_left _ 1)
  let Z : GL n E := .mk'' Yᵀ (by simpa using hdet)
  refine ⟨x, Z, ⟨fun i j ↦ ?_, ?_⟩, fun hy ↦ ?_⟩
  · -- A single coordinate is at most the Euclidean length.
    have h_coord (w : NumberField.InfinitePlace E) :
        ‖((y⁻¹.val *ᵥ toAdele ∘ Y j) i).1 w‖ ≤ 2 ^ x j :=
      (norm_apply_le_frameLength y (Y j) w i).trans (h_length j)
    have h_entry : (y⁻¹ * Z.map toAdele * (dyadicDiag x)⁻¹).val i j =
        (y⁻¹.val *ᵥ toAdele ∘ Y j) i * (twoAtInfinity E ^ (-x j)).val := by
      change _ = (y⁻¹.val * Yᵀ.map toAdele) i j * _
      simp [Z, dyadicDiag, ← map_inv]
    simpa [h_entry, pi_norm_le_iff_of_nonneg, twoAtInfinity, field, ← map_zpow, ← map_inv]
      using And.intro h_coord (h_integral j i)
  · -- The determinant of the rational matrix `Z` has module `1` by the product formula.
    have h_det : ideleAbs (y⁻¹ * Z.map toAdele * (dyadicDiag x)⁻¹).det =
        (ideleAbs y.det * (2 ^ (2 * numInfPlaces E)) ^ ∑ i, x i)⁻¹ := by
      simp [field, ideleAbs_det_dyadicDiag]
    rw [h_det]
    exact inv_anti₀ (mul_pos (by simp) (by positivity)) hvol
  · have h_pow : ((2 ^ (2 * numInfPlaces E) : ℕ) : ℝ) ^ ∑ i, x i ≤ C :=
      hvol.trans' (by simpa [field] using hy)
    exact (Int.zpow_le_iff_le_log (by simp [one_lt_pow₀]) (by positivity)).1 h_pow

end New.Core

end CompactBases

/-!
## Mahler's criterion for frames of varying forms

Let an adelic frame `y` of a rational form `J` have its Gram matrix in a compact set. Take the
basis dual to a reduced basis at `y` (`New.Core.exists_isCompact_profileBases`), with some of its
columns set to zero. This matrix is bounded at `y` and has one of finitely many Gram matrices
(`New.exists_isBoundedDualBasis`).
-/

section MahlerForms

open Matrix New Core Units Set

namespace New

variable {E : Type*} [Field E] [CMType E] {n : Type*} [Fintype n] [DecidableEq n]

/-- The finite part of an invertible adelic matrix. -/
noncomputable abbrev finitePartGL (g : GL n (𝔸 E)) : GL n (𝔸f E) :=
  g.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))

/-- The basis `W` dual to `Y` for the form `J`, so that `Yᴴ J W = 1`. -/
noncomputable def formDual (J Y : GL n E) : GL n E := (star Y * J)⁻¹

variable (E) in
/-- The diagonal matrix with entry `0` at the indices in `s` and `1` at the others. -/
noncomputable def projectionOff (s : Finset n) : Matrix n n E :=
  diagonal fun i : n ↦ if i ∈ s then 0 else 1

/-- The basis dual to `Y` for the form `J`, with the columns indexed by `s` set to zero. -/
noncomputable def formDualOff (J Y : GL n E) (s : Finset n) : Matrix n n E :=
  (formDual J Y).val * projectionOff E s

/-- The columns of `Y` indexed by `s` span an isotropic subspace for `J`, and the basis `W` dual to
`Y` is bounded at the frame `y`: the finite part of `W⁻¹ y` lies in `Cf`, and the matrix `Z` made
from `W` by setting the columns indexed by `s` to zero has `y⁻¹ Z ∈ C` and `Zᴴ J Z ∈ F`. -/
structure IsBoundedDualBasis (F : Set (Matrix n n E)) (C : Set (Matrix n n (𝔸 E)))
    (Cf : Set (GL n (𝔸f E))) (J : GL n E) (y : GL n (𝔸 E)) (Y : GL n E) (s : Finset n) :
    Prop where
  /-- The columns of `Y` indexed by `s` span an isotropic subspace. -/
  isotropic : ∀ i ∈ s, ∀ j ∈ s, (Y.valᴴ * J.val * Y.val) i j = 0
  /-- The Gram matrix of the remaining dual columns lies in `F`. -/
  gram_mem : (formDualOff J Y s)ᴴ * J.val * formDualOff J Y s ∈ F
  /-- The remaining dual columns, in the coordinates of `y`, form a matrix in `C`. -/
  frame_mem : y⁻¹.val * (formDualOff J Y s).map toAdele ∈ C
  /-- The finite part of `W⁻¹ y`, for the whole dual basis `W`, lies in `Cf`. -/
  finitePart_mem : finitePartGL ((formDual J Y)⁻¹.map toAdele * y) ∈ Cf

/-- For `m = y⁻¹ Y (dyadicDiag x)⁻¹`, the product of `mᴴ` with the Gram matrix `yᴴ J y` is
`(dyadicDiag x)⁻¹ᴴ W⁻¹ y`, where `W = formDual J Y` is the basis dual to `Y` for the form `J`.
Here `dyadicDiag x` is diagonal with entries `2 ^ x i` at the infinite places and `1` at the
others. -/
lemma star_frame_mul_gram_eq_star_dyadicDiag_inv_mul (J Y : GL n E) (y : GL n (𝔸 E)) (x : n → ℤ) :
    star (y⁻¹ * Y.map toAdele * (dyadicDiag x)⁻¹) * (star y * J.map toAdele * y) =
      star (dyadicDiag x : GL n (𝔸 E))⁻¹ * ((formDual J Y)⁻¹.map toAdele * y) := by
  ext1
  simp [formDual, mul_assoc, star_eq_conjTranspose, conjTranspose_nonsing_inv]

/-- The conjugate transpose of `(dyadicDiag x)⁻¹` times the projection off `s` is diagonal, with
entry `0` at the indices in `s` and, at the other indices `j`, the idele that is `2 ^ (-x j)` at
the infinite places and `1` at the finite ones. -/
lemma star_dyadicDiag_inv_mul_projectionOff (x : n → ℤ) (s : Finset n) :
    (star (dyadicDiag x : GL n (𝔸 E))⁻¹).val * (projectionOff E s).map toAdele =
      diagonal fun j : n ↦ if j ∈ s then 0 else (twoAtInfinity E ^ (-x j)).val := by
  -- The diagonal entries are real, hence `star` fixes the first factor.
  have h_star : (star (dyadicDiag x : GL n (𝔸 E))⁻¹).val =
      diagonal fun j ↦ (twoAtInfinity E ^ (-x j)).val := by
    simp [dyadicDiag, twoAtInfinity, star_eq_conjTranspose, ← map_zpow, ← map_inv, funext_iff,
      Prod.ext_iff]
  rw [h_star, projectionOff, diagonal_map (map_zero _), diagonal_mul_diagonal]
  simp [apply_ite toAdele]

/-- Mahler's criterion for frames of forms that may vary, by the dual of a reduced basis. Given a
compact `K`, there are a finite `F` and compact `C`, `Cf` such that, for each invertible `J` over
`E` and adelic frame `y` with `yᴴ J y ∈ K`, some rational basis `Y` and set `s` of its columns
satisfy `New.IsBoundedDualBasis`. That is, the columns in `s` span an isotropic subspace; the
basis dual to `Y`, with its columns in `s` set to zero, has its Gram matrix in `F` and lies in `C`
in the coordinates of `y`; and the whole dual basis is bounded at the finite places by `Cf`. -/
lemma exists_isBoundedDualBasis {K : Set (GL n (𝔸 E))} (hK : IsCompact K) :
    ∃ (F : Set (Matrix n n E)) (C : Set (Matrix n n (𝔸 E))) (Cf : Set (GL n (𝔸f E))),
      F.Finite ∧ IsCompact C ∧ IsCompact Cf ∧
      ∀ (J : GL n E) (y : GL n (𝔸 E)), star y * J.map toAdele * y ∈ K →
        ∃ (Y : GL n E) (s : Finset n), IsBoundedDualBasis F C Cf J y Y s := by
  -- Take a reduced basis `Y` at `y`, of profile `x` for the compact set `M`. Call `j` short if
  -- `x j < c / 2`, for `c` as below; `s` is the set of short indices.
  obtain ⟨M, _, hM, exists_basis⟩ := exists_isCompact_profileBases E n
  -- `(Yᴴ J Y) i j`, divided by `2 ^ (x i + x j)` at infinity, lies in a compact set of adeles
  -- (`h_entry`); an element of `E` with this property is zero once `x i + x j < c`.
  obtain ⟨entries, h_entries, h_entry⟩ := exists_compact_gram_entry hM (hK.image continuous_val)
  obtain ⟨c, hc⟩ : ∃ c : ℤ, ∀ e < c, ∀ {a : E},
      (twoAtInfinity E ^ (-e)).val * toAdele a ∈ entries → a = 0 :=
    exists_eq_zero_of_zpow_mul_mem h_entries
  -- `Cf` holds the finite parts of the `B ∈ Mᴴ K`, and `C` the products `B⁻¹ Δ` with `Δ`
  -- integral and bounded by `2⁻¹ ^ (c / 2)` at infinity.
  let Ω : Set (Matrix n n (𝔸 E)) :=
    (Metric.closedBall 0 (2⁻¹ ^ (c / 2)) ×ˢ SetLike.coe (Ô E)).matrix
  let N : Set (GL n (𝔸 E)) := (fun (m, S) ↦ star m * S) '' M ×ˢ K
  have hN : IsCompact N := (hM.prod hK).image_of_continuous fun p ↦ star p.1 * p.2
  let C : Set (Matrix n n (𝔸 E)) := (fun (B, Δ) ↦ B⁻¹.val * Δ) '' N ×ˢ Ω
  have hC : IsCompact C :=
    (hN.prod (isCompact_closedBall_prod_integral _).matrix).image_of_continuous fun p ↦
      p.1⁻¹.val * p.2
  -- A rational Gram matrix `Aᴴ S A` with `A ∈ C` and `S ∈ K` has finitely many values.
  let F : Set (Matrix n n E) := {G | ∃ p ∈ C ×ˢ K, p.1ᴴ * p.2.val * p.1 = G.map toAdele}
  refine ⟨F, C, finitePartGL '' N,
    finite_setOf_map_toAdele_mem ((hC.prod hK).image_of_continuous fun p ↦ p.1ᴴ * p.2.val * p.1),
      hC,
    hN.image continuous_snd.generalLinearGroup_map, fun J y hy ↦ ?_⟩
  obtain ⟨x, Y, hY, -⟩ := exists_basis y
  let s : Finset n := {j | x j < c / 2}
  let Z : Matrix n n E := formDualOff J Y s
  have h_isotropic (i : n) (hi : i ∈ s) (j : n) (hj : j ∈ s) :
      (Y.valᴴ * J.val * Y.val) i j = 0 := by
    simp only [s, Finset.mem_filter_univ] at hi hj
    exact hc _ (by omega) (h_entry (mem_image_of_mem val hy) hY i j)
  -- `B = mᴴ S` for `m = y⁻¹ Y (dyadicDiag x)⁻¹ ∈ M` and `S = yᴴ J y ∈ K`.
  let B : GL n (𝔸 E) :=
    star (y⁻¹ * Y.map toAdele * (dyadicDiag x)⁻¹) * (star y * J.map toAdele * y)
  have hB_mem : B ∈ N := ⟨(y⁻¹ * Y.map toAdele * (dyadicDiag x)⁻¹, _), ⟨hY, hy⟩, rfl⟩
  have hB_eq : B = star (dyadicDiag x : GL n (𝔸 E))⁻¹ * ((formDual J Y)⁻¹.map toAdele * y) :=
    star_frame_mul_gram_eq_star_dyadicDiag_inv_mul J Y y x
  let A : Matrix n n (𝔸 E) := y⁻¹.val * Z.map toAdele
  -- `B A` is diagonal: entry `j` is `0` for short `j`, else `2 ^ (-x j)` at infinity.
  have h_diagonal :
      B.val * A = diagonal fun j ↦ if j ∈ s then 0 else (twoAtInfinity E ^ (-x j)).val := by
    have h_cancel : B * y⁻¹ * (formDual J Y).map toAdele = star (dyadicDiag x : GL n (𝔸 E))⁻¹ := by
      simp [hB_eq, mul_assoc]
    rw [← star_dyadicDiag_inv_mul_projectionOff, ← h_cancel]
    simp [A, Z, formDualOff, mul_assoc]
  have hΔ : B.val * A ∈ Ω := by
    have h_long (j : n) (hj : j ∉ s) : c / 2 ≤ x j := by simpa [s] using hj
    simpa [h_diagonal, Ω, diagonal_mem_matrix_iff, ite_mem, zpow_nonneg, twoAtInfinity,
      ← map_zpow, ← map_inv, field] using h_long
  have h_frame : A ∈ C := ⟨(B, B.val * A), ⟨hB_mem, hΔ⟩, B.inv_mul_cancel_left A⟩
  have h_gram : Aᴴ * (star y * J.map toAdele * y).val * A = (Zᴴ * J.val * Z).map toAdele := by
    simp [A, mul_assoc, star_eq_conjTranspose, ← Matrix.map_mul, conjTranspose_nonsing_inv]
  -- `dyadicDiag x` is `1` at the finite places.
  have h_finite : finitePartGL B = finitePartGL ((formDual J Y)⁻¹.map toAdele * y) := by
    simp [hB_eq, Units.ext_iff, dyadicDiag, twoAtInfinity, star_eq_conjTranspose, ← map_zpow,
      ← map_inv]
  exact ⟨Y, s, {
    isotropic := h_isotropic, frame_mem := h_frame, finitePart_mem := ⟨B, hB_mem, h_finite⟩
    gram_mem := ⟨(A, star y * J.map toAdele * y), ⟨h_frame, hy⟩, h_gram⟩ }⟩

end New

end MahlerForms

/-!
## Haar measure on the adelic unitary group and integration over [G]

The `volume` on the adelic unitary group `New.G` is a Haar measure: `G` is a product whose first
factor `GInf` carries a product (pi) Haar measure, and `volume` on `G` is the product measure.
-/

section GroupMeasure

open MeasureTheory Measure NumberField

namespace New

variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  {s : n → ℤˣ}

deriving instance MeasurableMul₂, MeasurableInv for G

instance : (volume : Measure (G E s)).IsHaarMeasure :=
  have : (volume : Measure (GInf E s)).IsHaarMeasure := pi.isHaarMeasure _
  prod.instIsHaarMeasure volume volume

instance : SFinite (volume : Measure (G E s)) := inferInstance

/-- The measure on `G E s` that computes integrals over the quotient `V.Γ \ G E s` by the rational
points of the space `V`: Haar measure weighted by a cutoff for counting measure on `V.Γ`, chosen so
that integrating `∑ γ : V.Γ, F (γ • g)` against it gives `∫⁻ F` for `volume`. -/
noncomputable abbrev Space.quotMeasure {E : Type} [Field E] [CMType E]
    (V : Space E n s) : Measure (G E s) :=
  V.Γ.quotMeasure

end New

end GroupMeasure

/-! ## Finite volume of [G] and integrability of counts of rational matrices -/

namespace New

open NumberField Matrix MeasureTheory New.Core Set ENNReal Finset Fintype Function

section

variable {E n : Type*} [Field E] [CMType E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  (V : Space E n s)

omit [Fintype n] [DecidableEq n] in
/-- If `θ - star θ` is invertible, then `S + θ • T` determines the hermitian matrices `S`, `T`. -/
lemma Core.eq_of_add_smul_eq_of_hermitian {θ : E} (hθ : IsUnit (θ - star θ))
    {S T S' T' : Matrix n n E} (hS : Sᴴ = S) (hT : Tᴴ = T) (hS' : S'ᴴ = S') (hT' : T'ᴴ = T')
    (h_eq : S + θ • T = S' + θ • T') : (S, T) = (S', T') := by
  -- Subtract the conjugate transpose of the equation and cancel `θ - star θ`.
  have h_star : S + star θ • T = S' + star θ • T' := by
    simpa [hS, hT, hS', hT'] using congrArg conjTranspose h_eq
  have h_sub : (θ - star θ) • T = (θ - star θ) • T' := by
    linear_combination (norm := module) h_eq - h_star
  obtain rfl : T = T' := hθ.smul_left_cancel.1 h_sub
  rw [add_right_cancel h_eq]

/-- For a compact set `B` of adelic matrices there is a finite constant `C` such that, for all
`x : n → ℤ`, at most `C * (2 ^ numInfPlaces E) ^ ∑ i, ∑ j, (x i + x j)₊` hermitian matrices `T`
over `E` land in `B` when `T i j` is scaled by `2 ^ (-(x i + x j))` at the infinite places. Here
`numInfPlaces E` is the number of infinite places, and `twoAtInfinity E` is the idele that is `2`
at these places and `1` at the finite ones. -/
lemma Core.encard_hermitian_le {B : Set (Matrix n n (𝔸 E))} (hB : IsCompact B) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x : n → ℤ,
      {T : Matrix n n E | Tᴴ = T ∧
          (of fun i j : n ↦ ↑(twoAtInfinity E ^ (-(x i + x j))) * toAdele (T i j)) ∈ B}.encard ≤
        C * ENNReal.ofReal ((2 ^ numInfPlaces E) ^ ∑ i : n, ∑ j : n, (x i + x j).toNat) := by
  -- For `θ ≠ star θ` the map `(S, T) ↦ S + θ • T` is injective on pairs of hermitian matrices, so
  -- the square of the count is at most a count of arbitrary matrices that scale into `B + θ • B`.
  open Pointwise in
  obtain ⟨θ, hθ⟩ : ∃ θ : E, IsUnit (θ - star θ) := exists_isUnit_sub_star
  let B' : Set (n × n → 𝔸 E) := vec '' (B + toAdele θ • B)
  have hB' : IsCompact B' := (hB.add (hB.smul (toAdele θ))).image_of_continuous vec
    (by fun_prop [vec])
  obtain ⟨C₀, hC₀, h_count⟩ := encard_le_of_dyadic_box hB'
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0∞, C ^ (2 : ℝ) = C₀ := rpow_left_surjective two_ne_zero C₀
  refine ⟨C, fun h_top ↦ hC₀ (by simp [← hC, h_top]), fun x ↦ ?_⟩
  let H : Set (Matrix n n E) := {T | Tᴴ = T ∧
    (of fun i j : n ↦ ↑(twoAtInfinity E ^ (-(x i + x j))) * toAdele (T i j)) ∈ B}
  suffices h_sq : ((H ×ˢ H).encard : ℝ≥0∞) ≤
      C₀ * ENNReal.ofReal (((2 ^ numInfPlaces E) ^ ∑ p : n × n, (x p.1 + x p.2).toNat) ^ 2) by
    rw [← ENNReal.pow_le_pow_left_iff two_ne_zero]
    simpa [H, ← hC, encard_prod, sq, mul_pow, sum_prod_type, ← pow_mul, mul_mul_mul_comm] using h_sq
  refine h_count (fun (i, j) ↦ x i + x j) (fun (S, T) ↦ (S + θ • T).vec) ?_ ?_
  · rintro ⟨S, T⟩ ⟨⟨hS, -⟩, hT, -⟩ ⟨S', T'⟩ ⟨⟨hS', -⟩, hT', -⟩ h_vec
    exact eq_of_add_smul_eq_of_hermitian hθ hS hT hS' hT' (vec_bijective.injective h_vec)
  · -- If `S` and `T` scale into `B`, then `S + θ • T` scales into `B + θ • B`.
    rintro ⟨S, T⟩ ⟨⟨-, hS⟩, -, hT⟩
    refine ⟨_, add_mem_add hS (smul_mem_smul_set hT), funext fun (i, j) ↦ ?_⟩
    simp [add_comm (-x i), mul_add, mul_left_comm]

/-- The module (adelic absolute value) of the determinant of the point `V.x` of a space is `1`. -/
lemma Space.ideleAbs_det_x : ideleAbs V.x.det = 1 := by
  let J : GL n (𝔸 E) := .map toAdele V.isUnit_J.unit
  -- By `V.gram_point` the matrix `xᴴ J x` is the standard form, whose square is `1`.
  have h_sq : (star V.x * J * V.x) ^ 2 = 1 := Units.ext (by simp [J, sq, star, V.gram_point])
  -- The rational `det J` has module `1` by the product formula, so `|det x| ^ 4 = 1`.
  simpa [J, field, pow_eq_one_iff_of_nonneg] using congrArg (fun g ↦ ideleAbs g.det) h_sq

variable (E n) in
/-- The invertible adelic matrices with entries in the closed unit box (absolute value at most `1`
at the infinite places, integral at the finite places) and determinant of module at least `1`. -/
def Core.unitBoxGL : Set (GL n (𝔸 E)) :=
  {A : GL n (𝔸 E) | A.val ∈ (Metric.closedBall 0 1 ×ˢ Ô E).matrix ∧ 1 ≤ ideleAbs A.det}

lemma Core.isCompact_unitBoxGL : IsCompact (unitBoxGL E n) :=
  isCompact_setOf_le_ideleAbs_det isCompact_closedBall_prod_integral.matrix one_pos

open Pointwise in
/-- From one basis `Y` of profile `x` one gets many: with `T = ∑ (x i - x j)₊`, the number
`2 ^ (2 * numInfPlaces E * T)` is at most `((2 * rootDiscr E) ^ numInfPlaces E) ^ card (n × n)`
times the number of bases of profile `x` for `M * unitBoxGL E n`. These come from adding to column
`j` of `Y` the columns `i` times integers of `E` of size less than `2 ^ (x j - x i)`. Here
`profileBases M x y` is the set of rational `Y` with `y⁻¹ Y (dyadicDiag x)⁻¹ ∈ M`, where
`dyadicDiag x` is diagonal with entries `2 ^ x i` at infinity and `1` at the finite places.
`numInfPlaces E` is the number of infinite places and `rootDiscr E` the root discriminant.
`unitBoxGL E n` is the set of invertible adelic matrices with entries of absolute value at most `1`
at infinity and integral at the finite places, and determinant of module at least `1`. -/
lemma Core.two_pow_sq_le_encard_profileBases {M : Set (GL n (𝔸 E))} {x : n → ℤ}
    {y : GL n (𝔸 E)} {Y : GL n E} (hY : Y ∈ profileBases M x y) :
    (2 ^ (numInfPlaces E * ∑ p : n × n, (x p.1 - x p.2).toNat)) ^ 2 ≤
      ENNReal.ofReal (((2 * rootDiscr E) ^ numInfPlaces E) ^ card (n × n)) *
        (profileBases (M * unitBoxGL E n) x y).encard := by
  let D : GL (n × n) (𝔸 E) := Core.dyadicDiag fun p ↦ (x p.1 - x p.2).toNat
  let U : Set (n × n → E) := {u | ∀ p, (D⁻¹.val *ᵥ toAdele ∘ u) p ∈ Metric.ball 0 1 ×ˢ Ô E}
  suffices h_sub :
      U ⊆ (fun Z : GL n E ↦ (Y.inv * Z.val - 1).vec) '' profileBases (M * unitBoxGL E n) x y by
    calc
      _ = ENNReal.ofReal (ideleAbs D.det) := by
        simp [D, ideleAbs_det_dyadicDiag_natCast, ← pow_mul, -Int.ofNat_toNat]
      _ ≤ ENNReal.ofReal (((2 * rootDiscr E) ^ numInfPlaces E) ^ card (n × n)) * U.encard :=
        minkowski_first D
      _ ≤ _ := by grw [h_sub, encard_image_le]
  intro u hu
  -- An integer of absolute value less than `1` at all infinite places is zero.
  have u_zero (p : n × n) (h_le : x p.1 ≤ x p.2) : u p = 0 := by
    obtain ⟨h_norm, h_int⟩ : (∀ v : InfinitePlace E, ‖Φ v (u p)‖ < 1) ∧ IsIntegral ℤ (u p) := by
      simpa [h_le, D, Core.dyadicDiag, ← map_inv, pi_norm_lt_iff, mulVec_diagonal] using hu p
    exact eq_zero_of_forall_norm_lt_one h_int h_norm
  -- So `1 + uᵀ` is unitriangular for the order of the `x i`.
  have h_det : (1 + (of u.curry)ᵀ).det = 1 :=
    det_eq_one_of_unitriangular fun i j (h_le : x j ≤ x i) ↦ by simp [u_zero (j, i) h_le]
  let Z : GL n E := .mk'' (1 + (of u.curry)ᵀ) (by simp [h_det])
  -- The conjugate of `Z` by the diagonal matrix of `x` has its entries in the unit box.
  have h_conj : dyadicDiag x * Z.map toAdele * (dyadicDiag x)⁻¹ ∈ unitBoxGL E n := by
    refine ⟨fun i j ↦ ?_, by simp [Z, field]⟩
    have h_box : (D⁻¹.val *ᵥ toAdele ∘ u) (j, i) ∈ Metric.closedBall 0 1 ×ˢ Ô E :=
      prod_mono_left Metric.ball_subset_closedBall (hu (j, i))
    -- The `(i, j)` entry is `1` if `i = j`, is `0` if `x j ≤ x i`, else is the entry of `h_box`.
    obtain rfl | h_ne := eq_or_ne i j
    · simp [Z, Core.dyadicDiag, ← map_inv diagGL, -map_inv, u_zero (i, i) le_rfl]
    obtain h_le | h_le := le_total (x j) (x i)
    · simp [Z, Core.dyadicDiag, ← map_inv diagGL, -map_inv, u_zero (j, i) h_le, h_ne]
    simpa [h_ne, h_le, Z, D, Core.dyadicDiag, ← map_inv diagGL, -map_inv, mul_comm,
      _root_.zpow_sub, mul_assoc, mulVec_diagonal] using h_box
  -- The basis `Y * Z` has profile `x` for `M * unitBoxGL E n`, and `Y⁻¹ * (Y * Z) - 1 = uᵀ`.
  exact ⟨Y * Z, mem_mul.2 ⟨_, hY, _, h_conj, by simp [mul_assoc]⟩, by simp [Z, funext_iff]⟩

/-- For a compact `M` there is a compact set `S` of adeles that holds the Gram entries
`(Yᴴ V.J Y) i j`, divided by `2 ^ (x i + x j)` at the infinite places, for every space `V` with
signs `s` and every rational basis `Y` with `V.x⁻¹ Y (dyadicDiag x)⁻¹ ∈ M`. -/
lemma Space.exists_isCompact_gram_entry_mem {M : Set (GL n (𝔸 E))} (hM : IsCompact M)
    (s : n → ℤˣ) : ∃ S : Set (𝔸 E), IsCompact S ∧
      ∀ (V : Space E n s) {x : n → ℤ} {Y : GL n E}, Y ∈ profileBases M x V.x →
        ∀ i j : n, (twoAtInfinity E ^ (-(x i + x j))).val * (Y.valᴴ * V.J * Y) i j ∈ S := by
  obtain ⟨S, hS, gram_mem⟩ := exists_compact_gram_entry hM (isCompact_singleton (x := stdForm E s))
  exact ⟨S, hS, fun V x Y hY ↦ gram_mem V.gram_point hY⟩

/-- If `Y` is a basis of profile `x` at the point of `V` (that is,
`V.x⁻¹ Y (dyadicDiag x)⁻¹ ∈ M`) and `∑ i, x i ≤ c`, then `x` is nearly symmetric about `0`: for
some permutation `σ` all `|x (σ i) + x i|` are at most a constant `B`, which depends only on the
compact set `M`, on `c` and on the signs `s`. -/
lemma Space.exists_perm_natAbs_add_le {M : Set (GL n (𝔸 E))} (hM : IsCompact M) (c : ℤ) :
    ∃ B : ℕ, ∀ (V : Space E n s) (x : n → ℤ) (Y : GL n E), Y ∈ profileBases M x V.x →
      ∑ i : n, x i ≤ c → ∃ σ : Equiv.Perm n, ∀ i : n, (x (σ i) + x i).natAbs ≤ B := by
  -- The scaled entries of the Gram matrices lie in a compact set `S`. An element of `E` that lies
  -- in `S` after scaling by `2 ^ (-e)` with `e < d` is zero.
  obtain ⟨S, hS, gram_mem⟩ := exists_isCompact_gram_entry_mem hM s
  obtain ⟨d, hd⟩ := exists_eq_zero_of_zpow_mul_mem hS
  refine ⟨(2 * c - card n * d).toNat + d.natAbs, fun V x Y hY hx ↦ ?_⟩
  -- The Gram matrix of `Y` is invertible, so for some permutation `σ` its entries at `(σ i, i)`
  -- are non-zero. Hence `d ≤ x (σ i) + x i`, and these sums are bounded above too, as `∑ x ≤ c`.
  have h_det : (Y.valᴴ * V.J * Y.val).det ≠ 0 := (star Y * V.isUnit_J.unit * Y).det_ne_zero
  obtain ⟨σ, entry_ne⟩ : ∃ σ : Equiv.Perm n, ∀ i, (Y.valᴴ * V.J * Y.val) (σ i) i ≠ 0 := by
    rw [det_apply] at h_det
    simpa [smul_eq_zero_iff_eq, prod_eq_zero_iff] using exists_ne_zero_of_sum_ne_zero h_det
  have pair_ge (i : n) : 0 ≤ x (σ i) + x i - d :=
    sub_nonneg_of_le <| le_of_not_gt fun h_lt ↦ entry_ne i (hd _ h_lt (gram_mem V hY (σ i) i))
  refine ⟨σ, fun i ↦ ?_⟩
  have h_le : x (σ i) + x i ≤ ∑ j, x j + ∑ j, x j - card n * d + d := by
    simpa [sum_add_distrib, σ.sum_comp] using single_le_sum (fun j _ ↦ pair_ge j) (mem_univ i)
  grind [pair_ge i]

omit [DecidableEq n] in
/-- The inequality of exponents behind `Space.lintegral_encard_ne_top`. Write `ν = ∑ (-x i)₊`,
`P = ∑ (x i + x j)₊` and `T = ∑ (x i - x j)₊`. Suppose `|x (σ i) + x i| ≤ B` for a permutation `σ`,
and that `2 m` is less than the number `N` of indices whenever there is at least one index. Then
`4 m ν + 2 P + ∑ |x i| ≤ 4 T + 6 (N + 1) ^ 2 B`. -/
lemma Core.sum_toNat_neg_add_le {m B : ℕ} (h_rank : Nonempty n → 2 * m < card n) {x : n → ℤ}
    {σ : Equiv.Perm n} (h_pair : ∀ i : n, (x (σ i) + x i).natAbs ≤ B) :
    4 * (m * ∑ i : n, (-x i).toNat) + 2 * ∑ i : n, ∑ j : n, (x i + x j).toNat +
      ∑ i : n, (x i).natAbs ≤
      4 * ∑ i : n, ∑ j : n, (x i - x j).toNat + 6 * ((card n + 1) ^ 2 * B) := by
  -- Term by term, `∑ |x i| + 2 N ν + 2 P ≤ 2 ν + 4 T + O(B)`.
  have h_sum : ∑ i, ((x i).natAbs + ∑ j, 2 * ((-x (σ i)).toNat + (x i + x j).toNat)) ≤
      ∑ i, ((-x i).toNat + (-x (σ i)).toNat + B +
        ∑ j, ((x i - x j).toNat + 3 * (x i - x (σ j)).toNat + 5 * B)) := by
    gcongr with i _ j _
    · grind [h_pair i]
    · grind [h_pair i, h_pair j]
  -- The rank condition gives `(2 m + 1) ν ≤ N ν`.
  have h_mul : (2 * m + 1) * ∑ i, (-x i).toNat ≤ card n * ∑ i, (-x i).toNat := by
    simp only [mul_sum]
    exact sum_le_sum fun i _ ↦ Nat.mul_le_mul_right _ (h_rank ⟨i⟩)
  simp only [sum_add_distrib, mul_add, ← mul_sum, Equiv.sum_comp σ fun i ↦ (-x i).toNat,
    fun i ↦ Equiv.sum_comp σ fun j ↦ (x i - x j).toNat, sum_const, card_univ, smul_eq_mul] at h_sum
  lia

end

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  (V : Space E n s)

open Pointwise in
/-- For `g` in the adelic unitary group `G E s`, a basis at `g` is a rational `Z` in
`profileBases N x (V.move g).x`, that is, one with `(V.x * g)⁻¹ Z (dyadicDiag x)⁻¹ ∈ N`; its Gram
matrix is `Zᴴ V.J Z`. Let `𝒯` hold the Gram matrices of all bases, and for each such matrix `T`
let `r T` be a basis at `A T` with Gram matrix `T`. If `B` contains every group element whose
adelic matrix `G.adeleMatrix` lies in `N * N⁻¹`, then the number of bases at `g`, times a weight
`w`, is at most the sum over `γ ∈ V.Γ` and `T ∈ 𝒯` of `w` times the indicator of `γ g ∈ A T * B`. -/
lemma Space.encard_profileBases_mul_le_lintegral {N : Set (GL n (𝔸 E))} {x : n → ℤ}
    {𝒯 : Set (Matrix n n E)} {A : Matrix n n E → G E s} {r : Matrix n n E → GL n E}
    {B : Set (G E s)} (hB : G.adeleMatrix ⁻¹' (Units.val '' (N * N⁻¹)) ⊆ B)
    (h_gram : ∀ g : G E s, ∀ Z ∈ profileBases N x (V.move g).x, Z.valᴴ * V.J * Z.val ∈ 𝒯)
    (h_basis : ∀ g : G E s, ∀ Z ∈ profileBases N x (V.move g).x,
      r (Z.valᴴ * V.J * Z.val) ∈ profileBases N x (V.move (A (Z.valᴴ * V.J * Z.val))).x)
    (h_gram_basis : ∀ g : G E s, ∀ Z ∈ profileBases N x (V.move g).x,
      (r (Z.valᴴ * V.J * Z.val)).valᴴ * V.J * (r (Z.valᴴ * V.J * Z.val)).val =
        Z.valᴴ * V.J * Z.val)
    (w : ℝ≥0∞) (g : G E s) :
    (profileBases N x (V.move g).x).encard * w ≤
      ∫⁻ γ : V.Γ, ∑' T : 𝒯,
        ((fun h : G E s ↦ (A T)⁻¹ * h) ⁻¹' B).indicator (fun _ ↦ w) (γ • g) ∂.count := by
  -- A basis `Z` at `g` with Gram matrix `T` gives `γ = r T * Z⁻¹` in `V.Γ` with `γ g ∈ A T * B`;
  -- `Z` is determined by the pair `(T, γ)`.
  let Bases : Set (GL n E) := profileBases N x (V.move g).x
  let F (T : 𝒯) : G E s → ℝ≥0∞ := ((fun h ↦ (A T)⁻¹ * h) ⁻¹' B).indicator fun _ ↦ w
  let T (Z : Bases) : 𝒯 := ⟨(Z : GL n E).valᴴ * V.J * (Z : GL n E), h_gram g Z Z.property⟩
  have h_unitary (Z : Bases) : r (T Z) * (Z : GL n E)⁻¹ ∈ U V.J :=
    gram_mul_of_gram_eq (h_gram_basis g Z Z.property) (gram_inv_of_gram_eq rfl)
  let γ (Z : Bases) : V.Γ := ⟨V.ratEmbed ⟨r (T Z) * (Z : GL n E)⁻¹, h_unitary Z⟩, _, rfl⟩
  have h_inj : Injective fun Z ↦ (T Z, γ Z) := by
    simp +contextual [Injective, Subtype.ext_iff, V.ratEmbed_injective.eq_iff, γ]
  have h_val (Z : Bases) : F (T Z) (γ Z • g) = w := by
    refine indicator_of_mem (s := _ ⁻¹' B) (hB ⟨_, mul_mem_mul (h_basis g Z Z.property)
      (inv_mem_inv.2 Z.property), ?_⟩) fun _ ↦ w
    simp [γ, T, move, ratEmbed, toRatCoords, G.adeleMatrix, U.map, Matrix.mul_assoc]
  calc
    _ = ∑' Z : Bases, F (T Z) (γ Z • g) := by simp [h_val, Bases]
    _ ≤ ∑' q : 𝒯 × V.Γ, F q.1 (q.2 • g) :=
      tsum_comp_le_tsum_of_injective h_inj fun q ↦ F q.1 (q.2 • g)
    _ = ∫⁻ γ : V.Γ, ∑' T, F T (γ • g) ∂.count := by
      rw [lintegral_count, ENNReal.tsum_comm, ENNReal.tsum_prod']

open Pointwise in
/-- Unfolding over the rational points `V.Γ` of the adelic unitary group `G E s`, for a hermitian
space `V` over a CM field `E` with its point `V.x`. Suppose that for each `g`, `f g` is at most
`ω x` times the number of rational bases of some profile `x` at the moved point
`(V.move g).x = V.x * g`, that is, of `Y` with `(V.x * g)⁻¹ Y (dyadicDiag x)⁻¹` in the compact set
`N`, where `dyadicDiag x` is diagonal with entries `2 ^ x i` at the infinite places and `1` at the
finite places. Bases with the same Gram matrix differ by `V.Γ`, and there are
`O(2 ^ (numInfPlaces E * ∑ i, ∑ j, (x i + x j)₊))` Gram matrices of profile `x`, so `f` has finite
integral against `V.quotMeasure` (the measure on `G E s` that integrates invariant functions over
`V.Γ \ G`) if `ω x` times this power of `2` is summable over `x`. -/
lemma Space.lintegral_ne_top_of_le_encard_profileBases {N : Set (GL n (𝔸 E))} (hN : IsCompact N)
    {ω : (n → ℤ) → ℝ≥0∞}
    (hω : ∑' x : n → ℤ, 2 ^ (numInfPlaces E * ∑ i : n, ∑ j : n, (x i + x j).toNat) * ω x ≠ ∞)
    {f : G E s → ℝ≥0∞}
    (hf : ∀ g : G E s, ∃ x : n → ℤ, f g ≤ (profileBases N x (V.move g).x).encard * ω x) :
    ∫⁻ g : G E s, f g ∂V.quotMeasure ≠ ∞ := by
  -- The scaled entries of the Gram matrices lie in a compact set `S`; this bounds their number.
  obtain ⟨S, hS, gram_mem⟩ := exists_isCompact_gram_entry_mem hN s
  let gram (x : n → ℤ) : Set (Matrix n n E) := {T | Tᴴ = T ∧
    (of fun i j ↦ ↑(twoAtInfinity E ^ (-(x i + x j))) * toAdele (T i j)) ∈ S.matrix}
  obtain ⟨C, hC, card_gram⟩ : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x : n → ℤ,
      (gram x).encard ≤ C * 2 ^ (numInfPlaces E * ∑ i, ∑ j, (x i + x j).toNat) := by
    simpa [gram, ← pow_mul] using encard_hermitian_le (n := n) hS.matrix
  -- For each profile `x` and Gram matrix `T` that occur, fix a point `A x T` and a basis `r x T`
  -- there. A point `g` with a basis of Gram matrix `T` is in a translate `γ⁻¹ (A x T * B)`.
  let Occurs (x : n → ℤ) (T : Matrix n n E) : Prop :=
    ∃ g : G E s, ∃ Z ∈ profileBases N x (V.move g).x, Z.valᴴ * V.J * Z = T
  choose! A r hr gram_r using fun (x : n → ℤ) (T : Matrix n n E) (hT : Occurs x T) ↦ hT
  let B : Set (G E s) := G.adeleMatrix ⁻¹' (Units.val '' (N * N⁻¹))
  have hB : IsCompact B :=
    G.isClosedEmbedding_adeleMatrix.isCompact_preimage
      ((hN.mul hN.inv).image_of_continuous Units.val)
  -- For `p = (x, T)`, `F p` is `ω x` times the indicator of `A x T * B`.
  let F (p : Σ x, gram x) : G E s → ℝ≥0∞ :=
    ((fun g ↦ (A p.1 p.2)⁻¹ * g) ⁻¹' B).indicator fun _ ↦ ω p.1
  have F_meas (p : Σ x, gram x) : Measurable (F p) :=
    measurable_const.indicator (measurable_const_mul (A p.1 p.2)⁻¹ hB.measurableSet)
  have bases_le (g : G E s) (x : n → ℤ) :
      (profileBases N x (V.move g).x).encard * ω x ≤ ∫⁻ γ : V.Γ, ∑' p, F p (γ • g) ∂.count := by
    calc
      _ ≤ ∫⁻ γ : V.Γ, ∑' T : gram x, F ⟨x, T⟩ (γ • g) ∂.count :=
        V.encard_profileBases_mul_le_lintegral (𝒯 := gram x) subset_rfl
          (fun h Z hZ ↦ ⟨IsSelfAdjoint.conjugate' V.conjTranspose_J _, gram_mem (V.move h) hZ⟩)
          (fun h Z hZ ↦ hr x _ ⟨h, Z, hZ, rfl⟩) (fun h Z hZ ↦ gram_r x _ ⟨h, Z, hZ, rfl⟩) _ g
      _ ≤ ∫⁻ γ : V.Γ, ∑' p, F p (γ • g) ∂.count :=
        lintegral_mono fun γ ↦ tsum_comp_le_tsum_of_injective sigma_mk_injective fun p ↦ F p (γ • g)
  refine ne_top_of_le_ne_top (mul_ne_top (mul_ne_top hC hω) (hB.measure_ne_top (μ := volume))) ?_
  calc
    ∫⁻ g, f g ∂V.quotMeasure ≤ ∫⁻ g, ∫⁻ γ : V.Γ, ∑' p, F p (γ • g) ∂.count ∂V.quotMeasure :=
      lintegral_mono fun g ↦ (hf g).elim fun x hx ↦ hx.trans (bases_le g x)
    _ = ∑' p, ∫⁻ g, F p g := by
      rw [lintegral_orbitMeasure_lintegral (.tsum F_meas),
        lintegral_tsum fun p ↦ (F_meas p).aemeasurable]
    -- Each pair `(x, T)` contributes at most `ω x` times the measure of `A x T * B`.
    _ ≤ ∑' p : Σ x, gram x, ω p.1 * volume B :=
      ENNReal.tsum_le_tsum fun p ↦ by grw [lintegral_indicator_const_le, measure_preimage_mul]
    _ = (∑' x, (gram x).encard * ω x) * volume B := by
      simp_rw [ENNReal.tsum_mul_right, ENNReal.tsum_sigma', tsum_set_const]
    _ ≤ C * (∑' x, 2 ^ (numInfPlaces E * ∑ i, ∑ j, (x i + x j).toNat) * ω x) * volume B := by
      grw [card_gram]
      simp [mul_assoc, ENNReal.tsum_mul_left]

/-- Let `M` and `Ω` be compact. There is a finite `C` such that, if `g` lies in the adelic unitary
group `G E s` and `Y` is a rational basis of profile `x` at the moved point `V.x * g`, then at most
`C * 4 ^ (numInfPlaces E * #t * ∑ (-x i)₊)` rational `n × t` matrices `ξ` satisfy
`(V.toRatCoords g)⁻¹ ξ ∈ Ω`, where `V.toRatCoords g = V.x * g * V.x⁻¹` and `numInfPlaces E` is the
number of infinite places. The hypothesis on `Y` means `(V.x * g)⁻¹ Y (dyadicDiag x)⁻¹ ∈ M`, for
the diagonal matrix `dyadicDiag x` with entries `2 ^ x i` at the infinite places and `1` at the
finite ones. -/
lemma Space.exists_encard_le_of_mem_profileBases {t : Type*} [Fintype t] {M : Set (GL n (𝔸 E))}
    (hM : IsCompact M) {Ω : Set (Matrix n t (𝔸 E))} (hΩ : IsCompact Ω) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {g : G E s} {x : n → ℤ} {Y : GL n E}, Y ∈ profileBases M x (V.move g).x →
      {ξ : Matrix n t E | (V.toRatCoords g).val⁻¹.val * ξ.map toAdele ∈ Ω}.encard ≤
        C * (2 ^ (numInfPlaces E * ∑ p : t × n, (-x p.2).toNat)) ^ 2 := by
  classical
  -- Row `i` of `Y⁻¹ ξ` is `2 ^ (-x i)` times row `i` of some `A⁻¹ * V.x⁻¹ * η` with `A ∈ M` and
  -- `η ∈ Ω`; these products lie in a compact set `B`.
  let B : Set (t × n → 𝔸 E) := (fun (A, η) (j, i) ↦ (A.inv * V.x.inv * η) i j) '' M ×ˢ Ω
  have hB : IsCompact B := (hM.prod hΩ).image_of_continuous _
  obtain ⟨C, hC, h_count⟩ := encard_le_of_dyadic_box (α := Matrix n t E) hB
  refine ⟨C, hC, fun {g x Y} hY ↦ ?_⟩
  have h_inj : Injective fun ξ : Matrix n t E ↦ (Y⁻¹.val * ξ).vec :=
    vec_bijective.injective.comp (mul_right_injective_of_invertible Y⁻¹.val)
  refine (h_count (fun p ↦ -x p.2) _ h_inj.injOn fun ξ hξ ↦ ?_).trans_eq (by simp [← pow_mul])
  let A : GL n (𝔸 E) := (V.move g).x⁻¹ * Y.map toAdele * (dyadicDiag x)⁻¹
  let η : Matrix n t (𝔸 E) := (V.toRatCoords g).val⁻¹.val * ξ.map toAdele
  refine ⟨(A, η), ⟨hY, hξ⟩, funext fun p ↦ ?_⟩
  simp [A, η, Core.dyadicDiag, move, toRatCoords, ← Matrix.map_mul, ← map_inv, Matrix.mul_assoc]

open Pointwise in
/-- Let `Ω` be a compact set of adelic `n × t` matrices, and suppose `2 * card t < card n` unless
`n` is empty. For `g` in the adelic unitary group `G E s`, count the rational `n × t` matrices `ξ`
with `(V.toRatCoords g)⁻¹ ξ ∈ Ω`, where `V.toRatCoords g = V.x * g * V.x⁻¹`. This count has a finite
integral over the quotient `V.Γ \ G` by the rational points, that is, against `V.quotMeasure`. -/
lemma Space.lintegral_encard_ne_top {t : Type*} [Fintype t] {Ω : Set (Matrix n t (𝔸 E))}
    (hΩ : IsCompact Ω) (h_rank : Nonempty n → 2 * card t < card n) :
    ∫⁻ g : G E s, {ξ : Matrix n t E | (V.toRatCoords g).val⁻¹.val * ξ.map toAdele ∈ Ω}.encard
      ∂V.quotMeasure ≠ ⊤ := by
  classical
  -- Reduction theory gives each `g` a profile `x : n → ℤ` of a rational basis. The count at `g` is
  -- at most a weight `ω x` times the number of bases of profile `x` at `g`, and `ω x` times the
  -- bound for the number of Gram matrices is summable over `x`.
  obtain ⟨M, c, hM, exists_basis⟩ := exists_isCompact_profileBases E n
  obtain ⟨B, hB⟩ := exists_perm_natAbs_add_le (s := s) hM c
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0∞, q ^ (2 : ℝ) = 2 ^ numInfPlaces E :=
    rpow_left_surjective two_ne_zero _
  have one_lt_q : 1 < q := (rpow_lt_rpow_iff two_pos).1 (by simp [hq, one_lt_pow₀])
  obtain ⟨C₁, hC₁, few_ξ⟩ := V.exists_encard_le_of_mem_profileBases hM hΩ
  let C₂ : ℝ≥0∞ := C₁ * 2 ^ (numInfPlaces E * (3 * ((card n + 1) ^ 2 * B)))
  -- `R` is the constant of Minkowski's first theorem. Up to a constant factor, `P x` bounds the
  -- number of Gram matrices of profile `x`.
  let R : ℝ≥0∞ := .ofReal (((2 * rootDiscr E) ^ numInfPlaces E) ^ card (n × n))
  let P (x : n → ℤ) : ℝ≥0∞ := 2 ^ (numInfPlaces E * ∑ i, ∑ j, (x i + x j).toNat)
  let ω (x : n → ℤ) : ℝ≥0∞ := (∏ i, q⁻¹ ^ (x i).natAbs) * (C₂ * R) / P x
  have h_geometric : ∑' k : ℤ, q⁻¹ ^ k.natAbs < ∞ :=
    lt_of_le_of_lt (le_of_add_le_left (tsum_nat_add_neg ENNReal.summable).ge)
      (by simp [ENNReal.tsum_add, one_lt_q])
  -- `P x` cancels the denominator of `ω x`; a product of geometric series in `q⁻¹ < 1` remains.
  have hω : ∑' x : n → ℤ, P x * ω x < ∞ :=
    calc
      _ ≤ (∏ _i : n, ∑' k : ℤ, q⁻¹ ^ k.natAbs) * (C₂ * R) := by
        grw [mul_div_le, ENNReal.tsum_mul_right, tsum_prod_le_prod_tsum fun k : ℤ ↦ q⁻¹ ^ k.natAbs]
      _ < ∞ := by simp [C₂, R, mul_lt_top_iff, Ne.lt_top, hC₁, ENNReal.pow_lt_top h_geometric]
  refine V.lintegral_ne_top_of_le_encard_profileBases (hM.mul isCompact_unitBoxGL) hω.ne fun g ↦ ?_
  obtain ⟨x, Y, hY, hx⟩ := exists_basis (V.move g).x
  obtain ⟨σ, hσ⟩ := hB (V.move g) x Y hY (hx (V.move g).ideleAbs_det_x.ge)
  -- Up to constants, `ν` is an upper bound for the count, `T` a lower one for the number of bases.
  let ν : ℝ≥0∞ := (2 ^ (numInfPlaces E * ∑ p : t × n, (-x p.2).toNat)) ^ 2
  let T : ℝ≥0∞ := (2 ^ (numInfPlaces E * ∑ p : n × n, (x p.1 - x p.2).toNat)) ^ 2
  have many_bases : T ≤ R * (profileBases (M * unitBoxGL E n) x (V.move g).x).encard :=
    two_pow_sq_le_encard_profileBases hY
  -- Compare exponents of `q`, where `q ^ 2 = 2 ^ numInfPlaces E`.
  have exponents : C₁ * ν * P x * q ^ ∑ i, (x i).natAbs ≤ C₂ * T :=
    calc
      _ = C₁ * q ^ (4 * (card t * ∑ i, (-x i).toNat) + 2 * ∑ i, ∑ j, (x i + x j).toNat +
            ∑ i, (x i).natAbs) := by
        simp [ν, P, pow_mul _ (numInfPlaces E), ← hq, sum_prod_type]
        ring
      _ ≤ C₁ * q ^ (4 * ∑ i, ∑ j, (x i - x j).toNat + 6 * ((card n + 1) ^ 2 * B)) := by
        grw [sum_toNat_neg_add_le h_rank hσ]
        exact one_lt_q.le
      _ = C₂ * T := by
        simp [C₂, T, pow_mul _ (numInfPlaces E), ← hq, sum_prod_type]
        ring
  refine ⟨x, ?_⟩
  calc
    _ ≤ C₁ * ν := few_ξ hY
    _ ≤ C₂ * T / (q ^ ∑ i, (x i).natAbs) / P x := by
      rwa [ENNReal.le_div_iff_mul_le (.inl (by positivity)) (.inr (by finiteness)),
        ENNReal.le_div_iff_mul_le (.inl (by positivity)) (.inr (by finiteness))]
    _ ≤ (profileBases (M * unitBoxGL E n) x (V.move g).x).encard * ω x := by
      grw [many_bases]
      simp only [ω, div_eq_mul_inv, prod_pow_eq_pow_sum, ENNReal.inv_pow]
      exact le_of_eq (by ring)

/-- The quotient `V.Γ \ G` of the adelic unitary group by its rational points has finite volume.

This is the finite volume theorem for adelic quotients in the case of unitary groups over CM
fields of hermitian forms with an adelic orthonormal frame, of any rank and signs. -/
instance Space.isFiniteMeasure_quotMeasure : IsFiniteMeasure V.quotMeasure := by
  -- The case `t = Empty`: there is exactly one matrix `ξ`, so the integrand is `1`.
  simpa [isFiniteMeasure_iff, lt_top_iff_ne_top, ENat.card, Cardinal.mk_eq_one] using
    V.lintegral_encard_ne_top (t := Empty) isCompact_univ (by simp [card_pos_iff])

end New

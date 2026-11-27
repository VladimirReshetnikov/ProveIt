import New.Spanning.RemainingTerms.ColumnLattice
import New.Spanning.RemainingTerms.FrameParts
import New.Spanning.RemainingTerms.LinkLattice
import New.Spanning.RemainingTerms.SchurTest

/-!
# Schur's test for one orbit

A term is a rational point `γ` of the unitary group with
`S.translateByClassReps c c' γ = h_c⁻¹ γ h_c'` integral. Its orbit is the double coset of `γ` under
the groups `New.Filling.classUnipotent₀` of unipotent elements of level `M = S.M` that fix the
frame. The amplitude majorants of the terms of an orbit are summed by Schur's test: the mean of the
sum of the weights over the orbit is reduced to a sum over a lattice, and then to the integral of a
kernel divided by the covolume of the lattice.

Throughout, `Λ` is the lattice of the class `c`, `A` is the isotropic space spanned by `e₁, …, e_ϱ`,
and `X₀` is the positive definite part of dimension `k`. For a term of cell rank `j`
(`New.Filling.HasCellRank`) put `i = min ϱ j`. The unit frame at an infinite place is the frame
rescaled by `New.Filling.basisScale`.

Notions from other files:
* `S.frameProducts γ`: the matrix of products of the frame `e₁, …, e_ϱ, z` with its image by `γ`.
* `S.HasCellRank j γ`: in `γ` a norm-one pair occurs from `j`, its leading minor of order `j` is
  nonzero, and `S.termDisc γ` is nonzero exactly when `j = ϱ + 1`.
* `S.schurWeight c' γ i y`: the boxed cutoff of `c'` at `γ⁻¹ y` times the product over the places of
  the powers `-(k + i)` of the ratio of volumes `volumeRatio`.
* `S.tailScale`: the number `α = b ^ (k f / 4)`, where `f` is the number of infinite places.

## Main definitions and results

* `New.Filling.tsum_orbit_le_of_isLatticeTranslate`: the frames of an orbit lie in at most
  `isotropicRowsIndex ^ k` cosets of a lattice.
* `New.Filling.exists_tsum_schurWeight_le`: from cosets to the lattice.
* `New.Filling.tsum_schurIntegral_le`: from the lattice to an integral.
* `New.Filling.sq_tsum_amplitudeMajorant_doubleCoset_le`,
  `New.Filling.tsum_amplitudeMajorant_orbit_le`: the test, and its form as a bound by
  `New.Filling.orbitBound`.
-/

namespace New.Filling

open MeasureTheory Matrix Fintype RealPlace ENNReal Real Pointwise Fin
  DoubleCoset AddSubgroup Finset LinearMap
open NumberField (InfinitePlace)

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
  [S.IsAdmissible] {j : Fin (𝔰.ϱ + 2)} {c c' : S.Classes} {s : S.ResidueGL} {γ : S.G E}

omit [S.IsAdmissible] in
/-- The terms of an orbit have the same cell rank: if `δ` lies in the double coset of `γ` under the
unipotent groups `classUnipotent₀` of `c` and `c'`, and `γ` has cell rank `j`, then so has `δ`. -/
lemma HasCellRank.of_mem_doubleCoset {δ : S.G E}
    (hδ : δ ∈ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'))
    (h_rank : S.HasCellRank j γ) : S.HasCellRank j δ := by
  obtain ⟨u, ⟨-, hu_bessel, -⟩, x, ⟨-, hx_bessel, -⟩, rfl⟩ := mem_doubleCoset.1 hδ
  have h_stable : S.HasCellRank j (u⁻¹⁻¹ * γ * x) ↔ S.HasCellRank j γ :=
    isStable_hasCellRank j u⁻¹ (inv_mem hu_bessel) x hx_bessel γ
  rw [inv_inv] at h_stable
  exact h_stable.2 h_rank

omit [S.IsAdmissible] in
/-- If `δ` lies in the orbit of `γ`, the double coset under the groups `classUnipotent₀` of the
classes `c` and `c'`, then `δ` and `γ` have the same matrix of products of the frame with its
image. -/
lemma frameProducts_eq_of_mem_doubleCoset {δ : S.G E}
    (hδ : δ ∈ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c')) :
    S.frameProducts δ = S.frameProducts γ := by
  obtain ⟨u, ⟨-, hu_frame⟩, x, ⟨-, hx_frame⟩, rfl⟩ := mem_doubleCoset.1 hδ
  obtain ⟨hu_bessel, hu_matrix⟩ := mem_besselU0_iff.1 (inv_mem hu_frame)
  obtain ⟨hx_bessel, hx_matrix⟩ := mem_besselU0_iff.1 hx_frame
  have h_gram : S.frameProducts (u⁻¹⁻¹ * γ * x) =
      (frameMatrix u⁻¹)ᴴ * S.frameProducts γ * frameMatrix x :=
    frameGram_inv_mul_mul hu_bessel hx_bessel
  simpa [hu_matrix, hx_matrix] using h_gram

omit [S.IsAdmissible] in
/-- The terms of an orbit lie over the same block `(c, s, c')`: if `γ ∈ S.termsOver c s c'` (its
translate by the class representatives is integral with residue `s`), then so is every `δ` in the
double coset of `γ` under `classUnipotent₀ c` and `classUnipotent₀ c'`. -/
lemma termsOver.of_mem_doubleCoset {δ : S.G E}
    (hδ : δ ∈ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'))
    (h_over : γ ∈ S.termsOver c s c') : δ ∈ S.termsOver c s c' := by
  obtain ⟨u, ⟨⟨-, hu_over⟩, -⟩, x, ⟨⟨-, hx_over⟩, -⟩, rfl⟩ := mem_doubleCoset.1 hδ
  simpa using termsOver.mul (.mul hu_over h_over) hx_over

omit [S.IsAdmissible] in
/-- For `δ` in the orbit of `γ`, the conjugate of each row `i` of middle coordinates of the frame
moved by `translateByClassReps c c' δ` differs from that for `γ` by `M` times an `Ô`-combination of
the conjugates of the isotropic rows of the products (`frameGram`) of the frame with its image under
`translateByClassReps c c' γ`. -/
lemma col_frameMiddle_sub_mem {δ : S.G E}
    (hδ : δ ∈ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c')) (i : 𝔰.MiddleIndex) :
    (frameMiddle (S.translateByClassReps c c' δ) - frameMiddle (S.translateByClassReps c c' γ))ᴴ.col
      i ∈
      S.ideleM • colLattice (Ô E)
        (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram (S.translateByClassReps c c' γ)))ᴴ := by
  -- Write `δ = u γ x`. The new frame is `u'` times the old one, where
  -- `u' = translateByClassReps c c u` is `u` in the basis of the lattice, and `M⁻¹ (u' - 1)` is
  -- integral.
  obtain ⟨u, ⟨hu_over, hu_frame⟩, x, ⟨-, hx_frame⟩, rfl⟩ := mem_doubleCoset.1 hδ
  let u' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := (S.translateByClassReps c c u).1.1
  have h_frame : frameImage (S.translateByClassReps c c' (u * γ * x)).1.1 =
      frameImage (S.translateByClassReps c c u * S.translateByClassReps c c' γ).1.1 := by
    -- `↓`: these rules must act before the products are reassociated.
    simp [↓frameImage_translateByClassReps, coe_translateByClassReps, classCoord,
      ↓frameImage_mul_of_mem_besselU0 hx_frame, ↓frameImage_mul, Matrix.mul_assoc]
  have h_int : IsIntMatrix (Ô E) (S.ideleM⁻¹ • (u' - 1)) :=
    (S.principalLevel_eq_unitaryLevel.le hu_over.2).2
  have h_star : star S.ideleM = S.ideleM := Units.ext (by simp [ideleM])
  -- The coefficients are the conjugates of row `i` of `M⁻¹ (u' - 1)` in the last block of columns;
  -- off this block the row agrees with the identity, as `u'` is unipotent.
  let row : Fin 𝔰.ϱ → 𝔸f E := fun a ↦ star ((S.ideleM⁻¹ • (u' - 1)) (.inr (.inl i)) (eStar a))
  refine ⟨_, ⟨row, fun a ↦ star_mem_Ô (h_int (.inr (.inl i)) (eStar a)), rfl⟩, ?_⟩
  let g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := (S.translateByClassReps c c' γ).1.1
  have h_unipotent (b : 𝔰.BesselIndex) (hb : ∀ a : Fin 𝔰.ϱ, b ≠ eStar a) :
      u' (.inr (.inl i)) b = if .inr (.inl i) = b then 1 else 0 :=
    apply_inr_of_mem_besselU (hu_frame.1.translateByClassReps_mem_besselU c) (.inl i) b hb
  -- The products of `e_a` with the frame of `g` are the coordinates of that frame along `e*_a`.
  have h_diff (b : Fin (𝔰.ϱ + 1)) : (frameMiddle (u' * g) - frameMiddle g) i b =
      ∑ a : Fin 𝔰.ϱ, u' (.inr (.inl i)) (eStar a) *
        isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram g) a b := by
    simp [mul_apply, frameGram, splitGram, h_unipotent, Matrix.one_apply]
  rw [frameMiddle, h_frame]
  funext b
  change _ = star ((frameMiddle (u' * g) - frameMiddle g) i b)
  rw [h_diff]
  simp [row, g, mulVec_eq_sum, h_star, ← Units.smul_def, mul_comm]

variable [HasPrimitiveRoot5040 E]

section

omit [HasPrimitiveRoot5040 E] [S.IsAdmissible]
/-- Two elements `δ`, `γ` of `S.G E` with the same matrix `frameProducts` have, at every infinite
place `v`, images `S.ratToInf δ v` and `S.ratToInf γ v` in `G₁` with the same matrix
`realFrameGram`. -/
lemma realFrameGram_ratToInf_congr {δ : S.G E} (hδ : S.frameProducts δ = S.frameProducts γ)
    {v : InfinitePlace E} : realFrameGram (S.ratToInf δ v) = realFrameGram (S.ratToInf γ v) := by
  ext a b
  simp [hδ]

/-- If `δ` has the same matrix `frameProducts` as `γ` and `u ∈ besselU0` (a unipotent element of
`G₁` fixing each frame vector), then at every infinite place `v`, `u⁻¹ * S.ratToInf δ v` has the
same matrix `realFrameGram` as `S.ratToInf γ v`. -/
lemma realFrameGram_inv_mul_ratToInf {u : 𝔰.G₁} (hu : u ∈ besselU0) {δ : S.G E}
    (hδ : S.frameProducts δ = S.frameProducts γ) {v : InfinitePlace E} :
    realFrameGram (u⁻¹ * S.ratToInf δ v) = realFrameGram (S.ratToInf γ v) := by
  simp [← realFrameGram_ratToInf_congr hδ, realFrameGram_mul_of_mem_besselFixer, hu,
    mem_besselFixer_of_mem_besselU0]

/-- At the infinite place `v`, take the leading `j × j` minor of `realFrameGram (S.ratToInf γ v)`,
the matrix of products in the unit frame. Its modulus is
`(|realM v| ^ ∑_{a < j} (ϱ - a)) ^ 2 / N ^ j` times `‖Φ v (leadingMinor (frameProducts γ) j)‖`. So
each index `a < j` contributes the square of its scale `basisScale`, which is
`realM v ^ (ϱ - a) / √N`. -/
lemma norm_det_submatrix_realFrameGram (v : InfinitePlace E) :
    ‖((realFrameGram (S.ratToInf γ v)).submatrix (castLE j.is_le) (castLE j.is_le)).det‖ =
      (|S.realM v| ^ ∑ a : Fin j, (𝔰.ϱ - a)) ^ 2 / S.N ^ j.1 *
        ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ := by
  have h_det :
      ((realFrameGram (S.ratToInf γ v)).submatrix (castLE j.is_le) (castLE j.is_le)).det =
        ↑(∏ a : Fin j, S.realM v ^ (2 * (𝔰.ϱ - castLE j.is_le a)) / S.N) *
          Φ v (leadingMinor (S.frameProducts γ) j) :=
    det_submatrix_realFrameGram_ratToInf ..
  rw [h_det, norm_mul, Complex.norm_real, Real.norm_eq_abs, Finset.prod_div_distrib, abs_div,
    abs_prod]
  simp [prod_pow_eq_pow_sum, ← pow_mul, sum_mul, mul_comm 2]

/-- If `γ` has cell rank `j`, the determinant of the products of `e₁, …, e_i, z` (`i = min ϱ j`)
with their images, in the unit frame at `v` (the matrix `subframeBlock`), has the modulus of the
rescaled leading minor of order `j` of `S.frameProducts γ`. -/
lemma HasCellRank.norm_det_subframeBlock (h_rank : S.HasCellRank j γ) (v : InfinitePlace E) :
    ‖(subframeBlock (min_le_left 𝔰.ϱ j) (realFrameGram (S.ratToInf γ v))).det‖ =
      (|S.realM v| ^ ∑ a : Fin j, (𝔰.ϱ - a)) ^ 2 / S.N ^ j.1 *
        ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ := by
  have h_pair : NormOnePairOccursFrom j (S.ratToInf γ v) := h_rank.normOnePairOccursFrom.ratToInf v
  rw [← norm_det_submatrix_realFrameGram]
  exact RealPlace.norm_det_subframeBlock (min_le_left 𝔰.ϱ j) (hZ := rfl) h_pair j.is_le
    (hij := rfl)

/-- A matrix product `P * M` with `P` integral has the conjugates of its rows in every `Ô`-module
that contains the conjugates of the rows of `M`. -/
lemma col_conjTranspose_mul_mem {m m' n : Type} [Fintype m] [DecidableEq m]
    {M : Matrix m n (𝔸f E)} {P : Matrix m' m (𝔸f E)} (hP : IsIntMatrix (Ô E) P)
    {K : Submodule (Ô E) (n → 𝔸f E)} (hM : ∀ r : m, Mᴴ.col r ∈ K) (i : m') :
    (P * M)ᴴ.col i ∈ K := by
  rw [conjTranspose_mul]
  exact colLattice_le hM ⟨Pᴴ.col i, fun r ↦ hP.conjTranspose r i, rfl⟩

variable (S j)

/-- The first `min ϱ j` indices of the isotropic vectors of the frame. -/
abbrev initialIsotropicIndex : Fin (min 𝔰.ϱ j) ↪ Fin 𝔰.ϱ := castLEEmb (min_le_left 𝔰.ϱ j)

/-- The diagonal matrix with entries `S.M / basisScale v (e_l)`, `l < min ϱ j`. It converts the
parameters of a shift, given in the rational frame, to the unit frame at the place `v`. -/
noncomputable def shiftScaling (v : InfinitePlace E) :
    Matrix (Fin (min 𝔰.ϱ j)) (Fin (min 𝔰.ϱ j)) ℂ :=
  diagonal fun l ↦ S.M / S.basisScale v (.inl (initialIsotropicIndex j l))

/-- The shift with parameter `x`: at each infinite place, the unipotent element with central
parameter `0` that acts on `X₀` as the product of the Eichler maps along `e₁, …, e_i`,
`i = min ϱ j`, with the parameters given by the rows of `(shiftScaling j v)ᴴ * x v`: the vectors
`x_l` multiplied by the conjugates of `S.M / basisScale v (e_l)`. -/
noncomputable def eichlerShift (x : InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ)
    (v : InfinitePlace E) : 𝔰.G₁ :=
  unipotentOf (inclMatrix ℂ (initialIsotropicIndex j) * ((S.shiftScaling j v)ᴴ * of (x v)), 0)

/-- The bound of `RealPlace.exists_majorant_volumeRatio_inv_pow` for the integral of the kernel at
the place `v`, times the Jacobian of the passage to the parameters of `eichlerShift`. -/
noncomputable def kernelBound (γ : S.G E) (v : InfinitePlace E) : ℝ :=
  ‖(S.shiftScaling j v).det‖⁻¹ ^ (2 * 𝔰.k) *
    ((2 * S.frameBoxRadius ^ 2) ^ ((min 𝔰.ϱ j + 1) * min 𝔰.ϱ j) *
      (2 ^ (min 𝔰.ϱ j + 1) * (S.b ^ (6 * 𝔰.n + 2)) ^ (2 * (j - min 𝔰.ϱ j))) ^ 𝔰.k /
      ‖(subframeBlock (min_le_left 𝔰.ϱ j) (realFrameGram (S.ratToInf γ v))).det‖ ^
        (𝔰.k + min 𝔰.ϱ j))

variable {S j}

/-- The columns of `l` lie in `Λ ∩ X₀`, where `Λ` is the lattice of the class `c`, and modulo the
isotropic space the frame of `p` is that of `p₀` moved in `X₀` by `S.M • l` times the first
`min ϱ j` rows of the matrix of products of `γ`. -/
def IsLatticeTranslate (c : S.Classes) (γ p₀ p : S.G E) (l : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E) :
    Prop :=
  IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix l) ∧
    (frameImage (p : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₂ =
      (frameImage (p₀ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₂ +
        fromRows (fromRows (S.M • (l * (isotropicRows (S.frameProducts γ)).submatrix
          (initialIsotropicIndex j) id)) 0) 0

@[fun_prop]
lemma measurable_eichlerShift : Measurable (S.eichlerShift j) := by
  have h_of : Continuous fun A : Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ ↦ of A := continuous_id
  unfold eichlerShift
  exact Continuous.measurable (by fun_prop)

/-- At every place a shift `eichlerShift` is a unipotent element that fixes the frame. -/
lemma eichlerShift_mem (x : InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ) (v : InfinitePlace E) :
    S.eichlerShift j x v ∈ besselU0 :=
  unipotentOf_mem_besselU0 _

/-- Let `p` be a lattice translate of `p₀` by `q`, for the lattice of the class `c` and the matrix
of products of `γ`. In the unit frame at the place `v`, the parts in `X₀` of the two frames
(`frameX₀Part`) differ by the conjugate transpose of the rescaled point `conjColumnsAtInfinity q`
times the first `min ϱ j` isotropic rows of products of `γ`. -/
lemma IsLatticeTranslate.frameX₀Part_eq {p p₀ : S.G E} {q : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E}
    (hq : IsLatticeTranslate c γ p₀ p q) (v : InfinitePlace E) :
    frameX₀Part (S.ratToInf p v) = frameX₀Part (S.ratToInf p₀ v) +
      ((S.shiftScaling j v)ᴴ * of (conjColumnsAtInfinity E 𝔰 (Fin (min 𝔰.ϱ j)) q v))ᴴ *
        (isotropicRows (realFrameGram (S.ratToInf γ v))).submatrix (initialIsotropicIndex j)
          id := by
  ext a b
  obtain ⟨-, hq_eq⟩ := hq
  have h_entry : p.1.1 (𝔰.indexX₀ a) (𝔰.besselFrame b) = p₀.1.1 (𝔰.indexX₀ a) (𝔰.besselFrame b) +
      S.M * ∑ l, q a l * S.frameProducts γ (initialIsotropicIndex j l).castSucc b := by
    have h_translate_entry := congrFun₂ hq_eq (.inl (.inl a)) b
    simpa [mul_apply] using h_translate_entry
  have h_term (l : Fin (min 𝔰.ϱ j)) :
      S.M * (Φ v (q a l) * Φ v (S.frameProducts γ (initialIsotropicIndex j l).castSucc b)) *
          S.basisScale v (𝔰.besselFrame b) =
        Φ v (q a l) * (S.M / S.basisScale v (.inl (initialIsotropicIndex j l))) *
          realFrameGram (S.ratToInf γ v) (initialIsotropicIndex j l).castSucc b := by
    have h_scale : S.basisScale v (.inl (initialIsotropicIndex j l)) =
        S.realM v ^ (𝔰.ϱ - initialIsotropicIndex j l) / √S.N := by simp [basisScale]
    have h_sqrt : (S.N : ℂ) = √S.N * √S.N := by
      rw [← Complex.ofReal_mul, mul_self_sqrt S.N.cast_nonneg, Complex.ofReal_natCast]
    have h_ne : (√S.N : ℂ) ≠ 0 := by simp [Nat.Prime.ne_zero]
    simp only [realFrameGram_ratToInf, basisScale_besselFrame, h_scale, val_castSucc]
    push_cast
    rw [h_sqrt]
    field_simp
  have h_one : S.basisScale v (𝔰.indexX₀ a) = 1 := by simp [basisScale]
  rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.add_apply, mul_apply]
  simp only [shiftScaling, mul_diagonal, conjTranspose_apply, of_apply, conjColumnsAtInfinity_apply,
    star_star, submatrix_apply, id_eq, ← h_term]
  simp [frameX₀Part, inclMatrix, mul_apply, Matrix.one_apply, h_entry, add_mul, mul_sum, sum_mul,
    h_one, -Nat.cast_mul]

/-- **The shifted points.** Let `p` be a lattice translate of `p₀` by `q`, both with the matrix of
products `frameProducts γ`. Let `u` lie in `besselU0`, and let `s` be `eichlerShift j x v`. Then the
parts in `X₀` (`frameX₀Part`) of the frames of `(u s)⁻¹ p` and of `u⁻¹ p₀` at `v` differ by a
product. The first factor is the conjugate transpose of the point `conjColumnsAtInfinity q + x`,
rescaled by `shiftScaling j v`. The second factor is the first `min ϱ j` isotropic rows of products
of `γ`. -/
lemma frameX₀Part_eichlerShift_inv_mul {p p₀ : S.G E} (hp : S.frameProducts p = S.frameProducts γ)
    (hp₀ : S.frameProducts p₀ = S.frameProducts γ) {q : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E}
    (hq : IsLatticeTranslate c γ p₀ p q) (v : InfinitePlace E) {u : 𝔰.G₁} (hu : u ∈ besselU0)
    (x : InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ) :
    frameX₀Part ((u * S.eichlerShift j x v)⁻¹ * S.ratToInf p v) =
      frameX₀Part (u⁻¹ * S.ratToInf p₀ v) +
        ((S.shiftScaling j v)ᴴ * of ((conjColumnsAtInfinity E 𝔰 (Fin (min 𝔰.ϱ j)) q + x) v))ᴴ *
          (isotropicRows (realFrameGram (S.ratToInf γ v))).submatrix (initialIsotropicIndex j)
            id := by
  obtain ⟨t, rfl⟩ : ∃ t : 𝔰.UnipotentParams, u = unipotentOf t :=
    mem_besselU0_iff_unipotentOf.1 hu
  have h_rows (Z : 𝔰.FrameMatrix) :
      (inclMatrix ℂ (initialIsotropicIndex j))ᴴ * isotropicRows Z = (isotropicRows Z).submatrix
        (initialIsotropicIndex j) id := by
    ext l b
    simp [inclMatrix, mul_apply, Matrix.one_apply]
  set Z : 𝔰.FrameMatrix := realFrameGram (S.ratToInf γ v) with hZ
  have h_moved : frameX₀Part ((unipotentOf t * S.eichlerShift j x v)⁻¹ * S.ratToInf p v) =
      frameX₀Part (S.ratToInf p v) + t.1ᴴ * isotropicRows Z +
        ((S.shiftScaling j v)ᴴ * of (x v))ᴴ * (isotropicRows Z).submatrix (initialIsotropicIndex j)
          id := by
    rw [_root_.mul_inv_rev, mul_assoc, eichlerShift, frameX₀Part_unipotentOf_inv_mul,
      realFrameGram_inv_mul_ratToInf hu hp, frameX₀Part_unipotentOf_inv_mul,
      realFrameGram_ratToInf_congr hp, conjTranspose_mul (inclMatrix ℂ _),
      Matrix.mul_assoc _ _ᴴ, h_rows]
  have h_base : frameX₀Part ((unipotentOf t)⁻¹ * S.ratToInf p₀ v) =
      frameX₀Part (S.ratToInf p₀ v) + t.1ᴴ * isotropicRows Z := by
    rw [frameX₀Part_unipotentOf_inv_mul, realFrameGram_ratToInf_congr hp₀]
  rw [h_moved, h_base, hq.frameX₀Part_eq, Pi.add_apply, ← of_add_of, Matrix.mul_add,
    conjTranspose_add, Matrix.add_mul]
  abel

/-- Two terms with the same matrix of products differ, in the middle part of the frame, by vectors
of `X₀`: in the basis of the lattice of `c`, the difference is `S.classCoordX₀ c` times the
difference of the rational coordinates in `X₀`, taken as finite adeles. -/
lemma frameMiddle_translateByClassReps_sub {p p' : S.G E}
    (hZ : S.frameProducts p' = S.frameProducts p) :
    frameMiddle (S.translateByClassReps c c' p') - frameMiddle (S.translateByClassReps c c' p) =
      S.classCoordX₀ c * finAdeleMatrix
        (frameMiddle (p' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) -
          frameMiddle (p : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₁ := by
  have hz_eq (b : Fin (𝔰.ϱ + 1)) :
      (p' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) 𝔰.z (𝔰.besselFrame b) =
        (p : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) 𝔰.z (𝔰.besselFrame b) := by
    simpa [frameGram, splitGram, middleGram, mul_apply, Nat.Prime.ne_zero] using
      congrFun₂ hZ 𝔰.top b
  ext r b
  simp [frameMiddle_translateByClassReps, hz_eq, mul_apply, mul_sub]

end

omit [HasPrimitiveRoot5040 E] in
/-- If `γ` has cell rank `j`, the products of `e₁, …, e_i, z` (`i = min ϱ j`) with their images
form an invertible matrix at every infinite place. -/
lemma HasCellRank.det_subframeBlock_ne_zero (h_rank : S.HasCellRank j γ) (v : InfinitePlace E) :
    (subframeBlock (min_le_left 𝔰.ϱ j) (realFrameGram (S.ratToInf γ v))).det ≠ 0 := by
  have hδ : 0 < ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ := by
    simpa using h_rank.leadingMinor_ne_zero
  have hκ : 1 ≤ |S.realM v| := one_le_abs_realM v
  have hN : 0 < S.N := S.N_prime.pos
  rw [← norm_pos_iff, h_rank.norm_det_subframeBlock]
  positivity

omit [S.IsAdmissible] [HasPrimitiveRoot5040 E] in
/-- Let `γ` have cell rank `j` (`HasCellRank`), let `ξ` be the first `min ϱ j` isotropic rows of
`frameProducts γ`, and let `p₀`, `p` have the same matrix of products as `γ`. Suppose the middle
parts (`frameMiddle`) of the frames moved by `translateByClassReps c c' p` and
`translateByClassReps c c' p₀` differ row by row by `M` times `Ô`-linear combinations of the rows of
`ξ`, taken as finite adeles (`finAdeleMatrix`). Then `p` is a lattice translate of `p₀`. -/
lemma HasCellRank.exists_isLatticeTranslate (h_rank : S.HasCellRank j γ) {p₀ p : S.G E}
    (hZ₀ : S.frameProducts p₀ = S.frameProducts γ) (hZ : S.frameProducts p = S.frameProducts γ)
    (h_rows : ∀ r : 𝔰.MiddleIndex,
      (frameMiddle (S.translateByClassReps c c' p) - frameMiddle
        (S.translateByClassReps c c' p₀))ᴴ.col r ∈
        S.ideleM • colLattice (Ô E)
          (finAdeleMatrix ((isotropicRows (S.frameProducts γ)).submatrix (initialIsotropicIndex j)
            id))ᴴ) :
    ∃ l : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E, IsLatticeTranslate c γ p₀ p l := by
  -- The rows of `ξ` are independent, so the adelic coefficients `W` come from a rational `l`.
  set ξ : Matrix (Fin (min 𝔰.ϱ j)) (Fin (𝔰.ϱ + 1)) E :=
    (isotropicRows (S.frameProducts γ)).submatrix (initialIsotropicIndex j) id with hξ
  let ξ' : Matrix (Fin (𝔰.ϱ + 1)) (Fin (min 𝔰.ϱ j)) E :=
    (paddedLeading j (S.frameProducts γ))⁻¹.submatrix id (castSucc ∘ initialIsotropicIndex j)
  have h_inv : ξ * ξ' = 1 := by
    ext a b
    have ha : a.val < j.val := a.2.trans_le (min_le_right _ _)
    simpa [hξ, ξ', paddedLeading, mul_apply, ha, Matrix.one_apply, Fin.ext_iff] using
      congrFun₂ h_rank.paddedLeading_mul_inv (initialIsotropicIndex j a).castSucc
        (initialIsotropicIndex j b).castSucc
  have h_eq : S.frameProducts p = S.frameProducts p₀ := hZ.trans hZ₀.symm
  set x : Matrix 𝔰.κ (Fin (𝔰.ϱ + 1)) E := (frameMiddle p.1.1 - frameMiddle p₀.1.1).toRows₁ with hx
  rw [frameMiddle_translateByClassReps_sub h_eq, ← colLattice_smul] at h_rows
  obtain ⟨W, hW_int, hW⟩ := exists_isIntMatrix_mul_eq_of_col_mem h_rows
  have h_adelic : S.classCoordX₀ c * finAdeleMatrix x = (S.M : 𝔸f E) • (Wᴴ * finAdeleMatrix ξ) := by
    rw [← conjTranspose_conjTranspose (S.classCoordX₀ c * finAdeleMatrix x), ← hW]
    simp [Units.smul_def, ideleM_val]
  let l : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E := (S.M : E)⁻¹ • (x * ξ')
  have hl : S.classCoordX₀ c * finAdeleMatrix l = Wᴴ := by
    have h_cancel : (((S.M : E)⁻¹ : E) : 𝔸f E) * (S.M : 𝔸f E) = 1 := by
      simpa [Nat.Prime.ne_zero, -Nat.cast_mul] using
        (map_mul (algebraMap E (𝔸f E)) (S.M : E)⁻¹ S.M).symm
    rw [finAdeleMatrix_smul, finAdeleMatrix_mul, Matrix.mul_smul, ← Matrix.mul_assoc, h_adelic,
      Matrix.smul_mul, Matrix.mul_assoc, ← finAdeleMatrix_mul, h_inv, smul_smul, h_cancel]
    simp
  have h_rational : x = S.M • (l * ξ) := by
    -- `classCoordX₀ c` has a left inverse, so it is enough to compare coordinates.
    have h_coords : S.classCoordX₀ c * finAdeleMatrix x =
        S.classCoordX₀ c * finAdeleMatrix ((S.M : E) • (l * ξ)) := by
      simp [h_adelic, finAdeleMatrix_smul, ← Matrix.mul_assoc, hl]
    rw [← Nat.cast_smul_eq_nsmul E]
    exact Matrix.map_injective (algebraMap E (𝔸f E)).injective
      (mul_right_injective_of_inv _ _ (gram_classCoordX₀ c) h_coords)
  refine ⟨l, by simpa only [hl] using hW_int.conjTranspose, ?_⟩
  rw [← hξ, ← h_rational]
  ext (⟨i | i⟩ | i) b
  · simp [hx]
  · simpa [frameGram, splitGram, middleGram, mul_apply, S.N_prime.ne_zero] using
      congrFun₂ h_eq 𝔰.top b
  · simpa [frameGram, mul_apply, Matrix.one_apply] using congrFun₂ h_eq i.castSucc b

omit [S.IsAdmissible] in
/-- Let `γ` have cell rank `j` and lie over the block `(c, s, c')`, let `Λ` be the lattice of the
class `c` and `A` the span of the isotropic vectors `e_a` of the frame. A term `p` is a lattice
translate of `p₀` by `l` if `l` has columns in `Λ ∩ X₀` and, modulo `A`, the frame of `p` is that of
`p₀` moved in `X₀` by `M l` times the first `min ϱ j` rows of products of `γ`. If the sum of `w` is
at most `bound` over every subset `B` of the orbit of `γ` that consists of translates of one of its
points, then the sum over the orbit is at most `isotropicRowsIndex ^ k * bound`, as the orbit falls
into at most `isotropicRowsIndex ^ k` such sets. -/
lemma tsum_orbit_le_of_isLatticeTranslate (h_over : γ ∈ S.termsOver c s c')
    (h_rank : S.HasCellRank j γ) (w : S.G E → ℝ≥0∞) (bound : ℝ≥0∞)
    (h_coset : ∀ B : Set (S.G E), B ⊆ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c') →
      ∀ p₀ ∈ B, ∀ l : S.G E → Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E,
        (∀ p ∈ B, IsLatticeTranslate c γ p₀ p (l p)) → ∑' p : B, w p ≤ bound) :
    ∑' p : doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'), w p ≤
      .ofReal (S.isotropicRowsIndex j (S.translateByClassReps c c' γ) ^ 𝔰.k) * bound := by
  classical
  -- The middle parts of the frames differ by `k` rows in a basis of `Λ ∩ X₀`. These rows lie in `M`
  -- times the larger lattice in the definition of `isotropicRowsIndex`; colour them modulo `M`
  -- times the smaller one. `a` is a basis of `Λ ∩ X₀`, and `Q` is an integral left inverse of its
  -- coordinates.
  obtain ⟨a, -, ha, Q, hQ, hQa⟩ :=
    exists_preimageLattice_eq_colLattice (R := Ô E) ⟨_, gram_classCoordX₀ c⟩
  -- `D p` is the change of the middle part of the frame from `γ` to `p`, and `Z` is the matrix of
  -- products of `γ` in the basis of the lattice.
  let D (p : S.G E) : Matrix 𝔰.MiddleIndex (Fin (𝔰.ϱ + 1)) (𝔸f E) :=
    frameMiddle (S.translateByClassReps c c' p) - frameMiddle (S.translateByClassReps c c' γ)
  let Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) (𝔸f E) :=
    (S.latticeMiddle (𝔸f E)).frameGram (S.translateByClassReps c c' γ)
  let latticeBelow : Submodule (Ô E) (Fin (𝔰.ϱ + 1) → 𝔸f E) :=
    colLattice (Ô E) (Z.submatrix (fun b : IndexBelow j ↦ b.1.castSucc) _root_.id)ᴴ
  have h_index : relIndex (S.ideleM • latticeBelow.toAddSubgroup)
      (S.ideleM • (colLattice (Ô E) (isotropicRows Z)ᴴ).toAddSubgroup) ≠ 0 :=
    ((relIndex_pointwise_smul S.ideleM ..).trans_gt (isotropicRowsIndex_pos h_over h_rank)).ne'
  have h_mem_all (p : S.G E) (hp : p ∈ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'))
      (i : 𝔰.κ) : (Q * D p)ᴴ.col i ∈ S.ideleM • colLattice (Ô E) (isotropicRows Z)ᴴ :=
    col_conjTranspose_mul_mem hQ (col_frameMiddle_sub_mem hp) i
  have h_card : card 𝔰.κ = 𝔰.k := by simp
  rw [isotropicRowsIndex, submoduleIndex, ← relIndex_pointwise_smul S.ideleM, ← h_card]
  refine tsum_le_relIndex_pow_mul (fun p ↦ (Q * D p)ᴴ.col) h_index h_mem_all w bound
    fun B hB p₀ hp₀ h_colour ↦ ?_
  have hZ {p : S.G E} (hp : p ∈ B) : S.frameProducts p = S.frameProducts γ :=
    frameProducts_eq_of_mem_doubleCoset (hB hp)
  have h_basis {p : S.G E} (hp : p ∈ B) : S.classCoordX₀ c * a.1 * (Q * D p) = D p := by
    have hQ_inv : Q * S.classCoordX₀ c = (a⁻¹).1 :=
      (Units.inv_eq_of_mul_eq_one_left (by rw [Matrix.mul_assoc, hQa])).symm
    simp [D, frameMiddle_translateByClassReps_sub (hZ hp), ← Matrix.mul_assoc Q, hQ_inv,
      Matrix.mul_assoc,
      ← Matrix.mul_assoc a.1]
  have h_rows_le : latticeBelow ≤ colLattice (Ô E)
    ((isotropicRows Z).submatrix (initialIsotropicIndex j) _root_.id)ᴴ :=
    colLattice_le fun ⟨b, hb⟩ ↦ col_mem_colLattice (⟨b, lt_min b.2 hb⟩ : Fin (min 𝔰.ϱ j))
  -- Two terms of one colour differ by `M` times the smaller lattice, so are lattice translates.
  have h_translate (p : S.G E) (hp : p ∈ B) :
      ∃ l : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E, IsLatticeTranslate c γ p₀ p l := by
    refine h_rank.exists_isLatticeTranslate (c' := c') (hZ hp₀) (hZ hp) fun r ↦ ?_
    have h_diff : frameMiddle (S.translateByClassReps c c' p) - frameMiddle
      (S.translateByClassReps c c' p₀) =
        S.classCoordX₀ c * a.1 * (Q * D p - Q * D p₀) := by
      rw [Matrix.mul_sub, h_basis hp, h_basis hp₀, sub_sub_sub_cancel_right]
    have h_mem (i : 𝔰.κ) : (Q * D p - Q * D p₀)ᴴ.col i ∈
        S.ideleM • colLattice (Ô E) ((isotropicRows Z).submatrix (initialIsotropicIndex j)
          _root_.id)ᴴ := by
      rw [conjTranspose_sub]
      exact Set.smul_set_mono h_rows_le (h_colour p hp p₀ hp₀ i)
    rw [h_diff]
    simpa [Z, frameGram_translateByClassReps] using! col_conjTranspose_mul_mem ha h_mem r
  choose! l hl using h_translate
  exact h_coset B hB p₀ hp₀ l hl

/-- Let the terms of `B` lie in the orbit of `γ` and be lattice translates of `p₀` with parameters
`l`. The frames of the terms with one lattice point `q` differ by vectors of the isotropic space. So
by packing, for `γ` over the block `(c, s, c')` and any exponent `i`, the sum of their weights
`schurWeight` at `y` is at most `tailScale` times a common bound `C` for the products over the
places of the powers `-(k + i)` of the ratios of the volumes (`volumeRatio`). -/
lemma tsum_schurWeight_fibre_le {B : Set (S.G E)}
    (hB : B ⊆ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c')) {p₀ : S.G E}
    {l : S.G E → Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E}
    (hl : ∀ p ∈ B, IsLatticeTranslate c γ p₀ p (l p))
    {y : NumberField.InfinitePlace E → 𝔰.G₁} (h_over : γ ∈ S.termsOver c s c')
    (q : Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E) {i : ℕ} {C : ℝ≥0∞}
    (hC : ∀ p ∈ B, l p = q →
      ∏ v : NumberField.InfinitePlace E,
        ENNReal.ofReal ((volumeRatio (S.ratToInf p v) (y v))⁻¹ ^ (𝔰.k + i)) ≤ C) :
    ∑' p : {p ∈ B | l p = q}, S.schurWeight c' p i y ≤ .ofReal S.tailScale * C := by
  have h_term (p : {p ∈ B | l p = q}) (_ : S.schurWeight c' p i y ≠ 0) :
      S.schurWeight c' p i y ≤ S.classCutoff c' ((S.ratToInf p)⁻¹ * y) * C := by
    obtain ⟨p, hp_mem, hp_point⟩ := p
    grw [schurWeight, boxCutoff, Set.indicator_le_self .., hC p hp_mem hp_point]
  have h_box (p : {p ∈ B | l p = q}) (hp : S.schurWeight c' p i y ≠ 0) :
      (S.ratToInf p)⁻¹ * y ∈ S.boxedPoints :=
    Set.mem_of_indicator_ne_zero (left_ne_zero_of_mul hp)
  -- `V` is the space of `n`-tuples of vectors of the isotropic space, seen from `y`.
  let V : Submodule ℝ (NumberField.InfinitePlace E → Fin 𝔰.n → EuclideanSpace ℂ 𝔰.BesselIndex) :=
    (piMap fun v ↦ Fintype.linearCombination ℂ (fun a : Fin 𝔰.ϱ ↦ frameVector (y v) a.castSucc)
      |>.restrictScalars ℝ |>.compLeft (Fin 𝔰.n)).range
  -- `10 ^ 5 * n ^ 9 * numInfPlaces E` is the exponent of `b` up to which `pow_le_tailScale` bounds
  -- by `S.tailScale`.
  have h_dim : 6 * 𝔰.n ^ 2 * Module.finrank ℝ V ≤ 10 ^ 5 * 𝔰.n ^ 9 * numInfPlaces E := by
    grw [finrank_range_le]
    simp [Module.finrank_pi_fintype]
    lia
  have h_differ (p : {p ∈ B | l p = q}) (_ : S.schurWeight c' p i y ≠ 0) (p₁ : {p ∈ B | l p = q})
      (_ : S.schurWeight c' p₁ i y ≠ 0) :
      (fun v ↦ frameVector ((S.ratToInf p v)⁻¹ * y v)) -
        (fun v ↦ frameVector ((S.ratToInf p₁ v)⁻¹ * y v)) ∈ V := by
    obtain ⟨p, hp_mem, hp_point⟩ := p
    obtain ⟨p₁, hp₁_mem, hp₁_point⟩ := p₁
    obtain ⟨-, hp_eq⟩ := hl p hp_mem
    obtain ⟨-, hp₁_eq⟩ := hl p₁ hp₁_mem
    have h_rows : (frameImage p.1.1).toRows₂ = (frameImage p₁.1.1).toRows₂ := by
      rw [hp_eq, hp₁_eq, hp_point, hp₁_point]
    exact ⟨_, funext₂ fun v _ ↦ (frameVector_sub_eq_sum h_rows ..).symm⟩
  have h_lie (p : {p ∈ B | l p = q}) (_ : S.schurWeight c' p i y ≠ 0) :
      p.1 ∈ S.termsOver c s c' :=
    termsOver.of_mem_doubleCoset (hB p.2.1) h_over
  have h_size (p : {p ∈ B | l p = q}) (hp : S.schurWeight c' p i y ≠ 0)
      (v : NumberField.InfinitePlace E) :
      besselLength (((S.ratToInf p)⁻¹ * y) v) ≤ S.b ^ (6 * 𝔰.n + 2) * 1 :=
    (inCut_of_mem_boxedPoints (h_box p hp) v).trans_eq (mul_one _).symm
  refine (tsum_le_of_le_classCutoff_mul le_rfl (fun _ ↦ Subtype.ext) h_lie h_size h_term
    h_differ).trans ?_
  grw [one_pow, mul_one, ← pow_mul, pow_le_tailScale h_dim]

omit [HasPrimitiveRoot5040 E] in
/-- **The kernel at one place.** Let `γ` have cell rank `j`, let `i = min ϱ j`, let `y` be boxed,
and let `Z` be the matrix of products of `γ` in the unit frame at `v`. Let `g₀` have the products
`Z`, with a norm-one pair from `j`. There is a measurable `φ` on `X₀ ^ i` with integral at most
`kernelBound j γ v` such that `volumeRatio g (y v) ^ (-(k + i)) ≤ φ A` for every `g` with the same
two properties whose frame differs in `X₀` from that of `g₀` by the rescaled point `A` times the
first `i` rows of `Z`. -/
lemma HasCellRank.exists_majorant_lintegral_le_kernelBound (h_rank : S.HasCellRank j γ)
    {y : InfinitePlace E → 𝔰.G₁} (hy : y ∈ S.boxedPoints) (v : InfinitePlace E) {g₀ : 𝔰.G₁}
    (hg₀_gram : realFrameGram g₀ = realFrameGram (S.ratToInf γ v))
    (hg₀_pair : NormOnePairOccursFrom j g₀) :
    ∃ φ : (Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ) → ℝ≥0∞, Measurable φ ∧
      ∫⁻ A : Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ, φ A ≤ .ofReal (S.kernelBound j γ v) ∧
      ∀ (g : 𝔰.G₁) (A : Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ),
        realFrameGram g = realFrameGram (S.ratToInf γ v) → NormOnePairOccursFrom j g →
        frameX₀Part g = frameX₀Part g₀ + ((S.shiftScaling j v)ᴴ * of A)ᴴ *
          (isotropicRows (realFrameGram (S.ratToInf γ v))).submatrix (initialIsotropicIndex j) id →
        .ofReal ((volumeRatio g (y v))⁻¹ ^ (𝔰.k + min 𝔰.ϱ j)) ≤ φ A := by
  have h_box : y v ∈ frameBox S.frameBoxRadius := mem_frameBox_of_mem_boxedPoints hy v
  have h_cut : InCut (y v) S.b := inCut_of_mem_boxedPoints hy v
  have h_seven : 7 ≤ 𝔰.k := by
    have h_base : 2 ^ 9 ≤ (2 * 𝔰.ϱ + 2) ^ 9 := Nat.pow_le_pow_left (by lia) 9
    grind [S.pow_le_k]
  have h_block : (subframeBlock (min_le_left 𝔰.ϱ j) (realFrameGram (S.ratToInf γ v))).det ≠ 0 :=
    h_rank.det_subframeBlock_ne_zero v
  obtain ⟨φ₀, h_meas, h_int, h_le⟩ := exists_majorant_volumeRatio_inv_pow (min_le_left 𝔰.ϱ j)
    h_box h_cut j.is_le (hij := rfl) h_seven hg₀_gram hg₀_pair h_block
  -- Pass to the parameters of the shift; the term `+ 0` is the form that `lintegral_comp_mul_add`
  -- takes.
  refine ⟨fun A ↦ φ₀ ((S.shiftScaling j v)ᴴ * of A + 0), h_meas.comp (Continuous.measurable ?_),
    ?_, fun g A hg_gram hg_pair hg_part ↦ h_le g _ hg_gram hg_pair ?_⟩
  · have h_of : Continuous fun A : Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ ↦ of A := continuous_id
    show Continuous fun A : Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ ↦ (S.shiftScaling j v)ᴴ * of A + 0
    fun_prop
  · -- The change of variables brings in the Jacobian that `kernelBound` carries.
    have h_det : (S.shiftScaling j v)ᴴ.det ≠ 0 := by
      simp [shiftScaling, basisScale, prod_eq_zero_iff, Nat.Prime.ne_zero]
    have h_card : card 𝔰.κ = 𝔰.k := by simp
    refine (lintegral_comp_mul_add h_det 0 h_meas).trans_le ?_
    grw [h_int, det_conjTranspose, norm_star, h_card, kernelBound, ofReal_mul (by positivity)]
  · rw [hg_part, Matrix.add_mul, Matrix.mul_assoc, mul_inclMatrix ((isotropicRows _).submatrix _ _)]
    congr 2
    · exact congrArg conjTranspose (add_zero _).symm
    · ext a b
      simp

/-- **From cosets to a lattice.** Let `γ` be a term of cell rank `j` over the block `(c, s, c')`,
let `i = min ϱ j` and let `Λ` be the lattice of `c`. Let `B` be a set of terms of the orbit of `γ`,
each a lattice translate of `p₀ ∈ B`: the matrix `l p` has columns in `Λ ∩ X₀` and, modulo the
isotropic space, the frame of `p` is that of `p₀` moved in `X₀` by `M * l p` times the first `i`
rows of products of `γ`. Let `u v` be unipotent and fix the frame at every place `v`, and let `y` be
boxed. There is a measurable `φ` whose integral is at most the product of the explicit numbers
`kernelBound j γ v`, which bound the integrals of its local factors, such that for every `x` the sum
over `B` of the weights `schurWeight` at `u * eichlerShift j x * y` is at most `S.tailScale` times
the sum of `φ` over the translate by `x` of the lattice `(Λ ∩ X₀) ^ i` (`columnLattice`). -/
lemma exists_tsum_schurWeight_le {B : Set (S.G E)}
    (hB : B ⊆ doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c')) {p₀ : S.G E}
    (hp₀ : p₀ ∈ B) {l : S.G E → Matrix 𝔰.κ (Fin (min 𝔰.ϱ j)) E}
    (hl : ∀ p ∈ B, IsLatticeTranslate c γ p₀ p (l p)) {u y : NumberField.InfinitePlace E → 𝔰.G₁}
    (hu : ∀ v : NumberField.InfinitePlace E, u v ∈ besselU0)
    (h_over : γ ∈ S.termsOver c s c') (h_rank : S.HasCellRank j γ) (hy : y ∈ S.boxedPoints) :
    ∃ φ : (NumberField.InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ) → ℝ≥0∞, Measurable φ ∧
      ∫⁻ x : NumberField.InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ, φ x ≤
        ∏ v : NumberField.InfinitePlace E, .ofReal (S.kernelBound j γ v) ∧
      ∀ x : NumberField.InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ,
        ∑' p : B, S.schurWeight c' p (min 𝔰.ϱ j) (u * S.eichlerShift j x * y) ≤
          .ofReal S.tailScale * ∑' w : S.columnLattice (Fin (min 𝔰.ϱ j)) c, φ (w +ᵥ x) := by
  -- `φ` is the product of the kernels at the places for the base point `u⁻¹ p₀`. The terms with one
  -- lattice point are then summed by packing.
  have hZ {p : S.G E} (hp : p ∈ B) : S.frameProducts p = S.frameProducts γ :=
    frameProducts_eq_of_mem_doubleCoset (hB hp)
  have h_pair {p : S.G E} (hp : p ∈ B) (v : InfinitePlace E) {g : 𝔰.G₁} (hg : g ∈ besselU0) :
      NormOnePairOccursFrom j (g⁻¹ * S.ratToInf p v) :=
    ((h_rank.of_mem_doubleCoset (hB hp)).normOnePairOccursFrom.ratToInf v).besselU_mul
      (inv_mem hg.1)
  choose φ₀ hφ₀_meas hφ₀_int hφ₀_le using fun v : InfinitePlace E ↦
    h_rank.exists_majorant_lintegral_le_kernelBound hy v
      (realFrameGram_inv_mul_ratToInf (hu v) (hZ hp₀)) (h_pair hp₀ v (hu v))
  refine ⟨fun x ↦ ∏ v : InfinitePlace E, φ₀ v (x v),
    Finset.measurable_prod _ fun v _ ↦ (hφ₀_meas v).comp (measurable_pi_apply v), ?_, fun x ↦ ?_⟩
  · rw [volume_pi, lintegral_pi_prod _ hφ₀_meas]
    exact Finset.prod_le_prod fun v _ ↦ hφ₀_int v
  -- The kernel at the shifted lattice point of `p` bounds the ratio of the volumes of `p`.
  have h_ratio {p : S.G E} (hp : p ∈ B) (v : InfinitePlace E) :
      .ofReal ((volumeRatio (S.ratToInf p v) (u v * S.eichlerShift j x v * y v))⁻¹ ^
          (𝔰.k + min 𝔰.ϱ j)) ≤ φ₀ v ((conjColumnsAtInfinity E 𝔰 _ (l p) + x) v) := by
    have h_shift : u v * S.eichlerShift j x v ∈ besselU0 := mul_mem (hu v) (eichlerShift_mem x v)
    rw [volumeRatio_mul_left _ h_shift]
    exact hφ₀_le v _ _ (realFrameGram_inv_mul_ratToInf h_shift (hZ hp)) (h_pair hp v h_shift)
      (frameX₀Part_eichlerShift_inv_mul (hZ hp) (hZ hp₀) (hl p hp) v (hu v) x)
  -- Sort the terms by their lattice point and sum each fibre by packing.
  let point (p : B) : S.columnLattice (Fin (min 𝔰.ϱ j)) c :=
    ⟨conjColumnsAtInfinity E 𝔰 _ (l p), mem_columnLattice.2 ⟨l p, (hl p p.2).1, rfl⟩⟩
  rw [← ENNReal.tsum_fiberwise _ point, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun ⟨_, q, hq_int, rfl⟩ ↦ ?_
  let f (p : point ⁻¹' {⟨conjColumnsAtInfinity E 𝔰 _ q, ⟨q, hq_int, rfl⟩⟩}) : {p ∈ B | l p = q} :=
    ⟨p.1, p.1.2, conjColumnsAtInfinity_injective (congrArg Subtype.val p.2)⟩
  have hf : Function.Injective f := fun _ _ h_eq ↦
    Subtype.ext (Subtype.ext (congrArg Subtype.val h_eq :))
  refine (tsum_comp_le_tsum_of_injective (f := f) hf
    fun r ↦ S.schurWeight c' r (min 𝔰.ϱ j) (u * S.eichlerShift j x * y)).trans ?_
  refine tsum_schurWeight_fibre_le hB hl h_over q fun p hp hq ↦ ?_
  subst hq
  exact Finset.prod_le_prod fun v _ ↦ h_ratio hp v

omit [S.IsAdmissible] [HasPrimitiveRoot5040 E] in
/-- The matrix `shiftScaling j v` is diagonal with entries `M / basisScale v (e_l)` for `l < i`. The
absolute value of its determinant is `(M √N) ^ i / |realM v| ^ ∑_{a < j} (ϱ - a)`, where
`i = min ϱ j`, `M = S.M` is the level, `N = S.N` is the number with `h(z, z) = -N`, and `S.realM v`
is the ratio of consecutive scales `basisScale` of the isotropic vectors. -/
lemma norm_det_shiftScaling (v : NumberField.InfinitePlace E) :
    ‖(S.shiftScaling j v).det‖ =
      (S.M * √S.N) ^ min 𝔰.ϱ j / |S.realM v| ^ ∑ a : Fin j, (𝔰.ϱ - a) := by
  -- The index `ϱ`, if it is below `j`, contributes `0` to the exponent.
  have h_exp : ∑ l : Fin (min 𝔰.ϱ j), (𝔰.ϱ - l) = ∑ a : Fin j, (𝔰.ϱ - a) := by
    refine sum_of_injective (castLE (min_le_right 𝔰.ϱ j)) (castLE_injective _) _ _
      (fun a ha ↦ ?_) fun _ ↦ rfl
    by_contra h_ne
    have ha_lt : a.val < min 𝔰.ϱ j := by lia
    exact ha ⟨⟨a, ha_lt⟩, rfl⟩
  have h_entry (l : Fin (min 𝔰.ϱ j)) :
      ‖(S.M / S.basisScale v (.inl (initialIsotropicIndex j l)) : ℂ)‖ =
        S.M * √S.N / |S.realM v| ^ (𝔰.ϱ - l) := by
    simp [basisScale, abs_of_nonneg, div_div_eq_mul_div, -Nat.cast_mul]
  rw [shiftScaling, det_diagonal, norm_prod, ← h_exp]
  simp only [h_entry]
  simp [prod_pow_eq_pow_sum, -Nat.cast_mul]

omit [HasPrimitiveRoot5040 E] in
/-- Let `γ` have cell rank `j ≥ 1`, let `i = min ϱ j`, and let `δ` be the image of the leading minor
of order `j` of `S.frameProducts γ` under the chosen embedding `Φ v` at the place `v`. The number
`kernelBound j γ v`, which bounds the integral over `X₀ ^ i` of the kernel of Schur's test at `v`,
is at most `((2 ρ²) ^ (i + 1) N ^ j / |δ|) ^ i` times the main factor
`((b ^ 13 / M²) ^ i N ^ (j - ϱ) / |δ|) ^ k`. Here `ρ = frameBoxRadius = b ^ (37 n)`, and the
truncated difference `j - ϱ` is `1` at the top rank `j = ϱ + 1` and `0` below. -/
lemma kernelBound_le (h_rank : S.HasCellRank j γ) (hj : j ≠ 0) (v : NumberField.InfinitePlace E) :
    S.kernelBound j γ v ≤
      ((2 * S.frameBoxRadius ^ 2) ^ (min 𝔰.ϱ j + 1) * S.N ^ j.1 /
          ‖Φ v (leadingMinor (S.frameProducts γ) j)‖) ^ min 𝔰.ϱ j *
        ((S.b ^ 13 / S.M ^ 2) ^ min 𝔰.ϱ j * S.N ^ (j - 𝔰.ϱ) /
          ‖Φ v (leadingMinor (S.frameProducts γ) j)‖) ^ 𝔰.k := by
  have hb : 2 ≤ S.b := two_le_b
  have hM : 2 ≤ S.M := two_le_M
  have hN : 0 < S.N := S.N_prime.pos
  have hδ : 0 < ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ := by
    simpa using h_rank.leadingMinor_ne_zero
  rw [kernelBound, h_rank.norm_det_subframeBlock, norm_det_shiftScaling]
  set δ : ℝ := ‖Φ v (leadingMinor (S.frameProducts γ) j)‖
  set θ : ℝ := S.b ^ (6 * 𝔰.n + 2) with hθ
  set w : ℝ := |S.realM v| ^ ∑ a : Fin j, (𝔰.ϱ - a)
  set i : ℕ := min 𝔰.ϱ j with hi
  have hw : 1 ≤ w := one_le_pow₀ (one_le_abs_realM v)
  have h_extra : j - i = j - 𝔰.ϱ := by lia
  -- The last column: `2 ^ (i + 1) θ ^ (2 (j - i)) ≤ b ^ (13 i)`, as `i ≥ 1`, and `i = ϱ` is
  -- large if `j > i`: then `2 ^ (i + 1) ≤ b ^ (i - 17)`, as `2 ^ 2 ≤ b`.
  have h_last : 2 ^ (i + 1) * θ ^ (2 * (j - 𝔰.ϱ)) ≤ (S.b ^ 13) ^ i := by
    have h_four : 2 ^ 2 ≤ S.b := by linarith [S.thousand_le_b]
    have h_exp : i - 17 * (j - 𝔰.ϱ) + (6 * 𝔰.n + 2) * (2 * (j - 𝔰.ϱ)) ≤ 13 * i := by
      obtain h_zero | h_one : j - 𝔰.ϱ = 0 ∨ j - 𝔰.ϱ = 1 := by lia
      · grind
      · grind [S.ten_pow_five_le_varrho]
    have h_two : i + 1 ≤ 2 * (i - 17 * (j - 𝔰.ϱ)) := by
      grind [S.ten_pow_five_le_varrho, val_ne_zero_iff.2 hj]
    calc 2 ^ (i + 1) * θ ^ (2 * (j - 𝔰.ϱ))
        ≤ (2 ^ 2) ^ (i - 17 * (j - 𝔰.ϱ)) * θ ^ (2 * (j - 𝔰.ϱ)) := by
          grw [pow_le_pow_right₀ one_le_two h_two, pow_mul 2]
      _ ≤ S.b ^ (i - 17 * (j - 𝔰.ϱ)) * θ ^ (2 * (j - 𝔰.ϱ)) := by gcongr
      _ = S.b ^ (i - 17 * (j - 𝔰.ϱ) + (6 * 𝔰.n + 2) * (2 * (j - 𝔰.ϱ))) := by
          rw [hθ, ← pow_mul, ← pow_add]
      _ ≤ (S.b ^ 13) ^ i := by grw [← pow_mul, pow_le_pow_right₀ S.one_le_b h_exp]
  -- The power `w` of `|realM v|` from the scales of the unit frame cancels in the `k`-th power and
  -- is dropped in the `i`-th power.
  have h_power : (S.N : ℝ) ^ j.1 = S.N ^ (j - 𝔰.ϱ) * S.N ^ i := by
    rw [← pow_add, ← h_extra, Nat.sub_add_cancel (min_le_right _ _)]
  have h_jacobian : ((S.M * √S.N) ^ i / w)⁻¹ ^ 2 = w ^ 2 / ((S.M ^ 2) ^ i * S.N ^ i) := by
    rw [inv_div, div_pow, pow_right_comm _ i 2, mul_pow, sq_sqrt (by positivity), mul_pow]
  calc ((S.M * √S.N) ^ i / w)⁻¹ ^ (2 * 𝔰.k) *
        ((2 * S.frameBoxRadius ^ 2) ^ ((i + 1) * i) * (2 ^ (i + 1) * θ ^ (2 * (j - i))) ^ 𝔰.k /
          (w ^ 2 / S.N ^ j.1 * δ) ^ (𝔰.k + i))
    _ = ((2 * S.frameBoxRadius ^ 2) ^ (i + 1) * S.N ^ j.1 / (w ^ 2 * δ)) ^ i *
        (2 ^ (i + 1) * θ ^ (2 * (j - 𝔰.ϱ)) * S.N ^ (j - 𝔰.ϱ) / ((S.M ^ 2) ^ i * δ)) ^ 𝔰.k := by
      rw [h_extra, pow_mul _ 2 𝔰.k, h_jacobian, pow_mul _ (i + 1), pow_add _ 𝔰.k, h_power]
      simp only [div_pow, mul_pow]
      field_simp
    _ ≤ ((2 * S.frameBoxRadius ^ 2) ^ (i + 1) * S.N ^ j.1 / (1 ^ 2 * δ)) ^ i *
        ((S.b ^ 13) ^ i * S.N ^ (j - 𝔰.ϱ) / ((S.M ^ 2) ^ i * δ)) ^ 𝔰.k := by gcongr
    _ = _ := by ring

omit [S.IsAdmissible] [HasPrimitiveRoot5040 E] in
lemma kernelBound_nonneg (hb : 0 ≤ S.b) (v : NumberField.InfinitePlace E) :
    0 ≤ S.kernelBound j γ v := by
  unfold kernelBound
  positivity

omit [HasPrimitiveRoot5040 E] in
/-- Let `γ` be a term of cell rank `j ≥ 1` over the block `(c, s, c')` and let `i = min ϱ j`. The
number `kernelBound j γ v` bounds the integral over `X₀ ^ i` of the kernel of Schur's test at the
place `v`. Its product over the `f` infinite places is at most
`tailScale * (b ^ 13 / M²) ^ (i k f) * minorNorm ^ (-k / 2)`, where `minorNorm` is the absolute norm
of the leading minor of order `j` of `S.frameProducts γ`, divided by `N ^ (2 f)` if `j = ϱ + 1`. -/
lemma prod_kernelBound_le (h_over : γ ∈ S.termsOver c s c') (h_rank : S.HasCellRank j γ)
    (hj : j ≠ 0) :
    ∏ v : NumberField.InfinitePlace E, S.kernelBound j γ v ≤
      S.tailScale * (S.b ^ 13 / S.M ^ 2) ^ (min 𝔰.ϱ j * 𝔰.k * numInfPlaces E) *
        (√(S.minorNorm j γ))⁻¹ ^ 𝔰.k := by
  have hb : 2 ≤ S.b := two_le_b
  have hN : 0 < S.N := S.N_prime.pos
  set P : ℝ := ∏ v, ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ with hP
  -- The minor is a nonzero integer of `E`.
  have h_one_le : 1 ≤ P := one_le_prod_norm_Φ (.det fun a b ↦ isIntegral_frameProducts h_over ..)
    h_rank.leadingMinor_ne_zero
  have h_sqrt : √(S.minorNorm j γ) = P / (S.N ^ (j - 𝔰.ϱ)) ^ numInfPlaces E := by
    rw [minorNorm, abs_norm_eq_prod_norm_sq, prod_pow, mul_assoc, pow_mul', ← div_pow,
      sqrt_sq (by positivity), pow_mul]
  have h_small : (((2 * S.frameBoxRadius ^ 2) ^ (min 𝔰.ϱ j + 1) * S.N ^ j.1) ^ numInfPlaces E / P) ^
      min 𝔰.ϱ j ≤ S.tailScale := by
    have h_exp : (37 * 𝔰.n * 2 + 1) * (min 𝔰.ϱ j + 1) + 60 * 𝔰.n * j ≤ 135 * 𝔰.n ^ 2 := by
      have h_min : min 𝔰.ϱ j + 1 ≤ 𝔰.n := Nat.succ_le_succ (min_le_left 𝔰.ϱ j)
      have h_le : j.1 ≤ 𝔰.n := j.is_le
      have h_sq : 𝔰.n ≤ 𝔰.n ^ 2 := Nat.le_self_pow two_ne_zero 𝔰.n
      calc _ ≤ (37 * 𝔰.n * 2 + 1) * 𝔰.n + 60 * 𝔰.n * 𝔰.n := by gcongr
        _ = 134 * 𝔰.n ^ 2 + 𝔰.n := by ring
        _ ≤ 135 * 𝔰.n ^ 2 := by linarith
    -- Here `frameBoxRadius = b ^ (37 n)`, `2 ≤ b` and `N ≤ b ^ (60 n)`.
    have h_base : (2 * S.frameBoxRadius ^ 2) ^ (min 𝔰.ϱ j + 1) * S.N ^ j.1 ≤
        S.b ^ (135 * 𝔰.n ^ 2) := by
      grw [frameBoxRadius, hb, N_le, ← pow_mul, ← pow_succ', ← pow_mul, ← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ S.one_le_b h_exp
    calc _ ≤ ((S.b ^ (135 * 𝔰.n ^ 2)) ^ numInfPlaces E) ^ min 𝔰.ϱ j := by
          grw [← h_one_le, div_one, h_base]
      _ ≤ S.b ^ (135 * 𝔰.n ^ 2 * numInfPlaces E * 𝔰.ϱ) := by
          rw [← pow_mul, ← pow_mul, ← mul_assoc]
          exact pow_le_pow_right₀ S.one_le_b (by grw [min_le_left])
      _ ≤ S.tailScale := pow_le_tailScale (by lia)
  calc ∏ v : InfinitePlace E, S.kernelBound j γ v
      ≤ ∏ v : InfinitePlace E, ((2 * S.frameBoxRadius ^ 2) ^ (min 𝔰.ϱ j + 1) * S.N ^ j.1 /
            ‖Φ v (leadingMinor (S.frameProducts γ) j)‖) ^ min 𝔰.ϱ j *
          ((S.b ^ 13 / S.M ^ 2) ^ min 𝔰.ϱ j * S.N ^ (j - 𝔰.ϱ) /
            ‖Φ v (leadingMinor (S.frameProducts γ) j)‖) ^ 𝔰.k :=
        prod_le_prod₀ (fun v _ ↦ kernelBound_nonneg b_pos.le v) fun v _ ↦ kernelBound_le h_rank hj v
    _ = (((2 * S.frameBoxRadius ^ 2) ^ (min 𝔰.ϱ j + 1) * S.N ^ j.1) ^ numInfPlaces E / P) ^
          min 𝔰.ϱ j * (((S.b ^ 13 / S.M ^ 2) ^ min 𝔰.ϱ j * S.N ^ (j - 𝔰.ϱ)) ^
            numInfPlaces E / P) ^ 𝔰.k := by
        rw [prod_mul_distrib, prod_pow, prod_pow, Finset.prod_div_distrib, Finset.prod_div_distrib,
          Finset.prod_const, Finset.prod_const, card_univ]
    _ ≤ S.tailScale * (((S.b ^ 13 / S.M ^ 2) ^ min 𝔰.ϱ j * S.N ^ (j - 𝔰.ϱ)) ^
          numInfPlaces E / P) ^ 𝔰.k := by grw [h_small]
    _ = _ := by
        rw [h_sqrt, inv_div]
        ring

omit [S.IsAdmissible] [HasPrimitiveRoot5040 E] in
/-- The sum of the weights `schurWeight` over the orbit of `γ` is left invariant under the
subgroup `classUnipotent₀ c`, which permutes the orbit and fixes the frame. -/
lemma tsum_schurWeight_ratToInf_mul {i : ℕ} {u : S.G E} (hu : u ∈ S.classUnipotent₀ c)
    (y : NumberField.InfinitePlace E → 𝔰.G₁) :
    ∑' p : doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'),
        S.schurWeight c' p i (S.ratToInf u * y) =
      ∑' p : doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'),
        S.schurWeight c' p i y := by
  set orbit : Set (S.G E) := doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c') with h_orbit
  have h_image : (fun p : S.G E ↦ u • p) '' orbit = orbit := by
    rw [Set.image_smul, h_orbit, doubleCoset, ← smul_mul_assoc, ← smul_mul_assoc, smul_coe_set hu]
  conv_lhs => rw [← h_image, tsum_image (S.schurWeight c' · _ _) (by simp)]
  simp [schurWeight, volumeRatio, frameVolume_mul_left, ratToInf_mem_besselU0 hu.2]

set_option synthInstance.maxHeartbeats 200000 in
/-- **From the lattice to an integral.** Let `γ` have cell rank `j ≥ 1` (`HasCellRank`) and lie in
`termsOver c s c'`.

One factor `schurIntegral` of Schur's test (the integral of the box cutoff of `c` times the squared
norm of the cut Bessel function times `schurWeight`), summed over the orbit of `γ`, is at most
`unipotentCovolume * #BesselCoord` times `tailScale² (b ^ 13 / M²) ^ (i k f)
(isotropicRowsIndex / √minorNorm) ^ k`. Here `i = min ϱ j`, `k = |κ|` and `f` is the number of
infinite places. Let `Λ` be the lattice of `c` and `A` the span of the isotropic vectors `e_a`. Then
`isotropicRowsIndex` is the index, in the lattice of the rows of products of `Λ ∩ A` with the frame
of `translateByClassReps c c' γ = h_c⁻¹ γ h_c'`, of the part that comes from the `e_a` with
`a < j`. -/
lemma tsum_schurIntegral_le (h_over : γ ∈ S.termsOver c s c') (h_rank : S.HasCellRank j γ)
    (hj : j ≠ 0) :
    ∑' δ : doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'),
        S.schurIntegral c c' δ (min 𝔰.ϱ j) ≤
      .ofReal (S.unipotentCovolume * (card S.BesselCoord * S.tailScale ^ 2 *
        (S.b ^ 13 / S.M ^ 2) ^ (min 𝔰.ϱ j * 𝔰.k * numInfPlaces E) *
        (S.isotropicRowsIndex j (S.translateByClassReps c c' γ) / √(S.minorNorm j γ)) ^ 𝔰.k)) := by
  -- Integrate in stages, averaging over the shifts with parameter in a fundamental domain `D` of
  -- the lattice. On each of the `isotropicRowsIndex ^ k` cosets the mean of the sum of the weights
  -- is at most `tailScale` times the integral of the kernel divided by the volume of `D`, which is
  -- at least `1`.
  have hτ : 2 ≤ S.tailScale := two_le_tailScale
  have hV : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb : 0 < S.b := b_pos
  obtain ⟨D, -, hD, hD_vol, hD_finite⟩ :=
    S.exists_isAddFundamentalDomain_columnLattice (Fin (min 𝔰.ϱ j)) c
  set d : ℕ := min 𝔰.ϱ j * 𝔰.k * numInfPlaces E with hd
  set orbit : Set (S.G E) := doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c')
  set index : ℕ := S.isotropicRowsIndex j (S.translateByClassReps c c' γ)
  -- Instance search finds this only when it is asked directly.
  have : Measure.IsAddHaarMeasure
      (volume : Measure (NumberField.InfinitePlace E → Fin (min 𝔰.ϱ j) → 𝔰.κ → ℂ)) := inferInstance
  let F (y : NumberField.InfinitePlace E → 𝔰.G₁) : ℝ≥0∞ :=
    ∑' p : orbit, S.schurWeight c' p (min 𝔰.ϱ j) y
  set C : ℝ≥0∞ :=
    .ofReal (index ^ 𝔰.k) * (.ofReal S.tailScale * ∏ v, .ofReal (S.kernelBound j γ v)) with hC
  have h_mean (u : NumberField.InfinitePlace E → 𝔰.G₁) (hu : ∀ v, u v ∈ besselU0)
      (y : NumberField.InfinitePlace E → 𝔰.G₁) (hy : y ∈ S.boxedPoints) :
      ∫⁻ x in D, F (u * S.eichlerShift j x * y) ≤ volume D * C := by
    refine le_trans ?_ (le_mul_of_one_le_left' hD_vol)
    rw [hC, lintegral_tsum fun _ ↦ Measurable.aemeasurable (by fun_prop)]
    refine tsum_orbit_le_of_isLatticeTranslate h_over h_rank
      (fun p ↦ ∫⁻ x in D, S.schurWeight c' p _ (u * S.eichlerShift j x * y)) _
      fun B hB p₀ hp₀ l hl ↦ ?_
    obtain ⟨φ, hφ_meas, hφ_int, hφ_le⟩ := exists_tsum_schurWeight_le hB hp₀ hl hu h_over h_rank hy
    have h_unfold : ∫⁻ x in D, ∑' w : S.columnLattice (Fin (min 𝔰.ϱ j)) c, φ (w +ᵥ x) =
        ∫⁻ x, φ x := by
      rw [hD.lintegral_eq_tsum'' φ, lintegral_tsum fun _ ↦ Measurable.aemeasurable (by fun_prop)]
    grw [← lintegral_tsum fun _ ↦ Measurable.aemeasurable (by fun_prop), lintegral_mono hφ_le,
      lintegral_const_mul' _ _ ofReal_ne_top, h_unfold, hφ_int]
  have h_inv (u : S.G E) (hu : u ∈ S.classUnipotent₀ c) (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      F (S.ratToInf u * y) = F y := tsum_schurWeight_ratToInf_mul hu y
  have h_pos : volume D ≠ 0 := (zero_lt_one.trans_le hD_vol).ne'
  calc
    _ = ∫⁻ y : NumberField.InfinitePlace E → 𝔰.G₁,
        S.boxCutoff c y * S.besselCutNormSq y * F y := by
      simp (disch := fun_prop) only [schurIntegral, ← lintegral_tsum, ENNReal.tsum_mul_left, F]
    _ ≤ C * (.ofReal S.unipotentCovolume * card S.BesselCoord) :=
      lintegral_boxCutoff_le_of_average c volume measurable_eichlerShift eichlerShift_mem
        (by fun_prop) h_inv D h_pos hD_finite h_mean
    _ ≤ .ofReal (index ^ 𝔰.k * (S.tailScale * (S.tailScale *
          (S.b ^ 13 / S.M ^ 2) ^ d * (√(S.minorNorm j γ))⁻¹ ^ 𝔰.k)) *
          (S.unipotentCovolume * card S.BesselCoord)) := by
      grw [hC, ← ofReal_prod_of_nonneg fun v _ ↦ kernelBound_nonneg hb.le v,
        prod_kernelBound_le h_over h_rank hj, ← ofReal_natCast]
      simp (disch := positivity) only [← ofReal_mul, ← hd, le_refl]
    _ = _ := by
      simp only [div_pow, inv_pow]
      congr 1
      field_simp

/-- **Schur's test.** Let `S` be admissible data over a CM field `E` with a primitive 5040th root of
unity, with size parameter `b`, `M = p₀ p₁` and `k = dim X₀`. Let `γ` have cell rank `j ≥ 1` and lie
over the block `(c, s, c')`. The square of the sum over its orbit of the absolute amplitudes, taken
with the cut Bessel functions `W♭` (`.cut`), is at most
`(V d τ² (b ^ 13 / M²) ^ (i k f))² (N ^ f / minorGauge) ^ k`.
Here `i = min ϱ j`, `V` is `unipotentCovolume`, the common covolume of the
unipotent groups of the classes, `d` is the number of Bessel coordinates, `τ = tailScale`, `f` is
the number of infinite places, and the gauge `minorGauge` is `N ^ f * minorNorm` divided by the two
indices `isotropicRowsIndex` of the term. -/
theorem sq_tsum_amplitudeMajorant_doubleCoset_le (h_over : γ ∈ S.termsOver c s c')
    (h_rank : S.HasCellRank j γ) (hj : j ≠ 0) :
    (∑' δ : doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'),
      S.amplitudeMajorant .cut c c' δ) ^ 2 ≤
      .ofReal ((S.unipotentCovolume * card S.BesselCoord * S.tailScale ^ 2 *
          (S.b ^ 13 / S.M ^ 2) ^ (min 𝔰.ϱ j * 𝔰.k * numInfPlaces E)) ^ 2 *
        (S.N ^ numInfPlaces E / S.minorGauge j c c' γ) ^ 𝔰.k) := by
  -- By Cauchy–Schwarz the square is at most the product of the sums of the two factors, for `γ`
  -- and for `γ⁻¹`.
  have hN : 0 < S.N := S.N_prime.pos
  have hV : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb : 0 < S.b := b_pos
  set orbit : Set (S.G E) := doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c') with h_orbit
  have h_schur : (∑' δ : orbit, S.amplitudeMajorant .cut c c' δ) ^ 2 ≤
      (∑' δ : orbit, S.schurIntegral c c' δ (min 𝔰.ϱ j)) *
        ∑' δ : orbit, S.schurIntegral c' c δ.1⁻¹ (min 𝔰.ϱ j) := by
    -- With every set measurable, a sum over the orbit is an integral for the counting measure.
    let : MeasurableSpace (S.G E) := ⊤
    simp only [← lintegral_count]
    exact sq_lintegral_le .of_discrete .of_discrete fun δ ↦ amplitudeMajorant_sq_le _
  -- Inversion maps the orbit of `γ` into that of `γ⁻¹`, which has the same cell rank and minor.
  have h_inverse : ∑' δ : orbit, S.schurIntegral c' c δ.1⁻¹ (min 𝔰.ϱ j) ≤
      ∑' δ : doubleCoset γ⁻¹ (S.classUnipotent₀ c') (S.classUnipotent₀ c),
        S.schurIntegral c' c δ (min 𝔰.ϱ j) := by
    rw [← tsum_image (S.schurIntegral c' c · (min 𝔰.ϱ j)) inv_injective.injOn]
    refine tsum_mono_subtype (S.schurIntegral c' c · (min 𝔰.ϱ j)) ?_
    simp [h_orbit, doubleCoset, mul_assoc, -Set.mul_singleton, -Set.singleton_mul]
  have h_translate_inv : S.translateByClassReps c' c γ⁻¹ = (S.translateByClassReps c c' γ)⁻¹ := by
    simp [translateByClassReps, mul_assoc]
  have h_ratio : S.N ^ numInfPlaces E / S.minorGauge j c c' γ =
      S.isotropicRowsIndex j (S.translateByClassReps c c' γ) / √(S.minorNorm j γ) *
        (S.isotropicRowsIndex j (S.translateByClassReps c c' γ)⁻¹ / √(S.minorNorm j γ)) := by
    rw [h_rank.minorGauge_eq, div_mul_div_comm, mul_self_sqrt h_rank.minorNorm_pos.le,
      div_div_eq_mul_div, mul_div_mul_left _ _ (by positivity)]
  grw [h_schur, h_inverse, tsum_schurIntegral_le h_over h_rank hj,
    tsum_schurIntegral_le (termsOver.inv h_over) h_rank.inv hj, minorNorm_inv, h_translate_inv,
    ← ofReal_mul (by positivity), h_ratio, mul_pow _ _ 𝔰.k]
  exact ofReal_le_ofReal (le_of_eq (by ring))

omit [HasPrimitiveRoot5040 E] in
/-- At cell rank `j ≥ 1`, the second moment `cellRankSecondMoment j` is at least `α ^ (8 - 32 i)`
times `identitySecondMoment`. Here `identitySecondMoment` is the order of the reduced image of the
Bessel subgroup `besselS` times the dimension `sourceDim` of the space of source forms, and
`cellRankSecondMoment j` is `mainSecondMoment` for `j = ϱ + 1` and `α ^ (-16)` times
`identitySecondMoment` for `j ≤ ϱ`. -/
lemma div_tailScale_pow_mul_identitySecondMoment_le_cellRankSecondMoment (hj : j ≠ 0) :
    S.tailScale ^ 8 / (S.tailScale ^ 32) ^ min 𝔰.ϱ j * S.identitySecondMoment ≤
      S.cellRankSecondMoment j := by
  have hτ : 1 ≤ S.tailScale := one_le_two.trans two_le_tailScale
  have h_identityMoment_nonneg : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  unfold cellRankSecondMoment
  split_ifs with h_top
  · calc S.tailScale ^ 8 / (S.tailScale ^ 32) ^ min 𝔰.ϱ j * S.identitySecondMoment
        ≤ S.tailScale ^ 8 * S.identitySecondMoment := by
          grw [div_le_self (by positivity) (by bound)]
      _ ≤ S.tailScale ^ 44 * S.identitySecondMoment := by
          gcongr
          lia
      _ ≤ S.mainSecondMoment := tailScale_pow_mul_identitySecondMoment_le
  · have h_min_ne : min 𝔰.ϱ j ≠ 0 := by
      rw [min_eq_right (not_lt.1 h_top)]
      exact val_ne_zero_iff.2 hj
    calc S.tailScale ^ 8 / (S.tailScale ^ 32) ^ min 𝔰.ϱ j * S.identitySecondMoment
        ≤ S.tailScale ^ 8 / S.tailScale ^ 32 * S.identitySecondMoment := by
          grw [← le_self_pow₀ (by bound) h_min_ne]
      _ = S.identitySecondMoment / S.tailScale ^ 24 := by field_simp
      _ ≤ S.identitySecondMoment / S.tailScale ^ 16 := by
          gcongr
          lia

omit [HasPrimitiveRoot5040 E] [S.IsAdmissible] in
/-- The field `le_M` of `S` gives `S.b ^ 19 ≤ S.M`, so the factor `S.b ^ 13 / S.M²` is at most
`1 / (S.b ^ 4 S.M)`. -/
lemma b_pow_div_M_sq_le : S.b ^ 13 / (S.M : ℝ) ^ 2 ≤ (S.b ^ 4 * S.M)⁻¹ := by
  have hb_pos : 0 < S.b := b_pos
  have h_pow : S.b ^ 17 ≤ (S.M : ℝ) := (pow_le_pow_right₀ S.one_le_b (by norm_num)).trans S.le_M
  have hM_pos : 0 < (S.M : ℝ) := (pow_pos hb_pos 17).trans_le h_pow
  field_simp
  exact h_pow

/-- Let `γ` lie over the block `(c, s, c')` and have cell rank `j ≥ 1`, and let
`termDiscNorm γ ≤ N ^ f * minorNorm j γ`, so that `maxGauge` equals `minorGauge` at `γ`. Then the
absolute amplitudes of the terms of its orbit, taken with the cut Bessel functions `W♭` (`.cut`),
add up to at most `unipotentCovolume` times `orbitBound`, which is
`α² √(D_j / (n_p (M ^ (2 i f) x) ^ k))` at the gauge `x = maxGauge`. Here `i = min ϱ j`,
`k = dim X₀`, `D_j` is the second moment `cellRankSecondMoment j`, `n_p = pairCountScale` and
`α = tailScale`. -/
lemma tsum_amplitudeMajorant_orbit_le (h_over : γ ∈ S.termsOver c s c')
    (h_rank : S.HasCellRank j γ) (hj : j ≠ 0)
    (h_disc_le : S.termDiscNorm γ ≤ S.N ^ numInfPlaces E * S.minorNorm j γ) :
    ∑' δ : doubleCoset γ (S.classUnipotent₀ c) (S.classUnipotent₀ c'),
      S.amplitudeMajorant .cut c c' δ ≤
      .ofReal (S.unipotentCovolume * S.orbitBound j (S.maxGauge j c c' γ)) := by
  classical
  have hτ : 2 ≤ S.tailScale := two_le_tailScale
  have h_identityMoment_nonneg : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_rankMoment_nonneg : 0 ≤ S.cellRankSecondMoment j := cellRankSecondMoment_nonneg j
  have hV : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb_pos : 0 < S.b := b_pos
  have h_gauge : S.maxGauge j c c' γ = S.minorGauge j c c' γ := by
    rw [h_rank.maxGauge_eq, max_eq_right h_disc_le, h_rank.minorGauge_eq]
  have h_pos : 0 < S.minorGauge j c c' γ := (maxGauge_pos h_over h_rank).trans_eq h_gauge
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, orbitBound, ← ofReal_pow (by positivity)]
  refine (sq_tsum_amplitudeMajorant_doubleCoset_le h_over h_rank hj).trans (ofReal_le_ofReal ?_)
  -- One factor `card S.BesselCoord` is at most `b ^ (2 k f) = tailScale ^ 8`; the other is part
  -- of `identitySecondMoment`.
  have h_dim : (card S.BesselCoord : ℝ) ≤ S.tailScale ^ 8 := by
    grw [IsAdmissible.card_besselCoord_le, pow_mul _ 4 2, tailScale_pow_four]
    exact le_of_eq (by ring)
  have h_gain : (S.tailScale ^ 32) ^ min 𝔰.ϱ j =
      ((S.b ^ 4) ^ (min 𝔰.ϱ j * 𝔰.k * numInfPlaces E)) ^ 2 := by
    rw [pow_mul _ 4 8, tailScale_pow_four]
    ring
  rw [h_gauge, mul_pow S.unipotentCovolume, mul_pow (S.tailScale ^ 2), sq_sqrt (by positivity)]
  -- Insert the bounds for `b ^ 13 / M²`, the second moment and the number of coordinates. What is
  -- left is an identity, by the definitions of `identitySecondMoment` and `pairCountScale`.
  have h_moment_le : S.tailScale ^ 8 / (S.tailScale ^ 32) ^ min 𝔰.ϱ j * S.identitySecondMoment ≤
      S.cellRankSecondMoment j :=
    div_tailScale_pow_mul_identitySecondMoment_le_cellRankSecondMoment hj
  have h_ratio_le : S.b ^ 13 / (S.M : ℝ) ^ 2 ≤ (S.b ^ 4 * S.M)⁻¹ := b_pow_div_M_sq_le
  grw [h_ratio_le, ← h_moment_le, ← h_dim, h_gain]
  refine le_of_eq ?_
  simp only [identitySecondMoment, sourceDim, pairCountScale, Nat.cast_mul, div_pow, inv_pow,
    mul_inv, mul_pow]
  field_simp
  ring

end New.Filling

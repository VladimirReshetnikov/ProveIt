import Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure
import New.Spanning.Unfolding.Packing

/-!
# The Bessel kernel and the integral of a class cutoff over the real unipotent group

This file proves that the kernel `New.Filling.besselKernel`, the tensor
`besselFn(y) ⊗ besselFn(γ⁻¹ y)^*` of Bessel functions at the infinite places, is continuous.
It bounds the amplitude `New.Filling.amplitude` by the integral of the norms
`New.Filling.amplitudeMajorant`. It then computes the integral of a class cutoff
`S.classCutoff c` over the real unipotent group as `S.unipotentCovolume`. The group is unfolded
one coordinate at a time (`New.Filling.rowCoords`). The integral is then a product of covolumes of
explicit lattices.

## Main definitions and results

* `New.Filling.enorm_amplitude_le`: the norm of the amplitude
  `∫ β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^* dy` is at most the integral of the norm of its integrand.
* `New.Filling.lintegral_classCutoff_eq_unipotentCovolume`: let `E` contain a primitive 5040th
  root of unity and let `S` be admissible. For every class `c` and archimedean point `y`, the
  integral of the cutoff `u ↦ S.classCutoff c (u y)` over the real unipotent group 𝖴_∞, for the
  product of the Haar measures `New.Shape.besselHaar`, is the number `S.unipotentCovolume`.

Notions from other files:
* `New.Filling.besselFn`: for a tuple `i` of coordinates (`New.Filling.BesselCoord`), the product
  over the places `v` of the `i v`-th coordinate of `W side (y v)`.
* `New.Filling.M`, `New.Filling.classUnipotent`: the level M = p₀ p₁, the product of the two primes
  `S.levelPrime`; the rational points u of 𝖴 with h_c⁻¹ u h_c in the principal congruence
  subgroup K(M).
* `New.Shape.Form.besselU`, `New.Shape.Form.besselS`: the group 𝖴 of block upper unitriangular
  isometries, and the Bessel subgroup, which 𝖴 generates together with the unitary group of the
  standard form on κ.
* `New.Filling.IsAdmissible`: the standing hypotheses. The level `sourceLevel` is the preimage of
  K(M), `reduction` is onto, and size inequalities hold between b, M and ϖ, κ_v, N, the second
  moments, the number of Bessel coordinates, an index and the constant `scaledSiegelConst`.
* `New.Filling.unipotentCovolume`: an explicit positive number built from M, N, |κ|, ϱ, the
  discriminant of E and the scales of the frame at the infinite places.
-/

/-!
## Continuity of the Bessel kernel and the bound of an amplitude

First facts on the kernel `New.Filling.besselKernel`, the tensor `besselFn(y) ⊗ besselFn(γ⁻¹ y)^*`
of Bessel functions at the infinite places. The amplitude `New.Filling.amplitude`, its integral
against the cutoffs `New.Filling.classCutoff`, is bounded by the integral of the norms
`New.Filling.amplitudeMajorant` (`New.Filling.enorm_amplitude_le`).
-/

section AmplitudeBounds

open Fintype NumberField

namespace New.Filling

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E] {S : Filling E 𝔰} {γ : S.G E}
  {side : FullOrCut}

/-- Each coordinate of the product of the local Bessel functions is continuous on G_∞. -/
@[fun_prop]
lemma continuous_besselFn (i : S.BesselCoord) :
    Continuous fun y : InfinitePlace E → 𝔰.G₁ ↦ S.besselFn side y i := by
  fun_prop [besselFn]

/-- The kernel `y ↦ W(y) ⊗ W(γ⁻¹ y)^*` is continuous on G_∞. -/
@[fun_prop]
lemma continuous_besselKernel : Continuous (S.besselKernel side γ) := by fun_prop [besselKernel]

/-- The norm of `W(y) ⊗ W(γ⁻¹ y)^*` is the product of the norms of the local factors. The factor at
the infinite place `v` is the Bessel function `(S.besselSystem v).besselFn side`, full or cut
according to `side`, and `S.ratToInf γ` is the image in G_∞ of the rational element `γ`. -/
lemma enorm_besselKernel (y : InfinitePlace E → 𝔰.G₁) :
    ‖S.besselKernel side γ y‖ₑ =
      (∏ v : InfinitePlace E, ‖(S.besselSystem v).besselFn side (y v)‖ₑ) *
        ∏ v : InfinitePlace E, ‖(S.besselSystem v).besselFn side (((S.ratToInf γ)⁻¹ * y) v)‖ₑ := by
  -- Square both sides: the sum over pairs of tuples of indices of the squared coordinates factors
  -- as a product over the places, for each of the two tensor factors.
  simp only [enorm]
  norm_cast
  rw [← sq_eq_sq₀ zero_le zero_le]
  simp [EuclideanSpace.nnnorm_eq, besselKernel, besselFn, mul_pow, ← Finset.prod_pow, sum_prod_type,
    prod_sum, sum_mul_sum]

/-- The norm of the amplitude `∫ β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^* dy` is at most the integral of
the norm of its integrand. -/
lemma enorm_amplitude_le (c c' : S.Classes) :
    ‖S.amplitude side c c' γ‖ₑ ≤ S.amplitudeMajorant side c c' γ := by
  grw [amplitude, MeasureTheory.enorm_integral_le_lintegral_enorm, enorm_toReal_smul_le,
    amplitudeMajorant]

end New.Filling

end AmplitudeBounds

/-!
## Integral of a class cutoff over the real unipotent group

`New.Filling.lintegral_classCutoff_eq_unipotentCovolume` computes the covolume of the arithmetic
unipotent group `S.classUnipotent c` of a class `c` in the real unipotent group (a copy of
`New.Shape.Form.besselU` at each infinite place, with the Haar measure `New.Shape.besselHaar`): the
cutoff `S.classCutoff c`, whose translates under `S.classUnipotent c` sum to `1`, has integral
`S.unipotentCovolume`.

The group is unfolded one coordinate at a time by `New.Filling.existsUnique_mul_mem_box`. The basis
is e_a, the middle block, e*_a (`New.Shape.BesselIndex`); the coordinates of a unipotent element are
the free entries of each row e_a (positions `New.RealPlace.IsFreeEntry`) and the imaginary part of
its entry at e*_a. Each coordinate is additive once the earlier ones vanish; the integral is then a
product of covolumes of explicit lattices.
-/

section UnipotentCovolume

namespace New.Filling

open NumberField MeasureTheory Matrix Complex Finset RealPlace Sum ENNReal Function Fintype

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod in
/-- Additivity of an entry in the row of e_a, for x and u in the Bessel unipotent group of G₁. Let
the column j be e*_a or free for the row (`IsFreeEntry`: e_b or e*_b with b > a, or a column of the
middle block). If the free entries of u vanish in the rows e_b with b > a and in the row e_b with
j = e*_b, and the entries of u at (e_b, e*_b), b > a, are real, then the (e_a, j) entry of x·u is
the sum of those of u and x. -/
lemma besselU_mul_apply_eq_add {𝔰 : Shape} (x u : (𝔰.middleGram (1 : ℂ)).besselU) {a : Fin 𝔰.ϱ}
    {j : 𝔰.BesselIndex} (hj : j = eStar a ∨ IsFreeEntry (a, j))
    (h_im : ∀ b : Fin 𝔰.ϱ, a < b →
      ((u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl b) (eStar b)).im = 0)
    (h_zero : ∀ (b : Fin 𝔰.ϱ) (k : 𝔰.BesselIndex), a < b ∨ j = eStar b → IsFreeEntry (b, k) →
      (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl b) k = 0) :
    (↑(x * u) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) j =
      (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) j +
        (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) j := by
  set X : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := ↑x with hX
  set U' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := ↑u with hU'
  -- It suffices that ((X − 1)(U' − 1))(e_a, j) = 0, and this holds term by term.
  suffices h_prod : ((X - 1) * (U' - 1)) (inl a) j = 0 by
    have h_ne : inl a ≠ j := by grind [IsFreeEntry]
    simpa [hX, hU', Matrix.one_apply, h_ne, sub_eq_iff_eq_add', mul_sub, sub_mul] using h_prod
  -- Outside the columns e*_d, the rows of U' that matter below are those of 1.
  have h_row (k l : 𝔰.BesselIndex) (hk : ∀ b, k = inl b → a < b ∨ j = eStar b)
      (hl : ∀ d, l ≠ eStar d) : U' k l = if k = l then 1 else 0 := by
    have h_low (hkl : BesselIndex.level l ≤ BesselIndex.level k) :
        U' k l = if k = l then 1 else 0 := mem_besselU.1 u.2 k l hkl
    rcases k with b | i | b <;> rcases l with b' | i' | b' <;>
      simp only [BesselIndex.level, elim_inl, elim_inr] at h_low <;>
      grind [IsFreeEntry]
  refine sum_eq_zero fun k _ ↦ mul_eq_zero.2 ?_
  by_cases hk : BesselIndex.level k ≤ BesselIndex.level (inl a : 𝔰.BesselIndex)
  · exact .inl (sub_eq_zero.2 (mem_besselU.1 x.2 _ k hk))
  -- Here k has higher level than e_a, and we show that U'(k, j) is the entry of 1.
  refine .inr (sub_eq_zero.2 ?_)
  have hk_row (b : Fin 𝔰.ϱ) (hb : k = inl b) : a < b ∨ j = eStar b :=
    .inl (by simpa [hb, BesselIndex.level] using hk)
  by_cases! hj_star : ∀ d, j ≠ eStar d
  · exact h_row k j hk_row hj_star
  obtain ⟨c, rfl⟩ := hj_star
  -- In the column e*_c use U' · (J U'ᴴ J) = 1.
  let J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := (𝔰.middleGram (1 : ℂ)).splitGram
  have h_inv : U' * (J * U'ᴴ * J) = 1 := by
    rw [← U.coe_inv IsHermitianInvolution.mul_self u.1]
    exact u.1.1.mul_inv
  have h_unitary : ∑ d, U' k (inl d) * starRingEnd ℂ (U' (inl c) (eStar d)) + U' k (eStar c) =
      if k = eStar c then 1 else 0 := by
    simpa [Matrix.one_apply, J, Shape.Form.splitGram, h_row (inl c), Matrix.mul_apply] using
      congrFun₂ h_inv k (eStar c)
  have h_col (d : Fin 𝔰.ϱ) : U' k (inl d) = if k = inl d then 1 else 0 :=
    h_row k _ hk_row (by simp)
  rcases k with d | i | d
  · -- For c ≠ d one of the two entries is free, hence zero; for c = d the entry is real.
    have h_skew : starRingEnd ℂ (U' (inl c) (eStar d)) + U' (inl d) (eStar c) = 0 := by
      simpa [h_col] using h_unitary
    have had : a < d := by simpa [BesselIndex.level] using hk
    suffices U' (inl d) (eStar c) = 0 by simpa
    grind [conj_eq_iff_im, IsFreeEntry]
  · simpa [h_col] using h_unitary
  · simpa [h_col, Matrix.one_apply] using h_unitary

/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. The basis matrix
`classBasis c` of the lattice of the class `c` differs from the identity only in its middle block
`M`, and the generalised index (`genIndex`, the inverse Haar modulus) of `det M` is `N ^ (-f)`.
Here `N = S.N` is the prime `π π̄` of `S` and `f` is the number of infinite places of `E`. -/
lemma exists_classBasis_eq_fromBlocks {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E]
    {𝔰 : Shape} {S : Filling E 𝔰} (c : S.Classes) [S.IsAdmissible] :
    ∃ M : Matrix 𝔰.MiddleIndex 𝔰.MiddleIndex (𝔸f E),
      (classBasis c).val = fromBlocks 1 0 0 (fromBlocks M 0 0 1) ∧
      genIndex M.det = 1 / S.N ^ numInfPlaces E := by
  -- The witness `M` is read off from the product of the block matrices that define `classBasis c`.
  use ?_, by
    simp [Matrix.fromBlocks_multiply, classBasis, toBesselH, besselLatticeBasis]
    rfl
  -- det M is the determinant of the unitary representative of c over the conjugate of `S.piN`.
  -- Apply `genIndex` to the unitarity relation and to `piN_mul_star`, and take positive square
  -- roots.
  have h_unitary : genIndex c.out.val.val.det = 1 := by
    have h_sq : genIndex c.out.val.val.det ^ 2 = 1 := by
      simpa [← sq] using congrArg (fun A ↦ genIndex (det A)) c.out.2
    exact (pow_eq_one_iff_of_nonneg (genIndex_pos c.out.val.det).le two_ne_zero).1 h_sq
  have h_norm : genIndex (S.piN : 𝔸f E) = S.N ^ numInfPlaces E := by
    have h_sq : genIndex (S.piN * star S.piN.val : 𝔸f E) = genIndex (S.N : 𝔸f E) :=
      congrArg genIndex S.piN_mul_star
    simpa [genIndex_natCast, ← sq, (genIndex_pos S.piN).le] using h_sq
  simp [h_unitary, h_norm]

/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. Let `γ` lie in
`S.classUnipotent c`, the rational unipotent elements that the representative of the class `c`
conjugates into the principal congruence subgroup of level `S.M`. Then the row of γ − 1 at e_a,
divided by `S.M`, has integral coordinates in the basis `classBasis c` of the lattice of `c`. -/
lemma classUnipotent_sub_one_div_M_row_integral {E : Type} [Field E] [CMType E]
    [HasPrimitiveRoot5040 E] {𝔰 : Shape} {S : Filling E 𝔰} {c : S.Classes} [S.IsAdmissible]
    (γ : S.classUnipotent c) (a : Fin 𝔰.ϱ) (j : 𝔰.BesselIndex) :
    (finAdeleMatrix ((S.M : E)⁻¹ • ((γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) - 1)) (inl a) ᵥ*
      (classBasis c).val) j ∈ Ô E := by
  -- Conjugation by the basis turns γ into `S.translateByClassReps c c γ`, which lies in
  -- `S.principalLevel`.
  let k : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := S.translateByClassReps c c γ
  have h_conj : finAdeleMatrix ((S.M : E)⁻¹ • ((γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) - 1)) *
      (classBasis c).val = (classBasis c).val * S.ideleM⁻¹ • (k - 1) := by
    simp [k, coe_translateByClassReps, Matrix.map_sub, -Nat.cast_mul, sub_mul, mul_assoc, mul_sub]
    rfl
  have h_level : S.translateByClassReps c c γ ∈ S.principalLevel := γ.2.2
  have h_int : (S.ideleM⁻¹ • (k - 1)) (inl a) j ∈ Ô E :=
    (S.principalLevel_eq_unitaryLevel.le h_level).2 _ j
  obtain ⟨M, h_basis, -⟩ := exists_classBasis_eq_fromBlocks c
  rw [← mul_apply_eq_vecMul, h_conj]
  simpa [Matrix.one_apply, h_basis, Matrix.mul_apply] using h_int

attribute [local simp] BesselIndex.level frameScaleSq

attribute [local grind] IsFreeEntry

section FreeBlock

variable {R : Type*} [CommRing R] {𝔰 : Shape} {b : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R}
  {M : Matrix 𝔰.MiddleIndex 𝔰.MiddleIndex R}

open scoped Classical in
/-- If `b` differs from the identity only in its middle block, then its square block on the free
columns (`IsFreeEntry`) of the row e_a has the determinant of `b`. -/
lemma det_toSquareBlockProp_isFreeEntry (hb : b = fromBlocks 1 0 0 (fromBlocks M 0 0 1))
    (a : Fin 𝔰.ϱ) :
    (b.toSquareBlockProp fun j : 𝔰.BesselIndex ↦ IsFreeEntry (a, j)).det = b.det := by
  have h_rest : (b.toSquareBlockProp fun j ↦ ¬IsFreeEntry (a, j)) = 1 := by
    simp [Matrix.one_apply, toSquareBlockProp, ← ext_iff, hb]
  have h_triangular : ∀ i, ¬IsFreeEntry (a, i) → ∀ j, IsFreeEntry (a, j) → b i j = 0 := by
    simp [Matrix.one_apply, hb]
    omega
  simp [b.twoBlockTriangular_det (fun j ↦ IsFreeEntry (a, j)) h_triangular, h_rest]

open scoped Classical in
/-- If `b` differs from the identity only in its middle block, then the entries of `l ᵥ* b` in the
free columns (`IsFreeEntry`) of the row e_a depend only on the entries of `l` in these columns. -/
lemma transpose_toSquareBlockProp_mulVec (hb : b = fromBlocks 1 0 0 (fromBlocks M 0 0 1))
    (a : Fin 𝔰.ϱ) (l : 𝔰.BesselIndex → R) (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) :
    ((b.toSquareBlockProp fun j : 𝔰.BesselIndex ↦ IsFreeEntry (a, j))ᵀ *ᵥ l ∘ Subtype.val) j =
      (l ᵥ* b) j := by
  refine sum_of_injective _ Subtype.val_injective _ _ ?_ fun k ↦ mul_comm _ (l k)
  revert j
  simp [Matrix.one_apply, hb]
  lia

end FreeBlock

section Coordinates

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- The embedding of `S.classUnipotent c` into the real unipotent group 𝖴_∞, the product over the
infinite places of the Bessel unipotent group of G₁. -/
noncomputable def classUnipotentToInf (c : S.Classes) :
    S.classUnipotent c →* InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU :=
  .mk' (fun γ v ↦ ⟨S.ratToInf γ v, γ.2.1.ratToInf_mem_agreeWithOneOn v⟩) (by aesop)

lemma coe_classUnipotentToInf_apply {c : S.Classes} (γ : S.classUnipotent c) (v : InfinitePlace E) :
    (classUnipotentToInf c γ v : 𝔰.G₁) = S.ratToInf γ v := rfl

lemma classUnipotentToInf_injective (c : S.Classes) : Injective (classUnipotentToInf c) := by
  intro _
  simp [funext_iff, coe_classUnipotentToInf_apply, ← SetLike.coe_eq_coe, GeneralLinearGroup.ext_iff,
    (RingHom.injective _).eq_iff]

/-- The free entries (`IsFreeEntry`) of the row e_a of a point `u` of the real unipotent group
𝖴_∞, at all infinite places. -/
def freeRowCoords (u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) (a : Fin 𝔰.ϱ)
    (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) (v : InfinitePlace E) : ℂ :=
  (u v : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) j

/-- The imaginary parts of the entry at (e_a, e*_a) of a point `u` of the real unipotent group
𝖴_∞, at all infinite places. -/
def imRowCoords (u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) (a : Fin 𝔰.ϱ)
    (v : InfinitePlace E) : ℝ :=
  ((u v : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a)).im

/-- The coordinates of a point `u` of the real unipotent group 𝖴_∞, grouped by rows: for each row
e_a, its free entries (`freeRowCoords`) and the imaginary parts of its entry at e*_a
(`imRowCoords`), at all infinite places. -/
def rowCoords (u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) :
    (∀ a : Fin 𝔰.ϱ, {j : 𝔰.BesselIndex // IsFreeEntry (a, j)} → InfinitePlace E → ℂ) ×
      (Fin 𝔰.ϱ → InfinitePlace E → ℝ) :=
  (freeRowCoords u, imRowCoords u)

open scoped Classical in
/-- The map `rowCoords` sends a point of the real unipotent group 𝖴_∞ to the free entries of its
rows e_a and the imaginary parts (real numbers) of its entries at (e_a, e*_a), at all infinite
places of `E`. It carries the product over the infinite places of the Haar measure `besselHaar` to
Lebesgue measure on these coordinates. -/
lemma measurePreserving_rowCoords :
    MeasurePreserving (rowCoords (E := E) (𝔰 := 𝔰)) (.pi fun _ ↦ 𝔰.besselHaar)
      (volume.prod volume) := by
  -- Use `measurePreserving_freeEntries_besselHaar` at each place, then regroup the coordinates by
  -- rows instead of places.
  exact ((((measurePreserving_sigma
    (.symm (.subtypeProdEquivSigmaSubtype fun a j ↦ IsFreeEntry (𝔰 := 𝔰) (a, j)))).comp
      measurePreserving_flip).prod measurePreserving_flip).comp
        (measurePreserving_arrowProdEquivProdArrow ..)).comp
    (measurePreserving_pi _ _ fun _ : InfinitePlace E ↦ measurePreserving_freeEntries_besselHaar)

/-- Unfolding. Let `E` contain a primitive 5040th root of unity and let `S` be admissible. The
cutoff `S.classCutoff c` is a measurable function G_∞ → [0, ∞], on tuples `y` of points of `G₁` at
the infinite places, whose left translates under the congruence group `S.classUnipotent c` of
rational unipotent elements add up to `1`. Let `B` be a measurable subset of the real unipotent
group 𝖴_∞ that meets each coset `u Γ` of the image `Γ` of `S.classUnipotent c` under
`classUnipotentToInf c` in exactly one point. Then the integral over 𝖴_∞ of
`u ↦ S.classCutoff c (u y)` is the measure of `B`, both for the product of the Haar measures
`𝔰.besselHaar`. -/
lemma lintegral_classCutoff_eq_measure [HasPrimitiveRoot5040 E] [S.IsAdmissible] (c : S.Classes)
    (y : InfinitePlace E → 𝔰.G₁)
    {B : Set (InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU)} (hB_meas : MeasurableSet B)
    (hB_unique : ∀ u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU,
      ∃! γ : (classUnipotentToInf c).range, u * γ ∈ B) :
    ∫⁻ u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU,
        S.classCutoff c (fun v : InfinitePlace E ↦ u v * y v) ∂(.pi fun _ ↦ 𝔰.besselHaar) =
      Measure.pi (fun _ ↦ 𝔰.besselHaar) B := by
  let Γ : Subgroup (InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) :=
    (classUnipotentToInf c).range
  -- The inverse of `B` is a fundamental domain for the left translations by `Γ`.
  have h_fund : IsFundamentalDomain Γ B⁻¹ (.pi fun _ ↦ 𝔰.besselHaar) :=
    .mk' hB_meas.inv.nullMeasurableSet fun u ↦
      ((Equiv.inv Γ).existsUnique_congr fun γ ↦ by simp [Subgroup.smul_def]).1 (hB_unique u⁻¹)
  have h_sum (u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) :
      ∑' γ : Γ, S.classCutoff c (fun v ↦ (γ • u) v * y v) = 1 := by
    rw [← ((classUnipotentToInf c).ofInjective (classUnipotentToInf_injective c)).tsum_eq,
      ← tsum_classCutoff_eq_one c fun v ↦ u v * y v]
    exact tsum_congr fun γ ↦ congrArg (S.classCutoff c) (funext fun v ↦ mul_assoc ..)
  have : Countable Γ := (classUnipotentToInf c).rangeRestrict_surjective.countable
  have : MeasurableConstSMul Γ (InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) :=
    ⟨fun γ ↦ measurable_const_mul γ.val⟩
  have : SMulInvariantMeasure Γ (InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU)
      (.pi fun _ ↦ 𝔰.besselHaar) :=
    ⟨fun γ s _ ↦ measure_preimage_mul _ γ.val s⟩
  -- The translates of the cutoff add up to 1, and the measure is inversion invariant.
  rw [h_fund.lintegral_eq_tsum'', ← lintegral_tsum (by fun_prop), lintegral_congr h_sum]
  simp

/-- Let `γ ∈ S.classUnipotent c`. If, at an infinite place `v`, right multiplication by `γ` adds the
(e_a, e*_a) entry of `γ` to that of every unipotent `x`, then the (e_a, e*_a) entry of `γ` divided
by the level `S.M` is skew: the complex conjugation `star` of the CM field `E` changes its sign. -/
lemma star_inv_mul_apply_eStar_eq_neg {c : S.Classes} (γ : S.classUnipotent c) (v : InfinitePlace E)
    (a : Fin 𝔰.ϱ)
    (h_add : ∀ x : (𝔰.middleGram (1 : ℂ)).besselU,
      (↑(x * classUnipotentToInf c γ v) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) =
        (classUnipotentToInf c γ v : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) +
          (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a)) :
    star ((S.M : E)⁻¹ * (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (inl a) (eStar a)) =
      -((S.M : E)⁻¹ * (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (inl a) (eStar a)) := by
  -- Take x = γ⁻¹ = J γᴴ J.
  let J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := (𝔰.middleGram (1 : ℂ)).splitGram
  let Y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := classUnipotentToInf c γ v
  have h_inv : (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) =
      Y (inl a) (eStar a) + (J * Yᴴ * J) (inl a) (eStar a) := by
    rw [← U.coe_inv IsHermitianInvolution.mul_self]
    simpa using h_add (classUnipotentToInf c γ v)⁻¹
  apply (Φ v).injective
  simpa [Matrix.mul_apply, J, Y, coe_classUnipotentToInf_apply, basisScale, Complex.ext_iff,
    self_eq_neg, ← two_mul, Nat.Prime.ne_zero, -ofReal_div] using h_inv

/-- For admissible `S` and `γ ∈ S.classUnipotent c`, the (e_a, e*_a) entry of `γ` is the level
`S.M` times an algebraic integer. -/
lemma isIntegral_inv_mul_apply_eStar [HasPrimitiveRoot5040 E] [S.IsAdmissible] {c : S.Classes}
    (γ : S.classUnipotent c) (a : Fin 𝔰.ϱ) :
    IsIntegral ℤ
      ((S.M : E)⁻¹ * (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (inl a) (eStar a)) := by
  obtain ⟨M, h_basis, -⟩ := exists_classBasis_eq_fromBlocks c
  -- `using!` identifies the entry of `finAdeleMatrix` with the image under `algebraMap`.
  exact algebraMap_mem_Ô.1
    (by simpa [vecMul_fromBlocks, h_basis] using! classUnipotent_sub_one_div_M_row_integral γ a
          (eStar a))

open scoped Classical in
/-- The volume of the fundamental domain for the free entries (`IsFreeEntry`) of the row e_a, of
which there are 2(ϱ − 1 − a) + k + 1, is `(∏ v, S.M ^ 2 / S.frameScaleSq v a) / volÔ E` to that
power. Here `S.basisScale v j` is the scale of the basis vector `j` at the place `v`,
`S.frameScaleSq v a` is the square of the scale of e_a, `S.M` is the level, and `volÔ E` is
2^r₂/√|disc E|, with r₂ the number of complex places. -/
lemma prod_norm_basisScale_sq_div_eq (S : Filling E 𝔰) (a : Fin 𝔰.ϱ) :
    (∏ v : InfinitePlace E, ‖∏ j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)},
        (S.M : ℂ) / S.basisScale v (inl a) * S.basisScale v j‖ ^ 2) /
        (1 / (S.N : ℝ) ^ numInfPlaces E) /
        volÔ E ^ Fintype.card {j : 𝔰.BesselIndex // IsFreeEntry (a, j)} =
      ((∏ v : InfinitePlace E, (S.M : ℝ) ^ 2 / S.frameScaleSq v a) / volÔ E) ^
        (a.rev + (𝔰.k + 1) + a.rev : ℕ) := by
  -- `↓` splits the product and the count over the three blocks before they are simplified.
  simp [div_pow, prod_pow, tsub_add_eq_tsub_tsub_swap, Finset.prod_mul_distrib,
    Fintype.card_subtype, card_filter, basisScale, ↓prod_sum_type,
    ← prod_subtype _ mem_filter_univ, ↓sum_sum_type, prod_filter, filter_lt_eq_Ioi, mul_pow,
    pow_right_comm _ _ 2, prod_ite]
  field [prod_eq_zero_iff, Nat.Prime.ne_zero]

/-- The number `S.unipotentCovolume` is the product, over the rows e_a, of the covolumes of the
lattice of free entries and of the lattice of imaginary parts at e*_a. -/
lemma unipotentCovolume_eq_prod (S : Filling E 𝔰) :
    S.unipotentCovolume =
      (∏ a : Fin 𝔰.ϱ, ((∏ v : InfinitePlace E, (S.M : ℝ) ^ 2 / S.frameScaleSq v a) / volÔ E) ^
          (a.rev + (𝔰.k + 1) + a.rev : ℕ)) *
        ∏ a : Fin 𝔰.ϱ, ((∏ v : InfinitePlace E, |S.M / S.frameScaleSq v a|) *
          √√|NumberField.discr E|) := by
  have h_exponent (k : ℕ) (a : Fin 𝔰.ϱ) :
      k + 2 * (𝔰.ϱ - a) = a.rev + (k + 1) + a.rev + 1 := by grind
  rw [unipotentCovolume, ← sum_range_reflect, sum_range, frameScaleProd, prod_comm,
    Fin.prod_univ_castSucc]
  simp [div_pow, pow_mul', prod_pow, tsub_add_eq_tsub_tsub_swap, Finset.prod_mul_distrib,
    Finset.sum_add_distrib, mul_pow, abs_div, pow_right_comm _ _ 2,
    pow_succ _ (_ + _), prod_pow_eq_pow_sum, h_exponent]
  field [prod_eq_zero_iff, Nat.Prime.ne_zero]

lemma inl_ne_coe_isFreeEntry (a : Fin 𝔰.ϱ) (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) :
    inl a ≠ j.val := by grind

lemma coe_isFreeEntry_ne_eStar (a : Fin 𝔰.ϱ) (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) :
    j.val ≠ eStar a := by grind

omit [CMType E] in
lemma rowCoords_one : rowCoords (1 : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) = 0 := by
  simp [rowCoords, freeRowCoords, imRowCoords, Prod.ext_iff, funext_iff, inl_ne_coe_isFreeEntry]

omit [CMType E] in
lemma rowCoords_injective : Injective (rowCoords (E := E) (𝔰 := 𝔰)) := by
  intro u u' h_eq
  obtain ⟨h_free, h_im⟩ := Prod.ext_iff.1 h_eq
  exact funext fun v ↦ injective_freeEntries_besselU (Prod.ext
    (funext fun ⟨(a, j), hj⟩ ↦ congrFun₂ (congrFun h_free a) ⟨j, hj⟩ v)
    (funext fun a ↦ congrFun₂ h_im a v))

omit [CMType E] in
/-- If the free entries (`freeRowCoords`) and the imaginary parts of the (e_d, e*_d) entry
(`imRowCoords`) of `u` vanish in every row e_d with d > a, then the free entries of `x * u` in the
row e_a are the sum of those of `u` and of `x`. -/
lemma rowCoords_mul_fst (x : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU)
    {u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU} {a : Fin 𝔰.ϱ}
    (h_free : ∀ d : Fin 𝔰.ϱ, a < d → freeRowCoords u d = 0)
    (h_im : ∀ d : Fin 𝔰.ϱ, a < d → imRowCoords u d = 0) :
    freeRowCoords (x * u) a = freeRowCoords u a + freeRowCoords x a := by
  funext j v
  refine besselU_mul_apply_eq_add (x v) (u v) (.inr j.2) (fun d hd ↦ congrFun (h_im d hd) v)
    fun d k hd hk ↦ congrFun₂ (h_free d ?_) ⟨k, hk⟩ v
  -- If the free column `j` is e*_d, then d > a.
  grind

omit [CMType E] in
/-- If the free entries of `u` vanish in the rows e_d with d ≥ a and the imaginary parts at
(e_d, e*_d) vanish for d > a, then at each place right multiplication by `u` adds the (e_a, e*_a)
entry of `u` to that of `x`. -/
lemma mul_apply_eStar_of_rowCoords {u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU}
    {a : Fin 𝔰.ϱ} (h_free : ∀ d : Fin 𝔰.ϱ, a ≤ d → freeRowCoords u d = 0)
    (h_im : ∀ d : Fin 𝔰.ϱ, a < d → imRowCoords u d = 0) (v : InfinitePlace E)
    (x : (𝔰.middleGram (1 : ℂ)).besselU) :
    (↑(x * u v) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) =
      (u v : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) +
        (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) := by
  refine besselU_mul_apply_eq_add x (u v) (.inl rfl) (fun d hd ↦ congrFun (h_im d hd) v)
    fun d k hd hk ↦ congrFun₂ (h_free d ?_) ⟨k, hk⟩ v
  simpa [le_iff_lt_or_eq] using hd

section Lattices

/-! In this section `c` is a class and e_a is a row; `S` is admissible unless this is omitted. -/

open scoped Classical

variable [HasPrimitiveRoot5040 E] [S.IsAdmissible]

/-- The transpose of the square block of the lattice basis `classBasis c` on the free columns
(`IsFreeEntry`) of the row e_a, as an invertible matrix. -/
noncomputable def freeBlock (c : S.Classes) (a : Fin 𝔰.ϱ) :
    GL {j : 𝔰.BesselIndex // IsFreeEntry (a, j)} (𝔸f E) :=
  .mk'' ((classBasis c).val.toSquareBlockProp fun j ↦ IsFreeEntry (a, j))ᵀ <| by
    obtain ⟨M, h_basis, -⟩ := exists_classBasis_eq_fromBlocks c
    simp [det_toSquareBlockProp_isFreeEntry h_basis]

lemma freeBlock_mulVec (c : S.Classes) (a : Fin 𝔰.ϱ) (l : 𝔰.BesselIndex → 𝔸f E)
    (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) :
    ((freeBlock c a).val *ᵥ l ∘ Subtype.val) j = (l ᵥ* (classBasis c).val) j := by
  obtain ⟨M, h_basis, -⟩ := exists_classBasis_eq_fromBlocks c
  exact transpose_toSquareBlockProp_mulVec h_basis a l j

lemma genIndex_det_freeBlock (c : S.Classes) (a : Fin 𝔰.ϱ) :
    genIndex (freeBlock c a).val.det = 1 / S.N ^ numInfPlaces E := by
  obtain ⟨M, h_basis, h_index⟩ := exists_classBasis_eq_fromBlocks c
  rw [← h_index, freeBlock, GeneralLinearGroup.val_mk'', det_transpose,
    det_toSquareBlockProp_isFreeEntry h_basis, h_basis]
  simp

omit [HasPrimitiveRoot5040 E] [S.IsAdmissible] in
variable (S) in
/-- For each `a`, the scales `S.M / S.basisScale v (inl a) * S.basisScale v j` are nonzero for all
infinite places `v` and all `j` with `IsFreeEntry (a, j)`. Here `inl a` indexes the basis vector
e_a. So this family of scales is a unit. -/
lemma isUnit_basisScale_ratio (a : Fin 𝔰.ϱ) :
    IsUnit fun (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) (v : InfinitePlace E) ↦
      (S.M : ℂ) / S.basisScale v (inl a) * S.basisScale v j := by
  simp [Nat.Prime.ne_zero, Pi.isUnit_iff]

/-- The lattice of free entries of the row e_a for the class `c`: the vectors with entries
`S.M / S.basisScale v e_a * S.basisScale v j * Φ v (x j)`, for the rational vectors `x` on the free
columns `j` such that `freeBlock c a *ᵥ x` is integral. Here `S.basisScale v j` is the scale of the
basis vector `j` at the infinite place `v`, and `Φ v` is the chosen complex embedding at `v`. -/
noncomputable def freeLattice (c : S.Classes) (a : Fin 𝔰.ϱ) :
    AddSubmonoid ({j : 𝔰.BesselIndex // IsFreeEntry (a, j)} → InfinitePlace E → ℂ) :=
  (Variety.classLattice (freeBlock c a)⁻¹ ⊥
    (ContinuousLinearEquiv.smulLeft (isUnit_basisScale_ratio S a).unit)).toAddSubmonoid

/-- Let `S` be a filling of shape `𝔰` over the CM field `E` containing a primitive 5040th root of
unity, with `S` admissible. For `c` in `S.Classes`, the lattice `freeLattice c a` of free entries of
the row e_a has a measurable strict fundamental domain. Its volume is `((∏ v, S.M ^
2 / S.frameScaleSq v a) / volÔ E) ^ (a.rev + (𝔰.k + 1) + a.rev)`, the exponent being the number of
free columns. -/
lemma exists_fundamental_domain_freeLattice (c : S.Classes) (a : Fin 𝔰.ϱ) :
    ∃ F : Set ({j : 𝔰.BesselIndex // IsFreeEntry (a, j)} → InfinitePlace E → ℂ),
      MeasurableSet F ∧
      volume.real F = ((∏ v : InfinitePlace E, (S.M : ℝ) ^ 2 / S.frameScaleSq v a) / volÔ E) ^
        (a.rev + (𝔰.k + 1) + a.rev : ℕ) ∧
      ∀ x : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)} → InfinitePlace E → ℂ,
        ∃! l : freeLattice c a, l.val + x ∈ F := by
  obtain ⟨F, hF_meas, hF_vol, hF_fund⟩ :=
    exists_fundamental_domain_classLattice _ (isUnit_basisScale_ratio S a) (freeBlock c a)
  exact ⟨F, hF_meas, by rw [hF_vol, genIndex_det_freeBlock, prod_norm_basisScale_sq_div_eq],
    hF_fund⟩

/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. The free entries
(`IsFreeEntry`) of the row e_a of the real image of any `γ ∈ S.classUnipotent c` lie in
`freeLattice c a`, the lattice of rescaled rational vectors `x` on the free columns with
`freeBlock c a *ᵥ x` integral. -/
lemma rowCoords_fst_mem_freeLattice (c : S.Classes) (a : Fin 𝔰.ϱ) (γ : S.classUnipotent c) :
    freeRowCoords (classUnipotentToInf c γ) a ∈ freeLattice c a := by
  let row : 𝔰.BesselIndex → 𝔸f E :=
    finAdeleMatrix ((S.M : E)⁻¹ • ((γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) - 1)) (inl a)
  have h_int (j : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)}) :
      ((freeBlock c a).val *ᵥ row ∘ Subtype.val) j ∈ Ô E := by
    simpa only [freeBlock_mulVec] using classUnipotent_sub_one_div_M_row_integral γ a j
  refine ⟨_, torsionClass_eq_zero.2 h_int, ?_⟩
  have hM : (S.M : ℂ) ≠ 0 := by simp [Nat.Prime.ne_zero]
  simp [funext_iff, mul_assoc, freeRowCoords, coe_classUnipotentToInf_apply,
    inl_ne_coe_isFreeEntry, field, -Nat.cast_mul]

/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. Fix a class `c` and
a row e_a; its free columns (`IsFreeEntry`) are e_b and e*_b with b > a and the middle block. Let
`l` lie in `freeLattice c a`: its entries are the rescaled complex embeddings of a rational vector
`x` on the free columns with `freeBlock c a *ᵥ x` integral, `freeBlock c a` being the transposed
block of the lattice basis of `c` on these columns. Then `l` is the vector of free entries in the
row e_a of the real image of some `γ ∈ S.classUnipotent c`, for which all coordinates `rowCoords`
vanish in the rows e_d with d > a. -/
lemma exists_rowCoords_fst_eq (c : S.Classes) (a : Fin 𝔰.ϱ)
    {l : {j : 𝔰.BesselIndex // IsFreeEntry (a, j)} → InfinitePlace E → ℂ}
    (hl : l ∈ freeLattice c a) :
    ∃ γ : S.classUnipotent c,
      freeRowCoords (classUnipotentToInf c γ) a = l ∧
      (∀ d : Fin 𝔰.ϱ, a < d → freeRowCoords (classUnipotentToInf c γ) d = 0) ∧
      ∀ d : Fin 𝔰.ϱ, a < d → imRowCoords (classUnipotentToInf c γ) d = 0 := by
  obtain ⟨x, hx, hxl⟩ := hl
  obtain ⟨M, h_basis, -⟩ := exists_classBasis_eq_fromBlocks c
  rw [← extend_comp Subtype.val_injective x 0] at hx hxl
  -- `x`, extended by zero off the free positions, has integral coordinates in the lattice basis.
  have hx_int : algebraMap E (𝔸f E) ∘ extend Subtype.val x 0 ᵥ* (classBasis c).val ∈
      intVectors (Ô E) 𝔰.BesselIndex := by
    intro j
    by_cases hj : IsFreeEntry (a, j)
    · rw [← freeBlock_mulVec c a _ ⟨j, hj⟩]
      exact torsionClass_eq_zero.1 hx _
    · revert j
      simp +contextual [vecMul_fromBlocks, h_basis]
  -- In the rows e_d, γ differs from 1 only in the row e_a and the column e*_a.
  obtain ⟨γ, hγ⟩ :=
    exists_eichler_classUnipotent c a (fun _ hj ↦ extend_val_apply' (g := x) hj) hx_int 0
  refine ⟨γ, ?_, fun d hd ↦ ?_, fun d hd ↦ ?_⟩
  · simp [funext_iff, mul_assoc, ← hxl, freeRowCoords, coe_classUnipotentToInf_apply, basisScale,
      field, inl_ne_coe_isFreeEntry, coe_isFreeEntry_ne_eStar, hγ]
  · have h_col (j : {j : 𝔰.BesselIndex // IsFreeEntry (d, j)}) : j.val ≠ eStar a := by grind
    simp [funext_iff, freeRowCoords, coe_classUnipotentToInf_apply, inl_ne_coe_isFreeEntry, hγ,
      h_col, hd.ne']
  · simp [funext_iff, imRowCoords, coe_classUnipotentToInf_apply, hγ, hd.ne']

/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. Suppose that at the
place `v`, right multiplication by the image `classUnipotentToInf c γ v` of `γ ∈ S.classUnipotent c`
adds its (e_a, e*_a) entry to that of every `x` in `besselU`. Then the imaginary parts of this entry
of `classUnipotentToInf c γ` at all places form a vector `(S.M / S.frameScaleSq w a * Im Φ_w(s))_w`
for an integer `s` of `E` with `star s = -s` (`imSkewLattice`). -/
lemma rowCoords_snd_mem_imSkewLattice (c : S.Classes) (a : Fin 𝔰.ϱ) (γ : S.classUnipotent c)
    (v : InfinitePlace E)
    (h_add : ∀ x : (𝔰.middleGram (1 : ℂ)).besselU,
      (↑(x * classUnipotentToInf c γ v) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) =
        (classUnipotentToInf c γ v : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a) +
          (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (inl a) (eStar a)) :
    imRowCoords (classUnipotentToInf c γ) a ∈
      imSkewLattice fun w : InfinitePlace E ↦ S.M / S.frameScaleSq w a := by
  -- The entry of γ at (e_a, e*_a) is `S.M` times s, with s integral and skew.
  refine ⟨IsIntegralClosure.mk' (𝓞 E) _ (isIntegral_inv_mul_apply_eStar γ a), RingOfIntegers.ext ?_,
    ?_⟩
  · simpa using star_inv_mul_apply_eStar_eq_neg γ v a h_add
  · have hM : (S.M : ℝ) ≠ 0 := by simp [Nat.Prime.ne_zero]
    simp [pow_mul', funext_iff, imRowCoords, coe_classUnipotentToInf_apply, basisScale, field,
      -Nat.cast_mul, -ofReal_div]

omit [S.IsAdmissible] in
/-- Let `E` contain a primitive 5040th root of unity. Fix a class `c` and a row e_a. Let `l` be a
vector `(S.M / S.frameScaleSq v a * Im Φ_v(s))_v` for an integer `s` of `E` with `star s = -s`
(`imSkewLattice`). Then `l` is the vector of imaginary parts at (e_a, e*_a) of the real image of
some `γ ∈ S.classUnipotent c` whose other coordinates `rowCoords` vanish. -/
lemma exists_rowCoords_snd_eq (c : S.Classes) (a : Fin 𝔰.ϱ) {l : InfinitePlace E → ℝ}
    (hl : l ∈ imSkewLattice fun v : InfinitePlace E ↦ S.M / S.frameScaleSq v a) :
    ∃ γ : S.classUnipotent c,
      imRowCoords (classUnipotentToInf c γ) a = l ∧
      freeRowCoords (classUnipotentToInf c γ) = 0 ∧
      ∀ d : Fin 𝔰.ϱ, d ≠ a → imRowCoords (classUnipotentToInf c γ) d = 0 := by
  obtain ⟨s, hs, hsl⟩ := hl
  obtain ⟨γ, hγ⟩ := exists_eichler_classUnipotent c a (l := 0) (by simp) (by simp) ⟨s, hs⟩
  refine ⟨γ, ?_, ?_, fun d hd ↦ ?_⟩
  · simp [pow_mul', funext_iff, mul_assoc, ← hsl, imRowCoords, coe_classUnipotentToInf_apply,
      basisScale, field, hγ, -ofReal_div]
  · funext d j v
    by_cases hd : d = a
    · subst hd
      simp [freeRowCoords, coe_classUnipotentToInf_apply, inl_ne_coe_isFreeEntry,
        coe_isFreeEntry_ne_eStar, hγ]
    · simp [freeRowCoords, coe_classUnipotentToInf_apply, inl_ne_coe_isFreeEntry, hγ, hd]
  · simp [funext_iff, imRowCoords, coe_classUnipotentToInf_apply, hγ, hd]

end Lattices

open scoped Classical in
/-- Let `S` be admissible and `c` a class, with finite adelic representative h_c. The group
`S.classUnipotent c` consists of the rational unipotent `γ` with h_c⁻¹ γ h_c in the principal
congruence subgroup of level `S.M`; let `Γ` be its image in the real unipotent group 𝖴_∞. In the
basis e₁, …, e_ϱ, middle block, e*₁, …, e*_ϱ, the map `rowCoords` sends a point of 𝖴_∞ to the free
entries of each row e_a and the imaginary parts of the entries at (e_a, e*_a), at all infinite
places. There are measurable sets `F a` and `F' a` such that each coset `u Γ` has exactly one point
with coordinates in the box over them. The product of the volumes of all `F a` and `F' a` is the
explicit number `S.unipotentCovolume`, which does not depend on `c`. -/
lemma exists_box_existsUnique_rowCoords_mem [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (c : S.Classes) :
    ∃ (F : ∀ a : Fin 𝔰.ϱ, Set ({j : 𝔰.BesselIndex // IsFreeEntry (a, j)} → InfinitePlace E → ℂ))
      (F' : Fin 𝔰.ϱ → Set (InfinitePlace E → ℝ)),
      (∀ a : Fin 𝔰.ϱ, MeasurableSet (F a)) ∧
      (∀ a : Fin 𝔰.ϱ, MeasurableSet (F' a)) ∧
      (∏ a : Fin 𝔰.ϱ, volume.real (F a)) * ∏ a : Fin 𝔰.ϱ, volume.real (F' a) = S.unipotentCovolume ∧
      ∀ u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU,
        ∃! γ : (classUnipotentToInf c).range,
          rowCoords (u * γ.val) ∈ Set.univ.pi F ×ˢ Set.univ.pi F' := by
  -- The group translates the coordinates by explicit lattices, in a triangular way. So
  -- `existsUnique_mul_mem_box` applies to fundamental domains of these lattices.
  choose F hF_meas hF_vol hF_fund using exists_fundamental_domain_freeLattice c
  choose F' hF'_meas hF'_vol hF'_fund using fun a : Fin 𝔰.ϱ ↦
    exists_fundamental_domain_im_skew (fun v ↦ S.M / S.frameScaleSq v a)
      (by simp [Nat.Prime.ne_zero])
  refine ⟨F, F', hF_meas, hF'_meas, ?_, fun u ↦ ?_⟩
  · simp only [hF_vol, hF'_vol, unipotentCovolume_eq_prod]
  -- The coordinates as one family: `inl a` for the free entries of the row e_a, `inr a` for the
  -- imaginary parts. The type names the additive group in which each coordinate lies.
  let coord (u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU) : ∀ i : Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ,
      (Sum.elim (fun a ↦ .of ({j // IsFreeEntry (a, j)} → InfinitePlace E → ℂ))
        (fun _ ↦ .of (InfinitePlace E → ℝ)) i : AddGrpCat) :=
    Sum.rec (freeRowCoords u) (imRowCoords u)
  have h_coord_inj : coord.Injective := fun _ _ h ↦
    rowCoords_injective (Prod.ext (funext (congrFun h <| inl ·)) (funext (congrFun h <| inr ·)))
  have h_coord_one_inl (d : Fin 𝔰.ϱ) : coord 1 (inl d) = 0 :=
    congrFun (congrArg Prod.fst rowCoords_one) d
  have h_coord_one_inr (d : Fin 𝔰.ϱ) : coord 1 (inr d) = 0 :=
    congrFun (congrArg Prod.snd rowCoords_one) d
  -- The last rows come first; in one row the free entries come before the imaginary part.
  let deg : Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ → ℕ := Sum.elim (fun a ↦ 2 * a.rev) fun a ↦ 2 * a.rev + 1
  -- What the vanishing of the coordinates of lower degree means, row by row.
  have h_low_inl {x : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU} {a : Fin 𝔰.ϱ}
      (h_low : ∀ i, deg i < deg (inl a) → coord x i = coord 1 i) :
      (∀ d, a < d → freeRowCoords x d = 0) ∧ ∀ d, a < d → imRowCoords x d = 0 :=
    ⟨fun d hd ↦ (h_low (inl d) (by grind)).trans (h_coord_one_inl d),
      fun d hd ↦ (h_low (inr d) (by grind)).trans (h_coord_one_inr d)⟩
  have h_low_inr {x : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU} {a : Fin 𝔰.ϱ}
      (h_low : ∀ i, deg i < deg (inr a) → coord x i = coord 1 i) :
      (∀ d, a ≤ d → freeRowCoords x d = 0) ∧ ∀ d, a < d → imRowCoords x d = 0 :=
    ⟨fun d hd ↦ (h_low (inl d) (by grind)).trans (h_coord_one_inl d),
      fun d hd ↦ (h_low (inr d) (by grind)).trans (h_coord_one_inr d)⟩
  refine (existsUnique_congr fun _ ↦ Sum.forall).1
    (existsUnique_mul_mem_box deg coord h_coord_inj (classUnipotentToInf c).range
      (Sum.rec (freeLattice c)
        fun a ↦ (imSkewLattice fun v ↦ S.M / S.frameScaleSq v a).toAddSubmonoid)
      (Sum.rec F F') (Sum.rec hF_fund hF'_fund) ?attained ?in_lattice ?translates u)
  case translates =>
    rintro γ (a | a) h_low x
    · obtain ⟨h_free, h_im⟩ := h_low_inl h_low
      exact rowCoords_mul_fst x h_free h_im
    · obtain ⟨h_free, h_im⟩ := h_low_inr h_low
      exact funext fun v ↦ congrArg im (mul_apply_eStar_of_rowCoords h_free h_im v (x v))
  case in_lattice =>
    rintro ⟨_, γ, rfl⟩ (a | a) h_low
    · exact rowCoords_fst_mem_freeLattice c a γ
    · obtain ⟨h_free, h_im⟩ := h_low_inr h_low
      exact rowCoords_snd_mem_imSkewLattice c a γ Classical.ofNonempty
        (mul_apply_eStar_of_rowCoords h_free h_im _)
  case attained =>
    rintro (a | a) l hl
    · obtain ⟨γ, hγ, h_free, h_im⟩ := exists_rowCoords_fst_eq c a hl
      refine ⟨⟨_, γ, rfl⟩, hγ, ?_⟩
      rintro (d | d) h_ne h_deg
      · exact (h_free d (by grind)).trans (h_coord_one_inl d).symm
      · exact (h_im d (by grind)).trans (h_coord_one_inr d).symm
    · obtain ⟨γ, hγ, h_free, h_im⟩ := exists_rowCoords_snd_eq c a hl
      refine ⟨⟨_, γ, rfl⟩, hγ, ?_⟩
      rintro (d | d) h_ne -
      · exact (congrFun h_free d).trans (h_coord_one_inl d).symm
      · exact (h_im d fun hd ↦ h_ne (congrArg inr hd)).trans (h_coord_one_inr d).symm

end Coordinates

/-- Let `E` contain a primitive 5040th root of unity and let `S` be admissible. For every class `c`
and archimedean point `y`, the integral of the cutoff `u ↦ S.classCutoff c (u y)` over the real
unipotent group 𝖴_∞, for the product of the Haar measures `New.Shape.besselHaar`, is the number
`S.unipotentCovolume`, which depends neither on `c` nor on `y`.

A case of the covolume computation for Heisenberg radicals, with a fixed product Haar measure in
place of Tate's self-dual measures. -/
lemma lintegral_classCutoff_eq_unipotentCovolume {E : Type} [Field E] [CMType E]
    [HasPrimitiveRoot5040 E] {𝔰 : Shape} (S : Filling E 𝔰) (c : S.Classes) [S.IsAdmissible]
    (y : InfinitePlace E → 𝔰.G₁) :
    ∫⁻ u : InfinitePlace E → (𝔰.middleGram (1 : ℂ)).besselU,
        S.classCutoff c (fun v : InfinitePlace E ↦ u v * y v) ∂(.pi fun _ ↦ 𝔰.besselHaar) =
      .ofReal S.unipotentCovolume := by
  classical
  -- The integral is the measure of a box that meets each coset of `S.classUnipotent c` once.
  obtain ⟨F, F', hF_meas, hF'_meas, h_vol, h_unique⟩ := exists_box_existsUnique_rowCoords_mem c
  have h_box : MeasurableSet (Set.univ.pi F ×ˢ Set.univ.pi F') :=
    (MeasurableSet.univ_pi hF_meas).prod (.univ_pi hF'_meas)
  have h_real : ((∏ a, volume (F a)) * ∏ a, volume (F' a)).toReal = S.unipotentCovolume := by
    simp [← h_vol, measureReal_def]
  rw [lintegral_classCutoff_eq_measure c y (measurePreserving_rowCoords.measurable h_box) h_unique,
    measurePreserving_rowCoords.measure_preimage h_box.nullMeasurableSet, Measure.prod_prod,
    volume_pi_pi, volume_pi_pi, ← h_real, ofReal_toReal]
  -- An infinite measure would have real value 0, but `S.unipotentCovolume` is positive.
  exact fun h_top ↦ S.unipotentCovolume_pos.ne (by simpa [h_top] using h_real)

end New.Filling

end UnipotentCovolume

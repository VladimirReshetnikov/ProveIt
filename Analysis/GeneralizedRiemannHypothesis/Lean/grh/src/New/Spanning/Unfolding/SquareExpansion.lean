import New.Spanning.RemainingTerms.Sum

/-!
# The expansion of the squares and the second moment near the Bessel subgroup

This file proves the expansion of the squares and the bound on the second moment near `R̄₀`, where
`R̄₀ = reducedImage besselS` is the reduction of the Bessel subgroup. These results concern the
operators `P_s = P* s P`, stated in terms of their blocks. The terms in the Bessel subgroup give the
operator `r_ψ(s)`, which is `New.Filling.besselTranslate`, and the terms off it give `P_s - r_ψ(s)`.
Along the way it treats the terms of cell rank `0` and the cosets `ζ R̄₀` by integral `ζ ∈ E` with
`ζ ζ̄ = 1`, called roots of unity (these are the roots of unity of `E`, by Kronecker's theorem), and
it computes the blocks of the Bessel subgroup.

## Main definitions and results

* `New.Filling.sqrt_secondMoment_compl_besselS_le`: the expansion of the squares.
* `New.Filling.secondMoment_compl_besselS_le`: `P_s` is close to `r_ψ(s)` near `R̄₀`.

Notions from other files:
* `termsOver c s c'`: the rational `γ` such that `h_c⁻¹ γ h_c'` (`translateByClassReps`) is integral
  with reduction `s`; such a `γ` lies over the block `(c, s, c')`.
* `amplitudeSum side T c s c'`: the sum of the amplitudes of the elements of `T` over that block.
* `secondMoment A Ω`: the sum of `‖A c s c'‖² / unipotentCovolume²` over all classes `c`, `c'` and
  `s ∈ Ω`.
* `reducedImage A`: the image in the finite group `ResidueGL` of the integral elements of `A`.
-/

namespace New

open Matrix Complex Module InnerProductSpace EuclideanSpace Finset Fintype

attribute [local instance low] Fintype.ofFinite

section Scalars

variable {R n : Type} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n] (J : Matrix n n R)

/-- A scalar `ζ` with `ζ ζ̄ = 1` as an isometry of the form `J`. -/
noncomputable def scalarIsometry (ζ : R) (hζ : ζ * star ζ = 1) : U J :=
  ⟨⟨ζ • 1, star ζ • 1, by simp [smul_smul, mul_comm, hζ], by simp [smul_smul, hζ]⟩,
    show (ζ • 1)ᴴ * J * (ζ • 1) = J by simp [smul_smul, hζ]⟩

lemma scalarIsometry_one (h : (1 : R) * star 1 = 1) : scalarIsometry J 1 h = 1 := by
  ext : 2
  simp [scalarIsometry]

/-- For `ζ ζ̄ = 1` and an isometry `g` of `J`, the matrix of `ζ⁻¹ g` is `ζ̄` times that of `g`. -/
lemma val_scalarIsometry_inv_mul {ζ : R} (hζ : ζ * star ζ = 1) (g : U J) :
    (((scalarIsometry J ζ hζ)⁻¹ * g : U J) : GL n R).val = star ζ • (g : GL n R).val := by
  simp [scalarIsometry]

end Scalars

/-- Let `ϱ > 0`, so that the first frame vector `e₁` is orthogonal to the frame. If `g` maps `e₁` to
a multiple of itself, then the leading minors of positive size of `frameGram g`, the matrix of the
products of the frame with its image under `g`, vanish. -/
lemma leadingMinor_frameGram_eq_zero {R : Type} [CommRing R] {𝔰 : Shape} (T : 𝔰.Form R)
    (hϱ : 0 < 𝔰.ϱ) {g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R}
    (hg : ∀ j : 𝔰.BesselIndex, j ≠ 𝔰.besselFrame 0 → g j (𝔰.besselFrame 0) = 0)
    {l : Fin (𝔰.ϱ + 2)} (hl : 0 < l.val) : leadingMinor (T.frameGram g) l = 0 := by
  have h_orth (b : Fin (𝔰.ϱ + 1)) : T.splitGram (𝔰.besselFrame b) (𝔰.besselFrame 0) = 0 := by
    rw [show 𝔰.besselFrame 0 = .inl ⟨0, hϱ⟩ from besselFrame_castSucc ⟨0, hϱ⟩]
    cases b using Fin.lastCases <;> simp [splitGram]
  have h_col (b : Fin (𝔰.ϱ + 1)) : T.frameGram g b 0 = 0 := by
    rw [Shape.Form.frameGram, submatrix_apply, mul_apply, Fintype.sum_eq_single (𝔰.besselFrame 0)
      fun j hj ↦ by rw [hg j hj, mul_zero], h_orth, zero_mul]
  exact det_eq_zero_of_column_eq_zero ⟨0, hl⟩ fun a ↦ h_col (Fin.castLE l.is_le a)

lemma sqrt_add_le_sqrt_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  rw [Real.sqrt_le_left (by positivity), add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
  linarith [mul_nonneg x.sqrt_nonneg y.sqrt_nonneg]

/-- A real function `β` of positive type on a group, that is, with `β (a⁻¹ b) = ⟪u a, u b⟫` for
vectors `u a` of an inner product space, is largest at `1`. -/
lemma le_apply_one_of_inner_eq {G V : Type*} [Group G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {β : G → ℝ} {u : G → V}
    (h_posType : ∀ a b : G, ⟪u a, u b⟫_ℂ = β (a⁻¹ * b)) (s : G) : β s ≤ β 1 := by
  have h_norm (a : G) : ‖u a‖ ^ 2 = β 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), h_posType, inv_mul_cancel, RCLike.re_to_complex, ofReal_re]
  calc β s = RCLike.re ⟪u 1, u s⟫_ℂ := by simp [h_posType]
    _ ≤ ‖u 1‖ * ‖u s‖ := re_inner_le_norm (u 1) (u s)
    _ ≤ β 1 := by linarith [two_mul_le_add_sq ‖u 1‖ ‖u s‖, h_norm 1, h_norm s]

open scoped Classical in
/-- The sum of `β` over the elements of a subgroup `H` with the property `p`, read in the whole
group. -/
lemma sum_subgroup_filter {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (p : G → Prop)
    (β : G → ℝ) : ∑ s : H with p s.val, β s.val = ∑ s : G with s ∈ H ∧ p s, β s := by
  rw [← filter_filter, sum_filter, sum_filter p, sum_subtype (p := (· ∈ H)) _ (by simp)]

/-- If row `j` of `M` vanishes before the index `b`, and `v` vanishes after `b` and is `1` at `b`,
then the entry `j` of `M v` is `M j b`. -/
lemma mulVec_apply_eq_of_eq_zero_of_lt {R m n : Type*} [Semiring R] [Fintype n] [LinearOrder n]
    {M : Matrix m n R} {v : n → R} {j : m} {b : n} (hM : ∀ a : n, a < b → M j a = 0)
    (hv : ∀ a : n, b < a → v a = 0) (hb : v b = 1) : (M *ᵥ v) j = M j b := by
  rw [mulVec_apply_eq_sum, Fintype.sum_eq_single b, hb, mul_one]
  intro a ha
  obtain h | h := ha.lt_or_gt <;> simp [hM, hv, h]

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- Suppose that for every index `a` the frame and its image under `γ` have a common vector that is
a combination of their vectors up to `a`, with coefficient `1` at `a` in both
(`PairOccursAt`). Then `γ` lies in the Bessel subgroup. -/
lemma mem_besselS_of_pairOccursAt {γ : S.G E}
    (h_pairs : ∀ a : Fin (𝔰.ϱ + 1), PairOccursAt γ 1 1 a) : γ ∈ besselS := by
  -- By induction on `b`, the vector `γ e_b` is `e_b` plus earlier frame vectors.
  have h_col (j : 𝔰.BesselIndex) (b : Fin (𝔰.ϱ + 1)) (hb : b.val ≤ BesselIndex.level j) :
      frameImage (γ : GL 𝔰.BesselIndex E).val j b = frameImage 1 j b := by
    induction b using WellFoundedLT.induction with | ind b ih
    obtain ⟨x, y, hxy, hx, hy, h_zero⟩ := h_pairs b
    -- In row `j` of the relation at index `b` only the two terms at `b` remain.
    have h_one (a : Fin (𝔰.ϱ + 1)) (ha : a < b) :
        frameImage (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) j a = 0 :=
      one_apply_ne fun hj : j = _ ↦ ha.not_ge (by rwa [hj, level_besselFrame] at hb)
    have h_γ (a : Fin (𝔰.ϱ + 1)) (ha : a < b) : frameImage (γ : GL _ E).val j a = 0 := by
      rw [ih a ha (le_trans ha.le hb), h_one a ha]
    rw [← mulVec_apply_eq_of_eq_zero_of_lt h_γ (fun a ha ↦ (h_zero a ha).2) hy,
      ← mulVec_apply_eq_of_eq_zero_of_lt h_one (fun a ha ↦ (h_zero a ha).1) hx, hxy]
  exact Filling.mem_besselS_iff_frameImage.2 h_col

/-- If the first frame vector satisfies `ζ e₁ = γ e₁` in the form of `PairOccursAt` at the
index `0`, then `ζ` is the diagonal entry of `γ` at `e₁`. -/
lemma PairOccursAt.apply_besselFrame_zero {γ : S.G E} {ζ : E}
    (h_pair : PairOccursAt γ ζ 1 0) :
    (γ : GL 𝔰.BesselIndex E).val (𝔰.besselFrame 0) (𝔰.besselFrame 0) = ζ := by
  obtain ⟨x, y, hxy, hx, hy, h_zero⟩ := h_pair
  simpa [mulVec_eq_sum, Fin.sum_univ_succ, hx, hy, h_zero, Matrix.one_apply] using
    congrFun hxy.symm (𝔰.besselFrame 0)

/-- Let `ζ ζ̄ = 1`. If the frame and its image under `γ` have common vectors with leading
coefficients `ζ` and `1` at every index, then `ζ⁻¹ γ` lies in the Bessel subgroup. -/
lemma scalarIsometry_inv_mul_mem_besselS {γ : S.G E} {ζ : E} (hζ : ζ * star ζ = 1)
    (h_pairs : ∀ a : Fin (𝔰.ϱ + 1), PairOccursAt γ ζ 1 a) :
    (scalarIsometry (S.ratMiddle E).splitGram ζ hζ)⁻¹ * γ ∈ (S.ratMiddle E).besselS := by
  refine mem_besselS_of_pairOccursAt fun a ↦ ?_
  obtain ⟨x, y, hxy, hx, hy, h_zero⟩ := h_pairs a
  refine ⟨star ζ • x, y, ?_, by simp [hx, mul_comm, hζ], hy, fun b hb ↦ by simp [h_zero b hb]⟩
  have h_smul : frameImage (star ζ • (γ : GL 𝔰.BesselIndex E).val) =
      star ζ • frameImage (γ : GL 𝔰.BesselIndex E).val := rfl
  rw [mulVec_smul, hxy, val_scalarIsometry_inv_mul, h_smul, smul_mulVec]

namespace Filling

/-! ### Terms of cell rank `0` and scalar cosets -/

/-- For `γ` in the Bessel subgroup and classes `c`, `c'` with representatives `h_c`, `h_c'`, the
finite adelic element `h_c⁻¹ γ h_c'` lies in the Bessel subgroup. -/
lemma translateByClassReps_mem_besselS {γ : S.G E} (hγ : γ ∈ besselS) (c c' : S.Classes) :
    S.translateByClassReps c c' γ ∈ besselS := by
  obtain ⟨u, hu, η, rfl⟩ := exists_besselU_mul_toBesselH hγ S.isUnit_natCast_N
  have h_rep (k : Gf E 𝔰.κ) : S.inclHFin k ∈ besselS :=
    mem_partialUnitriangularGroup_of_mem_floorGroup (inclHFin_mem_besselH k)
  -- The representatives `h_c`, `h_c'` are values of `inclHFin`.
  refine mul_mem (mul_mem (inv_mem (h_rep _)) ?_) (h_rep _)
  rw [map_mul, ratToFin_toBesselH]
  exact mul_mem (mem_partialUnitriangularGroup_of_mem_besselU (ratToFin_mem_besselU_iff.2 hu))
    (h_rep _)

/-- If `h_c⁻¹ γ h_c' = translateByClassReps c c' γ` is an element `k` of the stabilizer of the
lattice, then the diagonal entry of `γ` at the first frame vector `e₁` is integral, being the same
entry of `k`. -/
lemma apply_besselFrame_zero_mem_Ô {γ : S.G E} {c c' : S.Classes} {k : S.latticeStabilizer}
    (hk : (k : S.GFin) = S.translateByClassReps c c' γ) :
    ((γ : GL 𝔰.BesselIndex E).val (𝔰.besselFrame 0) (𝔰.besselFrame 0) : 𝔸f E) ∈ Ô E := by
  have h_first : 𝔰.besselFrame 0 = .inl ⟨0, pos_of_gt S.ten_pow_five_le_varrho⟩ :=
    besselFrame_castSucc ⟨0, _⟩
  have h_frame : frameImage ((k : S.GFin) : GL 𝔰.BesselIndex (𝔸f E)).val =
      S.classCoord c * finAdeleMatrix (frameImage (γ : GL 𝔰.BesselIndex E).val) := by
    rw [hk, frameImage_translateByClassReps]
  have h_entry : (k : S.GFin).val (𝔰.besselFrame 0) (𝔰.besselFrame 0) =
      ((γ : GL 𝔰.BesselIndex E).val (𝔰.besselFrame 0) (𝔰.besselFrame 0) : 𝔸f E) := by
    simpa [classCoord_eq_fromBlocks, mul_apply, Matrix.one_apply, h_first]
      using congrFun₂ h_frame (𝔰.besselFrame 0) 0
  rw [← h_entry]
  exact k.property.isIntMatrix _ _

/-- If the matrix of an element `z` of the stabilizer of the lattice is the scalar `ζ`, an integral
adele, then its reduction at a chosen place `w` is the residue of `ζ` at `w`. -/
lemma val_reduction_of_eq_smul_one {z : S.latticeStabilizer} {ζ : Ô E}
    (hz : ((z : S.GFin) : GL 𝔰.BesselIndex (𝔸f E)).val = (ζ : 𝔸f E) • 1)
    (i : Fin 2) (w : S.chosenPlaces i) :
    (S.reduction z i w).val = New.reduceAt (w : FinPlace E) ζ • 1 := by
  ext a b
  change New.reduceAt (w : FinPlace E) ⟨((z : S.GFin) : GL 𝔰.BesselIndex (𝔸f E)).val a b, _⟩ = _
  by_cases hab : a = b <;> simp [hz, hab, ← ZeroMemClass.zero_def]

/-- The classes `c`, `c'` are double cosets of the unitary group of the middle space `X₀`, with
representatives `h_c`, `h_c'`; a rational `γ` lies over the block `(c, s, c')` (`termsOver`) if
`h_c⁻¹ γ h_c'` is integral with reduction `s`. Let such a `γ` have norm-one pairs occurring from
level `0`: for one `ζ` with `ζ ζ̄ = 1`, the frame and its image under `γ` have common vectors with
leading coefficients `ζ`, `1` at every index. Then there is an integral `ζ` with `ζ ζ̄ = 1` such
that `γ` lies in `ζ` times the Bessel subgroup and `s` in `ζ` times the reduction of the Bessel
subgroup (`InScalarCoset`). -/
lemma exists_scalar_mul_besselS {γ : S.G E} {c c' : S.Classes} {s : S.ResidueGL}
    (hγ : γ ∈ S.termsOver c s c') (h_pair : NormOnePairOccursFrom 0 γ) :
    ∃ (ζ : E) (hζ : ζ * star ζ = 1) (h_int : (ζ : 𝔸f E) ∈ Ô E),
      (∃ γ₀ ∈ besselS, γ = scalarIsometry (S.ratMiddle E).splitGram ζ hζ * γ₀) ∧
        S.InScalarCoset ⟨ζ, h_int⟩ s := by
  obtain ⟨k, rfl, hk⟩ :
    ∃ k : S.latticeStabilizer, S.reduction k = s ∧ (k : S.GFin) = S.translateByClassReps c c' γ :=
      hγ
  obtain ⟨ζ, hζ, h_flag⟩ : ∃ ζ : E, ζ * star ζ = 1 ∧
    ∀ a : Fin (𝔰.ϱ + 1), 0 ≤ a.val → PairOccursAt γ ζ 1 a := h_pair
  -- `ζ` is the coefficient of `γ e₁ = ζ e₁`, an entry of the integral matrix `k`.
  have h_int : (ζ : 𝔸f E) ∈ Ô E := by
    simpa only [(h_flag 0 bot_le).apply_besselFrame_zero] using apply_besselFrame_zero_mem_Ô hk
  let γ₀ : S.G E := (scalarIsometry (S.ratMiddle E).splitGram ζ hζ)⁻¹ * γ
  have hγ₀ : γ₀ ∈ besselS := scalarIsometry_inv_mul_mem_besselS hζ fun a ↦ h_flag a bot_le
  -- The scalar `ζ` as an element `z` of the stabilizer of the lattice; `k = z k₀`.
  have hζ_fin : (ζ : 𝔸f E) * star (ζ : 𝔸f E) = 1 := by
    simpa using congrArg (algebraMap E (𝔸f E)) hζ
  let z : S.latticeStabilizer := ⟨scalarIsometry _ (ζ : 𝔸f E) hζ_fin,
    mem_intGL.2 ⟨IsIntMatrix.smul h_int .one, IsIntMatrix.smul (star_mem_Ô h_int) .one⟩⟩
  let k₀ : S.latticeStabilizer := z⁻¹ * k
  have hk₀ : (k₀ : S.GFin) = S.translateByClassReps c c' γ₀ := by
    ext : 2
    have hk₀_val : ((k₀ : S.GFin) : GL 𝔰.BesselIndex (𝔸f E)).val =
        star (ζ : 𝔸f E) • ((k : S.GFin) : GL 𝔰.BesselIndex (𝔸f E)).val :=
      val_scalarIsometry_inv_mul _ hζ_fin (k : S.GFin)
    have hγ₀_val : (γ₀ : GL 𝔰.BesselIndex E).val = star ζ • (γ : GL 𝔰.BesselIndex E).val :=
      val_scalarIsometry_inv_mul _ hζ γ
    rw [hk₀_val, hk, coe_translateByClassReps, coe_translateByClassReps]
    simp [hγ₀_val, Matrix.map_smul' _ _ _ (map_mul (algebraMap E (𝔸f E)))]
  have hk₀_mem : (k₀ : S.GFin) ∈ besselS := by
    simpa [hk₀] using translateByClassReps_mem_besselS hγ₀ c c'
  refine ⟨ζ, hζ, h_int, ⟨γ₀, hγ₀, (mul_inv_cancel_left _ γ).symm⟩, S.reduction k₀,
    ⟨k₀, hk₀_mem, rfl⟩, fun i w ↦ ?_⟩
  calc (S.reduction k i w).val = (S.reduction z i w).val * (S.reduction k₀ i w).val := by
        rw [← Units.val_mul, ← Pi.mul_apply, ← Pi.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = New.reduceAt (w : FinPlace E) ⟨ζ, h_int⟩ • (S.reduction k₀ i w).val := by
      rw [val_reduction_of_eq_smul_one (z := z) (ζ := ⟨ζ, h_int⟩) rfl, smul_one_mul]

/-- An integral element of the Bessel subgroup fixes the first frame vector `e₁`. -/
lemma apply_besselFrame_zero_of_mem_besselS {k : S.latticeStabilizer} (hk : (k : S.GFin) ∈ besselS)
    (j : 𝔰.BesselIndex) : (k : S.GFin).val j (𝔰.besselFrame 0) =
      (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)) j (𝔰.besselFrame 0) :=
  mem_besselS_iff_frameImage.1 hk j 0 bot_le

/-- An element `t` of the reduction of the Bessel subgroup fixes the first frame vector modulo
every chosen place `w`: its column there is that of the identity matrix. -/
lemma apply_besselFrame_zero_of_mem_reducedImage {t : S.ResidueGL} (ht : t ∈ S.reducedImage besselS)
    (i : Fin 2) (w : S.chosenPlaces i) (j : 𝔰.BesselIndex) :
    (t i w).val j (𝔰.besselFrame 0) =
      (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (ResField (w : FinPlace E))) j
        (𝔰.besselFrame 0) := by
  obtain ⟨k, hk, rfl⟩ := ht
  simpa using reduction_apply_congr 1 i w (apply_besselFrame_zero_of_mem_besselS hk j)

/-- Let `s` coincide, at the chosen places above `p_i`, with an element `t` of the reduction of the
Bessel subgroup. Then modulo each such place `w`, and modulo its conjugate (`isConj = true`), the
span of the frame and its image under `s` share a nonzero vector (`MeetsAt`), namely the first
frame vector. -/
lemma meetsAt_of_eq_of_mem_reducedImage {s t : S.ResidueGL} (ht : t ∈ S.reducedImage besselS)
    {i : Fin 2} (hs : s i = t i) (w : S.chosenPlaces i) (isConj : Bool) :
    S.MeetsAt s (⟨i, w⟩, isConj) := by
  obtain ⟨k, hk, rfl⟩ : ∃ k : S.latticeStabilizer, (k : S.GFin) ∈ besselS ∧ S.reduction k = t := ht
  have h_action : S.actionAt s (⟨i, w⟩, isConj) = S.actionAt (S.reduction k) (⟨i, w⟩, isConj) := by
    simp only [actionAt, hs]
  refine ⟨Pi.single 0 1, Pi.single 0 1, by simp, funext fun j ↦ ?_⟩
  have h_col : (k : S.GFin).val j (𝔰.besselFrame 0) = if j = 𝔰.besselFrame 0 then 1 else 0 := by
    rw [apply_besselFrame_zero_of_mem_besselS hk j, Matrix.one_apply]
  rw [h_action, actionAt_reduction, mulVec_single_one, mulVec_single_one]
  obtain rfl | hj := eq_or_ne j (𝔰.besselFrame 0)
  · simp [h_col, ← Submonoid.one_def, Matrix.one_apply]
  · simp [hj, h_col, ← ZeroMemClass.zero_def]

/-- An element `s` of `ζ` times the reduction of the Bessel subgroup is not open (`IsOpenElement`):
at every chosen place the leading minor of size `1` of the products of the frame with its image
under `s` vanishes. -/
lemma InScalarCoset.not_isOpenElement {ζ : Ô E} {s : S.ResidueGL} (hs : S.InScalarCoset ζ s) :
    ¬S.IsOpenElement s := by
  rintro ⟨w, hw⟩
  obtain ⟨t, ht, h_eq⟩ : ∃ t ∈ S.reducedImage besselS, ∀ (i : Fin 2) (v : S.chosenPlaces i),
    (s i v).val = New.reduceAt (v : FinPlace E) ζ • (t i v).val := hs
  have hϱ : 0 < 𝔰.ϱ := pos_of_gt S.ten_pow_five_le_varrho
  have h_col (j : 𝔰.BesselIndex) (hj : j ≠ 𝔰.besselFrame 0) :
      (s 0 w).val j (𝔰.besselFrame 0) = 0 := by
    simp [h_eq, apply_besselFrame_zero_of_mem_reducedImage ht, hj]
  exact hw ⟨1, Nat.succ_lt_succ hϱ⟩ (leadingMinor_frameGram_eq_zero _ hϱ h_col one_pos)

lemma inScalarCoset_one {s : S.ResidueGL} (hs : s ∈ S.reducedImage besselS) : S.InScalarCoset 1 s :=
  ⟨s, hs, by simp⟩

/-- If `s` is not in the reduction of the Bessel subgroup, the terms in the Bessel subgroup
contribute `0` to every block `(c, s, c')`, as none of them lies over it. -/
lemma amplitudeSum_besselS_eq_zero {side : FullOrCut} {s : S.ResidueGL}
    (hs : s ∉ S.reducedImage besselS)
    (c c' : S.Classes) : S.amplitudeSum side (S.ratMiddle E).besselS c s c' = 0 := by
  have h_empty : IsEmpty ↥(((S.ratMiddle E).besselS : Set (S.G E)) ∩ S.termsOver c s c') := by
    refine ⟨?_⟩
    rintro ⟨γ, hγ, k, rfl, hk⟩
    have hk_mem : (k : S.GFin) ∈ besselS := by
      simpa [hk] using translateByClassReps_mem_besselS hγ c c'
    exact hs ⟨k, hk_mem, rfl⟩
  rw [amplitudeSum, tsum_empty]

/-- The complement of the Bessel subgroup is stable under multiplication by the unipotent group
`besselU` on both sides. -/
lemma isStable_compl_besselS [HasPrimitiveRoot5040 E] :
    S.IsStable ((S.ratMiddle E).besselS : Set (S.G E))ᶜ :=
  fun u hu u' hu' γ ↦ (S.isStable_besselS u hu u' hu' γ).not

/-- Let `E` contain a primitive `5040`-th root of unity and let the filling `S` be admissible
(`IsAdmissible`). An integral `ζ ∈ E` with `ζ ζ̄ = 1` that is `1` modulo every place of
`chosenPlaces i`, the finite places of norm `p_i = levelPrime i` chosen in `S`, is `1`. -/
lemma eq_one_of_reduceAt_scalar_eq_one [HasPrimitiveRoot5040 E] [S.IsAdmissible] {ζ : E}
    (hζ : ζ * star ζ = 1) (h_int : (ζ : 𝔸f E) ∈ Ô E) (i : Fin 2)
    (h_residue : ∀ w : S.chosenPlaces i, New.reduceAt (w : FinPlace E) ⟨ζ, h_int⟩ = 1) : ζ = 1 := by
  -- View `ζ` as an isometry `z` of the standard lattice of rank one and apply freeness to it.
  let z : U (stdSpace E Unit).J := scalarIsometry (stdSpace E Unit).J ζ hζ
  let x : Gf E Unit := 1⁻¹ * stdEmbFin z * 1
  have h_mem : x ∈ stdLevel E Unit := mem_stdLevel.2 fun _ _ ↦ by
    simpa [x, z, scalarIsometry] using h_int
  have h_red (w : S.chosenPlaces i) : stdLevel.reduceAt (w : FinPlace E) ⟨x, h_mem⟩ = 1 := by
    ext
    simpa [stdLevel.reduceAt, x, z, scalarIsometry] using h_residue w
  have hz : z = 1 := S.eq_one_of_reduceAt_eq_one (by simp; linarith [S.thousand_mul_le_k]) i h_mem
    h_red
  simpa [z, scalarIsometry] using congrArg (fun g : U (stdSpace E Unit).J ↦ g.val () ()) hz

/-- The product `k f` of the rank `k` of `X₀` and the number `f` of infinite places of `E` is at
least `40`. -/
lemma forty_le_k_mul_numInfPlaces (S : Filling E 𝔰) : 40 ≤ 𝔰.k * Core.numInfPlaces E :=
  le_mul_of_le_of_one_le (by linarith [S.thousand_mul_le_k]) NeZero.one_le

/-- The set `Ω` is disjoint from the cosets `ζ R̄₀` of the reduction `R̄₀` of the Bessel subgroup,
for all integral `ζ ≠ 1` in `E` with `ζ ζ̄ = 1`. -/
def AvoidsScalarCosets (S : Filling E 𝔰) (Ω : Set S.ResidueGL) : Prop :=
  ∀ (ζ : E) (h_int : (ζ : 𝔸f E) ∈ Ô E), ζ * star ζ = 1 → ζ ≠ 1 →
    ∀ s ∈ Ω, ¬S.InScalarCoset ⟨ζ, h_int⟩ s

/-- Let `Ω` avoid the cosets of the reduction of the Bessel subgroup by the roots of unity `ζ ≠ 1`.
Then no `γ` off the Bessel subgroup that lies over a block `(c, s, c')` with `s ∈ Ω` has a norm-one
pair occurring from level `0`: such a `γ` is `ζ` times an element of the Bessel subgroup, and
`ζ = 1`. -/
lemma AvoidsScalarCosets.not_normOnePairOccursFrom_zero {Ω : Set S.ResidueGL}
    (hΩ : S.AvoidsScalarCosets Ω)
    (γ : S.G E) (h_off : γ ∈ ((S.ratMiddle E).besselS : Set (S.G E))ᶜ) (c c' : S.Classes)
    (s : S.ResidueGL) (hs : s ∈ Ω) (hγ : γ ∈ S.termsOver c s c') : ¬NormOnePairOccursFrom 0 γ := by
  intro h_pair
  obtain ⟨ζ, hζ, h_int, ⟨γ₀, hγ₀, rfl⟩, h_coset⟩ := exists_scalar_mul_besselS hγ h_pair
  obtain rfl : ζ = 1 := by_contra fun h_ne ↦ hΩ ζ h_int hζ h_ne s hs h_coset
  exact h_off (by simpa [scalarIsometry_one] using hγ₀)

/-- An element `γ` of the Bessel subgroup has a norm-one pair occurring from level `0`: at every
index, the frame and its image under `γ` have a common vector with both leading coefficients `1`. -/
lemma normOnePairOccursFrom_zero_of_mem_besselS {γ : S.G E} (hγ : γ ∈ besselS) :
    NormOnePairOccursFrom 0 γ := by
  refine ⟨1, by simp, fun a _ ↦ ?_⟩
  -- The vector `γ e_a` is `e_a` plus earlier frame vectors.
  let F : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) E := frameImage (γ : GL 𝔰.BesselIndex E).val
  have h_col (i : 𝔰.BesselIndex) (hi : a.val ≤ BesselIndex.level i) : F i a = frameImage 1 i a :=
    mem_besselS_iff_frameImage.1 hγ i a hi
  let x (b : Fin (𝔰.ϱ + 1)) : E := F (𝔰.besselFrame b) a
  have hx (b : Fin (𝔰.ϱ + 1)) (hb : a ≤ b) : x b = if b = a then 1 else 0 := by
    simpa [x, Matrix.one_apply, besselFrame_injective.eq_iff] using
      h_col (𝔰.besselFrame b) (by rwa [level_besselFrame])
  -- It has no part in `X₀` or along the dual vectors.
  have h_off (i : 𝔰.BesselIndex) (hi : 𝔰.ϱ ≤ BesselIndex.level i) (h_ne : i ≠ 𝔰.z) :
      F i a = 0 := by
    refine (h_col i (a.is_le.trans hi)).trans (one_apply_ne fun h : i = 𝔰.besselFrame a ↦ ?_)
    rw [h, level_besselFrame] at hi
    exact h_ne (by rw [h, Fin.last_le_iff.1 hi, besselFrame_top])
  have h_common : frameImage 1 *ᵥ x = F *ᵥ Pi.single a 1 := by
    rw [frameImage_one_mulVec, mulVec_single_one]
    -- The rows at `e₁, …, e_ϱ`, in `X₀`, at the last frame vector and at the dual vectors.
    ext (b | (j | j) | b)
    · simp [x, Fin.init]
    · exact (h_off (.inr (.inl (.inl j))) le_rfl (by simp)).symm
    · simp [x]
    · exact (h_off (.inr (.inr b)) (show 𝔰.ϱ ≤ 2 * 𝔰.ϱ - b.val by lia) (by simp)).symm
  exact ⟨x, Pi.single a 1, h_common, by simp [hx], by simp, fun b hb ↦ by simp [hx b hb.le, hb.ne']⟩

/-! ### The blocks of the Bessel subgroup -/

/-- Let `u` lie in the unipotent group `besselU`. At each infinite place `v`, let the image
`ratToInf η v` of `η` be `embedH (k v)`: the unitary matrix `k v` in `U(κ)` acts on `X₀` and the
other basis vectors are fixed. Then, for either `side` (full or cut), left translation by the image
of `u η` multiplies the values of `besselFn` by the tensor product (`kroneckerPi`) of the matrices
`rep (k v)` of the local Bessel systems `besselSystem v`, divided by `unipotentChar` of the finite
adelic image `ratToFin u`. -/
lemma besselFn_mul_of_eq_embedH {side : FullOrCut} {u η : S.G E} (hu : u ∈ besselU)
    {k : NumberField.InfinitePlace E → U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)}
    (hk : ∀ v : NumberField.InfinitePlace E, S.ratToInf η v = RealPlace.embedH (k v))
    (y : NumberField.InfinitePlace E → 𝔰.G₁) :
    S.besselFn side (S.ratToInf (u * η) * y) = ((S.unipotentChar (S.ratToFin u))⁻¹ •
      kroneckerPi fun v : NumberField.InfinitePlace E ↦ ((S.besselSystem v).rep (k v)).val) *ᵥ
        S.besselFn side y := by
  rw [map_mul, mul_assoc, besselFn_ratToInf_mul hu, smul_mulVec]
  have h_map (v : NumberField.InfinitePlace E) (h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) (z : 𝔰.G₁) :
      (S.besselSystem v).besselFn side (RealPlace.embedH h * z) =
        toEuclideanCLM (𝕜 := ℂ) ((S.besselSystem v).rep h).1 ((S.besselSystem v).besselFn side z) :=
    ((S.besselSystem v).isCutPair.isBesselFunction side).map_unitary_mul h z
  ext
  simp [besselFn, hk, h_map, kroneckerPi, mulVec, dotProduct, Fintype.prod_sum, prod_mul_distrib]

/-- For `side` either the full Bessel function or its cut, an element `γ` of the Bessel subgroup
`besselS` acts on the values of `besselFn side` by a unitary matrix. That is, there is a unitary `M`
indexed by `BesselCoord` with `besselFn side (ratToInf γ * y) = M *ᵥ besselFn side y` for all
`y`. -/
lemma exists_unitary_besselFn_mul {side : FullOrCut} {γ : S.G E} (hγ : γ ∈ besselS) :
    ∃ M ∈ unitaryGroup S.BesselCoord ℂ, ∀ y : NumberField.InfinitePlace E → 𝔰.G₁,
      S.besselFn side (S.ratToInf γ * y) = M *ᵥ S.besselFn side y := by
  obtain ⟨u, hu, η, hη, rfl⟩ := mem_besselS.1 hγ
  have h_comp (v : NumberField.InfinitePlace E) :
      ∃ k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), S.ratToInf η v = RealPlace.embedH k :=
    exists_eq_toBesselH (hη.ratToInf_mem_agreeWithOneOn v) isUnit_one
  choose k hk using h_comp
  let M : Matrix S.BesselCoord S.BesselCoord ℂ := (S.unipotentChar (S.ratToFin u))⁻¹ •
    kroneckerPi fun v : NumberField.InfinitePlace E ↦ ((S.besselSystem v).rep (k v)).1
  refine ⟨M, ?_, besselFn_mul_of_eq_embedH hu hk⟩
  -- A scalar of modulus one times a tensor product of unitary matrices is unitary.
  have h_star : star (kroneckerPi fun v ↦ ((S.besselSystem v).rep (k v)).1) =
      kroneckerPi fun v ↦ star ((S.besselSystem v).rep (k v)).1 := by
    ext
    simp [kroneckerPi]
  have h_norm : ‖S.unipotentChar (S.ratToFin u)‖ = 1 := norm_selfDualChar
  rw [mem_unitaryGroup_iff, star_smul, smul_mul_smul_comm, h_star, ← kroneckerPi_mul,
    Complex.star_def, mul_conj', norm_inv, h_norm]
  simp [kroneckerPi_one]

open scoped Classical in
/-- Let `E` contain a primitive `5040`-th root of unity and let the filling `S` be admissible
(`IsAdmissible`). The classes `c` index the double cosets of the unitary group of `X₀`, with
representatives `h_c`, and `termsOver c s c'` is the set of rational `γ` with `h_c⁻¹ γ h_c'`
integral of reduction `s`: these lie over the block `(c, s, c')`. Let `γ` in the Bessel subgroup
`besselS` lie over it and act on the values of the full Bessel function by the matrix `M`, whose
indices `BesselCoord` are the coordinates of those values. Then the sum of amplitudes
(`amplitudeSum`, for the full function) of the terms in the Bessel subgroup is
`unipotentCovolume • M` over this block and `0` over the blocks `(c, s, d)` with `d ≠ c'`; here
`unipotentCovolume` is the positive constant that stands for the covolume of the unipotent lattice
at a class. -/
lemma amplitudeSum_besselS_apply [HasPrimitiveRoot5040 E] [S.IsAdmissible] {γ : S.G E}
    {c c' : S.Classes} {s : S.ResidueGL} (hγ : γ ∈ besselS) (hγ_over : γ ∈ S.termsOver c s c')
    {M : Matrix S.BesselCoord S.BesselCoord ℂ}
    (hM : ∀ y : NumberField.InfinitePlace E → 𝔰.G₁,
      S.besselFn .full (S.ratToInf γ * y) = M *ᵥ S.besselFn .full y)
    (d : S.Classes) (i j : S.BesselCoord) :
    S.amplitudeSum .full (S.ratMiddle E).besselS c s d (i, j) =
      if c' = d then S.unipotentCovolume * M i j else 0 := by
  -- Translation by `γ` moves the block `(c', 1, d)` to `(c, s, d)` and acts by `M ⊗ 1`.
  let L := toEuclideanCLM (n := S.BesselCoord × S.BesselCoord) (𝕜 := ℂ) (kronecker M 1)
  have hL (x : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord)) (a b : S.BesselCoord) :
      L x (a, b) = ∑ k : S.BesselCoord, M a k * x (k, b) := by
    simp [L, mulVec, dotProduct, Matrix.one_apply, sum_prod_type]
  have h_kernel (δ : S.G E) (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      S.besselKernel .full (γ * δ * 1⁻¹) (S.ratToInf γ * y) = L (S.besselKernel .full δ y) := by
    ext ⟨a, b⟩
    simp [hL, besselKernel, mul_assoc, hM, mulVec, dotProduct, sum_mul]
  have h_move : S.amplitudeSum .full (S.ratMiddle E).besselS c s d =
      L (S.amplitudeSum .full (S.ratMiddle E).besselS c' 1 d) := by
    simpa using amplitudeSum_mul_mul_inv isStable_besselS hγ hγ_over (one_mem _)
      (S.classUnipotent d).one_mem.2 (by simp [hγ, mul_mem_cancel_left]) L h_kernel 1
  rw [h_move, hL]
  split_ifs with h <;> simp [h, amplitudeSum_besselS_one_eq_ite, apply_ite, mul_comm]

/-- Let `E` contain a primitive `5040`-th root of unity and let the filling `S` be admissible
(`IsAdmissible`). For classes `c`, `d` and `s` in `ResidueGL`, a term lies over the block
`(c, s, d)` (`termsOver`) if `h_c⁻¹ γ h_d` is integral with reduction `s`. The sum of amplitudes
(`amplitudeSum`, for the full Bessel function) of the terms in the Bessel subgroup `besselS` over
`(d, s⁻¹, c)` is the adjoint of that over `(c, s, d)`, as a matrix indexed by the coordinates of the
Bessel function. -/
lemma amplitudeSum_besselS_inv [HasPrimitiveRoot5040 E] [S.IsAdmissible] (c d : S.Classes)
    (s : S.ResidueGL) (i j : S.BesselCoord) :
    S.amplitudeSum .full (S.ratMiddle E).besselS d s⁻¹ c (j, i) =
      star (S.amplitudeSum .full (S.ratMiddle E).besselS c s d (i, j)) := by
  by_cases h : ∃ γ ∈ (S.ratMiddle E).besselS, γ ∈ S.termsOver c s d
  · -- If `γ` acts by the unitary matrix `M`, then `γ⁻¹` acts by its adjoint.
    obtain ⟨γ, hγ, hγ_over⟩ := h
    obtain ⟨M, hM_unitary, hM⟩ := exists_unitary_besselFn_mul (side := .full) hγ
    have hM_inv (y : NumberField.InfinitePlace E → 𝔰.G₁) :
        S.besselFn .full (S.ratToInf γ⁻¹ * y) = star M *ᵥ S.besselFn .full y := by
      rw [← mul_inv_cancel_left (S.ratToInf γ) y, hM]
      simp [mem_unitaryGroup_iff'.1 hM_unitary]
    simp [amplitudeSum_besselS_apply hγ hγ_over hM,
      amplitudeSum_besselS_apply (inv_mem hγ) (termsOver.inv hγ_over) hM_inv]
  · have h_empty : IsEmpty ↥(((S.ratMiddle E).besselS : Set (S.G E)) ∩ S.termsOver c s d) :=
      ⟨fun γ ↦ h ⟨γ, γ.2⟩⟩
    have h_empty_inv : IsEmpty ↥(((S.ratMiddle E).besselS : Set (S.G E)) ∩ S.termsOver d s⁻¹ c) :=
      ⟨fun ⟨γ, hγ, hγ_over⟩ ↦ h ⟨γ⁻¹, inv_mem hγ, by simpa using termsOver.inv hγ_over⟩⟩
    simp [amplitudeSum, tsum_empty]

/-- Let `E` contain a primitive `5040`-th root of unity and let the filling `S` be admissible
(`IsAdmissible`). Let `δ` in the Bessel subgroup lie over `(d, t, d')` and act on the values of the
full Bessel function by `N`, and let `T` be a set of terms that is stable with `T δ = T`. Then the
sum of amplitudes of `T`, for the full function, over `(c, s t⁻¹, d)` is `A Nᴴ`, where `A` is that
over `(c, s, d')`. -/
lemma amplitudeSum_mul_inv_apply [HasPrimitiveRoot5040 E] [S.IsAdmissible] {T : Set (S.G E)}
    (hT : S.IsStable T) {δ : S.G E} {d d' : S.Classes} {t : S.ResidueGL} (hδ : δ ∈ besselS)
    (hδ_over : δ ∈ S.termsOver d t d') (hT_mul_inv : ∀ γ : S.G E, γ ∈ T ↔ γ * δ⁻¹ ∈ T)
    {N : Matrix S.BesselCoord S.BesselCoord ℂ}
    (hN : ∀ y : NumberField.InfinitePlace E → 𝔰.G₁,
      S.besselFn .full (S.ratToInf δ * y) = N *ᵥ S.besselFn .full y)
    (c : S.Classes) (s : S.ResidueGL) (i j : S.BesselCoord) :
    S.amplitudeSum .full T c (s * t⁻¹) d (i, j) =
      ∑ k : S.BesselCoord, star (N j k) * S.amplitudeSum .full T c s d' (i, k) := by
  -- Translation by `δ⁻¹` on the right acts on the kernel by `1 ⊗ conj N`.
  let L := toEuclideanCLM (n := S.BesselCoord × S.BesselCoord) (𝕜 := ℂ) (kronecker 1 (N.map star))
  have hL (x : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord)) (a b : S.BesselCoord) :
      L x (a, b) = ∑ k : S.BesselCoord, star (N b k) * x (a, k) := by
    simp [L, mulVec, dotProduct, Matrix.one_apply, sum_prod_type]
  have h_kernel (γ : S.G E) (y : NumberField.InfinitePlace E → 𝔰.G₁) :
      S.besselKernel .full (1 * γ * δ⁻¹) (S.ratToInf 1 * y) = L (S.besselKernel .full γ y) := by
    ext ⟨a, b⟩
    simp [hL, besselKernel, mul_assoc, hN, mulVec, dotProduct, mul_sum, mul_left_comm]
  have h_move : S.amplitudeSum .full T c (s * t⁻¹) d = L (S.amplitudeSum .full T c s d') := by
    simpa using amplitudeSum_mul_mul_inv hT (one_mem _) (S.classUnipotent c).one_mem.2 hδ hδ_over
      (by simpa using hT_mul_inv) L h_kernel s
  rw [h_move, hL]

/-! ### The expansion of the squares and the second moment near `R̄₀` -/

/-- Let `E` contain a primitive `5040`-th root of unity and let the filling `S` be admissible
(`IsAdmissible`). Let `Ω` avoid the cosets `ζ R̄₀` of the roots of unity `ζ ≠ 1`, and let `s ∈ Ω`.
Then over each block at `s` the terms off the Bessel subgroup `besselS` have the same sum of
amplitudes as the terms of `Γ* = remainingTerms`. These are the `γ` with `termDisc γ ≠ 0`, and those
with agreeing characters that move the span of the isotropic frame vectors `e₁, …, e_ϱ`. -/
lemma AvoidsScalarCosets.amplitudeSum_compl_besselS_eq [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    {side : FullOrCut} {Ω : Set S.ResidueGL} (hΩ : S.AvoidsScalarCosets Ω) {s : S.ResidueGL}
    (hs : s ∈ Ω) (c c' : S.Classes) :
    S.amplitudeSum side (S.ratMiddle E).besselSᶜ c s c' =
      S.amplitudeSum side S.remainingTerms c s c' := by
  -- The terms off `R₀` and `Γ*` whose characters do not agree (`CharsAgree` fails) form a stable
  -- set with sum `0`. One whose characters agree has a norm-one pair occurring from level `0`, so
  -- lies over no block at `s`.
  set offBessel : Set (S.G E) := ((S.ratMiddle E).besselS : Set (S.G E))ᶜ
  set agreeing : Set (S.G E) := {γ | S.CharsAgree γ}
  have h_sub : offBessel ∩ S.remainingTerms = S.remainingTerms :=
    Set.inter_eq_right.2 fun γ hγ h_mem ↦
      (normOnePairOccursFrom_zero_of_mem_besselS h_mem).notMem_remainingTerms hγ
  have h_stable : S.IsStable (offBessel ∩ S.remainingTermsᶜ ∩ agreeingᶜ) := fun u hu u' hu' γ ↦ by
    simp only [Set.mem_inter_iff, Set.mem_compl_iff S.remainingTerms, Set.mem_compl_iff agreeing]
    rw [isStable_compl_besselS u hu u' hu' γ, isStable_remainingTerms u hu u' hu' γ]
    simp only [offBessel, agreeing, Set.mem_ofPred_eq,
      charsAgree_mul_mul_iff_of_mem_besselU (inv_mem hu) hu']
  have h_disagree : S.amplitudeSum side (offBessel ∩ S.remainingTermsᶜ ∩ agreeingᶜ) c s c' = 0 :=
    amplitudeSum_eq_zero_of_not_charsAgree h_stable (fun γ hγ ↦ hγ.2) c s c'
  have h_empty : IsEmpty ↥(offBessel ∩ S.remainingTermsᶜ ∩ agreeing ∩ S.termsOver c s c') :=
    ⟨fun ⟨γ, ⟨⟨h_off, h_out⟩, h_agree⟩, h_over⟩ ↦
      hΩ.not_normOnePairOccursFrom_zero γ h_off c c' s hs h_over
      (CharsAgree.normOnePairOccursFrom_zero h_agree h_out)⟩
  have h_agree : S.amplitudeSum side (offBessel ∩ S.remainingTermsᶜ ∩ agreeing) c s c' = 0 :=
    tsum_empty
  rw [amplitudeSum_eq_inter_compl_add_inter offBessel S.remainingTerms, h_sub,
    amplitudeSum_eq_inter_compl_add_inter (offBessel ∩ S.remainingTermsᶜ) agreeing]
  simp [h_disagree, h_agree]

/-- Let `E` contain a primitive `5040`-th root of unity, let the filling `S` be admissible
(`IsAdmissible`), and let `Ω` avoid the cosets of the reduction of the Bessel subgroup by the roots
of unity `ζ ≠ 1`. For each block over `Ω` and each link, sum the amplitudes for the cut Bessel
function of the terms with that link and nonzero `termDisc`; let the squared norms of these sums
(`linkSecondMoment`) add up to at most `C unipotentCovolume²`, with `C ≥ 0` and the positive
constant `unipotentCovolume` that stands for the covolume of the unipotent lattice at a class. Then
the second moment over `Ω` of the terms off the Bessel subgroup, for the full Bessel function, has
square root at most `C^(1/2) + b⁻¹⁵ 𝒟_id^(1/2)`, where `b = S.b` and `𝒟_id = identitySecondMoment`
is the order of the reduction of the Bessel subgroup times the number `sourceDim` of pairs of a
class and a coordinate. -/
theorem sqrt_secondMoment_compl_besselS_le [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    {Ω : Set S.ResidueGL} (hΩ : S.AvoidsScalarCosets Ω) {C : ℝ} (hC : 0 ≤ C)
    (h_links : linkSecondMoment {γ : S.G E | S.termDisc γ ≠ 0} Ω ≤ .ofReal
      (C * S.unipotentCovolume ^ 2)) :
    √(secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) Ω) ≤
      √C + (S.b ^ 15)⁻¹ * √S.identitySecondMoment := by
  classical
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have h_id_nonneg : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  set remaining : Set (S.G E) := S.remainingTerms
  -- Over `Ω` the blocks of `P_s - r_ψ(s)` are those of `Γ*`.
  have h_blocks : secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) Ω =
      secondMoment (S.amplitudeSum .full remaining) Ω :=
    sum_congr rfl fun c _ ↦ sum_congr rfl fun c' _ ↦ sum_congr rfl fun s hs ↦ by
      rw [hΩ.amplitudeSum_compl_besselS_eq (mem_filter.1 hs).2]
  have h_sqrt : √((S.b ^ 40)⁻¹ * S.identitySecondMoment) = (S.b ^ 20)⁻¹ *
    √S.identitySecondMoment := by
    rw [Real.sqrt_mul' _ h_id_nonneg, Real.sqrt_inv, pow_mul _ 20 2, Real.sqrt_sq (by positivity)]
  -- The pairs of terms with the same link give `C`, the other pairs at most `b^(-kf) 𝒟_id`.
  have h_pairs : secondMoment (S.amplitudeSum .cut remaining) Ω ≤ C + (S.b ^ 40)⁻¹ *
    S.identitySecondMoment := by
    grw [secondMoment_remainingTerms_le hC h_links,
      ← pow_le_pow_right₀ S.one_le_b S.forty_le_k_mul_numInfPlaces, div_eq_inv_mul]
  have h_small : 2 * (S.b ^ 5)⁻¹ ≤ 1 := by
    grw [← hb]
    norm_num
  calc _ ≤ √(secondMoment (S.amplitudeSum .full remaining - S.amplitudeSum .cut remaining) Ω) +
        √(secondMoment (S.amplitudeSum .cut remaining) Ω) := by
        grw [h_blocks, ← sqrt_secondMoment_add_le, sub_add_cancel]
    -- Passing to the cut function costs `b⁻²⁰ 𝒟_id^(1/2)`.
    _ ≤ (S.b ^ 20)⁻¹ * √S.identitySecondMoment + (√C + (S.b ^ 20)⁻¹ * √S.identitySecondMoment) := by
      grw [secondMoment_sub_cut_le, h_pairs, sqrt_add_le_sqrt_add_sqrt hC (by positivity), h_sqrt]
    _ = √C + 2 * (S.b ^ 5)⁻¹ * ((S.b ^ 15)⁻¹ * √S.identitySecondMoment) := by ring
    _ ≤ √C + (S.b ^ 15)⁻¹ * √S.identitySecondMoment := by grw [h_small, one_mul]

/-- Let `E` contain a primitive `5040`-th root of unity and let the filling `S` be admissible
(`IsAdmissible`). Let `s` coincide, at the chosen places above `p_i = levelPrime i`, with an element
`t` of `reducedImage besselS`, the reduction of the Bessel subgroup. Then the product of the norms
`p_i` of these places and their conjugates is at most `meetNorm s`, the product of the norms of the
places at which `s` meets, as `s` meets at each of them. -/
lemma prod_levelPrime_le_meetNorm_of_eq [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    {s t : S.ResidueGL} (ht : t ∈ S.reducedImage besselS) {i : Fin 2} (hs : s i = t i) :
    ∏ _ : S.chosenPlaces i × Bool, S.levelPrime i ≤ S.meetNorm s := by
  classical
  let φ (p : S.chosenPlaces i × Bool) : (Σ j, S.chosenPlaces j) × Bool := (⟨i, p.1⟩, p.2)
  have hφ : φ.Injective := fun p p' h ↦ by simpa [φ, Prod.ext_iff] using h
  have h_meet : ∀ p ∈ univ.image φ, S.MeetsAt s p :=
    forall_mem_image.2 fun p _ ↦ meetsAt_of_eq_of_mem_reducedImage ht hs p.1 p.2
  exact (prod_image hφ.injOn).symm.trans_le (prod_le_meetNorm h_meet)

/-- The set of the `s` that coincide with an element of `R̄₀`, the reduction of the Bessel subgroup,
at the chosen places above `p_i` avoids the cosets `ζ R̄₀` with `ζ ≠ 1`: such an `s` fixes the first
frame vector there, so `ζ` is `1` modulo these places. -/
lemma avoidsScalarCosets_setOf_exists_apply_eq [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (i : Fin 2) : S.AvoidsScalarCosets
      {s : S.ResidueGL | ∃ t ∈ S.reducedImage besselS, s i = t i} := by
  rintro ζ h_int hζ h_ne s ⟨t, ht, hs⟩ ⟨t', ht', h_coset⟩
  refine h_ne (S.eq_one_of_reduceAt_scalar_eq_one hζ h_int i fun w ↦ ?_)
  have h_entry : (s i w).1 (𝔰.besselFrame 0) (𝔰.besselFrame 0) =
      New.reduceAt w.1 ⟨ζ, h_int⟩ * (t' i w).1 (𝔰.besselFrame 0) (𝔰.besselFrame 0) := by
    rw [h_coset i w, Matrix.smul_apply, smul_eq_mul]
  rw [hs, apply_besselFrame_zero_of_mem_reducedImage ht,
    apply_besselFrame_zero_of_mem_reducedImage ht', one_apply_eq, mul_one] at h_entry
  exact h_entry.symm

/-- Each level prime `levelPrime i` is at most `b` times the other, so `M / b ≤ p_i ^ 2`, with
`p_i = levelPrime i`, for the level `M = p₀ p₁`. -/
lemma M_div_b_le_levelPrime_sq (i : Fin 2) : S.M / S.b ≤ (S.levelPrime i : ℝ) ^ 2 := by
  have hb : 0 < S.b := one_pos.trans_le S.one_le_b
  have h_le (j : Fin 2) : (S.levelPrime j : ℝ) ≤ S.levelPrime i * S.b := by
    grw [S.levelPrime_le j, ← S.le_levelPrime i, ← pow_succ]
  rw [div_le_iff₀ hb, M, Nat.cast_mul, sq, mul_assoc]
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · grw [h_le 1]
  · grw [mul_comm, h_le 0]

/-- The second moment near the Bessel subgroup. Let `E` contain a primitive `5040`-th root of unity
and let the filling `S` be admissible (`IsAdmissible`). Let `Ω` be the set of `s` that coincide with
an element of `R̄₀` at the chosen places above `p_i`. Then the second moment over `Ω` of the terms
off the Bessel subgroup, that is `∑ ‖P_s - r_ψ(s)‖²`, is at most `b⁻¹² 𝒟_id`. Here `P_s` and
`r_ψ(s)` are the operators whose blocks at `s` are the conjugates of the amplitude sums of all terms
and of the terms in the Bessel subgroup, divided by `unipotentCovolume`, `R̄₀` is the reduction of
the Bessel subgroup, `p_i = levelPrime i`, `b` is the parameter `S.b` of the filling and
`𝒟_id = identitySecondMoment = #R̄₀ D_X`, with `D_X = sourceDim` the number of pairs of a class and
a coordinate. -/
theorem secondMoment_compl_besselS_le [HasPrimitiveRoot5040 E] [hS : S.IsAdmissible] (i : Fin 2) :
    secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ)
      {s : S.ResidueGL | ∃ t ∈ S.reducedImage besselS, s i = t i} ≤ (S.b ^ 12)⁻¹ *
        S.identitySecondMoment := by
  classical
  have hb : 1000 ≤ S.b := S.thousand_le_b
  have h_id_nonneg : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_main_nonneg : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  set Ω : Set S.ResidueGL := {s | ∃ t ∈ S.reducedImage besselS, s i = t i}
  set meetBound : ℕ := ∏ _ : S.chosenPlaces i × Bool, S.levelPrime i with h_meetBound_def
  have h_meetBound_ne : meetBound ≠ 0 :=
    prod_ne_zero_iff.2 fun _ _ ↦ (S.levelPrime_prime_and_ne i).1.ne_zero
  -- Every `s ∈ Ω` meets at the `f` chosen places above `p_i` and at their conjugates.
  have h_meet : ∀ s ∈ Ω, meetBound ≤ S.meetNorm s := fun s ⟨t, ht, hs⟩ ↦
    prod_levelPrime_le_meetNorm_of_eq ht hs
  -- With `m = k f`, `meetBound ≥ (M / b)^f` and `𝒟_main ≤ (M / b⁶)^m 𝒟_id`, the sums over links
  -- give at most `(b³ / M)^m (M / b⁶)^m 𝒟_id = b^(-3m) 𝒟_id ≤ b⁻³⁰ 𝒟_id`.
  have h_links : (S.b ^ (2 * Core.numInfPlaces E) / meetBound) ^ 𝔰.k * S.mainSecondMoment ≤
      (S.b ^ 30)⁻¹ * S.identitySecondMoment := by
    have hM : (0 : ℝ) < S.M := Nat.cast_pos.2 (two_pos.trans_le two_le_M)
    have h_meetBound_ge : (S.M / S.b) ^ Core.numInfPlaces E ≤ meetBound := by
      grw [h_meetBound_def, prod_const, card_univ, Fintype.card_prod, S.card_chosenPlaces,
          Fintype.card_bool,
        Nat.cast_pow, pow_mul', M_div_b_le_levelPrime_sq]
    have h_exp : 30 ≤ 3 * (𝔰.k * Core.numInfPlaces E) := by
      linarith [S.forty_le_k_mul_numInfPlaces]
    calc _ ≤ (S.b ^ (2 * Core.numInfPlaces E) / (S.M / S.b) ^ Core.numInfPlaces E) ^ 𝔰.k *
          ((S.M / S.b ^ 6) ^ (𝔰.k * Core.numInfPlaces E) * S.identitySecondMoment) := by
          grw [hS.mainSecondMoment_le, ← h_meetBound_ge]
      _ = (S.b ^ (3 * (𝔰.k * Core.numInfPlaces E)))⁻¹ * S.identitySecondMoment := by
        simp only [div_pow]
        field
      _ ≤ (S.b ^ 30)⁻¹ * S.identitySecondMoment := by grw [pow_le_pow_right₀ S.one_le_b h_exp]
  have h_sqrt : √(secondMoment (S.amplitudeSum .full (S.ratMiddle E).besselSᶜ) Ω) ≤
      2 * (S.b ^ 15)⁻¹ * √S.identitySecondMoment :=
    calc _ ≤ √((S.b ^ (2 * Core.numInfPlaces E) / meetBound) ^ 𝔰.k * S.mainSecondMoment) +
          (S.b ^ 15)⁻¹ * √S.identitySecondMoment :=
          sqrt_secondMoment_compl_besselS_le (avoidsScalarCosets_setOf_exists_apply_eq i)
            (by positivity)
            (linkSecondMoment_le_of_le_meetNorm h_meetBound_ne h_meet)
      _ ≤ √((S.b ^ 30)⁻¹ * S.identitySecondMoment) + (S.b ^ 15)⁻¹ * √S.identitySecondMoment := by
        grw [h_links]
      _ = 2 * (S.b ^ 15)⁻¹ * √S.identitySecondMoment := by
        rw [Real.sqrt_mul' _ h_id_nonneg, Real.sqrt_inv, pow_mul _ 15 2,
          Real.sqrt_sq (by positivity)]
        ring
  have h_small : (2 * (S.b ^ 15)⁻¹) ^ 2 ≤ (S.b ^ 12)⁻¹ := by
    have h_four : 4 ≤ S.b ^ 18 := le_trans (by linarith) (le_self_pow₀ S.one_le_b (by norm_num))
    field_simp
    linarith
  grw [(Real.sqrt_le_iff.1 h_sqrt).2, mul_pow, Real.sq_sqrt h_id_nonneg, h_small]

end Filling

end New

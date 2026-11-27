import New.Spanning.Unfolding.ReducedPoints

/-!
# Class cutoffs and counting frames in boxes

The translates of the cutoff `S.classCutoff c` of a class `c` are shown to add up to one, and
weights bounded by cutoffs are shown to add up to at most a bound for the number of frames in a box.

## Main definitions and results

* `New.Filling.frameImage_eq_frameImage_one_of_close`: a term that moves the frame vectors of a
  point in a box very little fixes the frame.
* `New.Filling.encard_image_frameImage_le`: terms `γ` with `γ⁻¹ y` in a box have few images of the
  frame, since the frame vectors of the points `γ⁻¹ y` lie in a ball and are separated.
* `New.Filling.tsum_le_of_le_classCutoff_mul`: weights bounded by cutoffs add up to at most that
  bound for the number of frames.

Notions from other files:
* `New.frameImage`, `New.frameVector`: the image `γ f` of the frame `f = (e₁, …, e_ϱ, z)` under a
  matrix `γ`, and the vector `y⁻¹ f_a` in Euclidean space.
* `New.frameBox`, `New.besselLength`: the points whose frame vectors have norm at most `ρ`, and the
  infimum of `‖s y‖ + 1` (operator norm) over `s` in the Bessel subgroup.
* `New.Filling.frameBoxRadius`, `New.Filling.basisScale`: the number `S.b ^ (37 n)`, and the scales
  of the normalised basis at an infinite place.
* `New.Filling.classUnipotent`, `New.Filling.classCutoff`: the congruence group of rational
  unipotent elements attached to a class `c`, and a cutoff for its subgroup fixing the frame times
  the indicator of the reduced points.
* `New.Filling.termsOver`: the rational `γ` with `h_c⁻¹ γ h_c'` integral and of reduction `s`, where
  `h_c` is the representative `New.Filling.classRep` of the class `c`.
* `New.Filling.IsAdmissible`: the standing hypotheses, among them the size inequalities between
  `S.b`, `S.realM v` and `S.N`.
-/
section BoxPartition

open ENNReal Fin Matrix Module Set Norms.L2Operator Subgroup

namespace New.Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
/-- Let `γ`, `γ'` be rational elements of the unitary group whose images `γ f`, `γ' f` of the frame
`f = (e₁, …, e_ϱ, z)` differ only in the coordinates along the `e_a`. At an infinite place `v`, the
`b`-th frame vectors of `γ⁻¹ y` and `γ'⁻¹ y` then differ by a combination of the vectors `y⁻¹ e_a`.
The coefficient of `y⁻¹ e_a` is the difference of the coordinates along `e_a`, embedded by `Φ v` and
multiplied by the ratio of the scales of `f_b` and `e_a` in the normalised basis at `v`
(`S.basisScale v`). -/
lemma frameVector_sub_eq_sum {γ γ' : S.G E}
    (h_rows : (frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₂ =
      (frameImage (γ' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₂)
    (y : 𝔰.G₁) (v : NumberField.InfinitePlace E) (b : Fin (𝔰.ϱ + 1)) :
    frameVector ((S.ratToInf γ v)⁻¹ * y) b - frameVector ((S.ratToInf γ' v)⁻¹ * y) b =
      ∑ a : Fin 𝔰.ϱ,
        (Φ v ((γ - γ' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (Sum.inl a) (𝔰.besselFrame b)) *
            (S.basisScale v (𝔰.besselFrame b) / S.basisScale v (𝔰.besselFrame a.castSucc))) •
          frameVector y a.castSucc := by
  ext i
  -- The coordinates of `(u⁻¹ y)⁻¹ f_b = y⁻¹ (u f_b)`.
  have h_coord (u : S.G E) : frameVector ((S.ratToInf u v)⁻¹ * y) b i =
      ∑ j : 𝔰.BesselIndex, y⁻¹.val i j * (Φ v (u.val j (𝔰.besselFrame b)) *
        (S.basisScale v (𝔰.besselFrame b) / S.basisScale v j)) := by
    simp [frameVector, Matrix.mul_apply]
  have h_lower (j : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) :
      γ.val (Sum.inr j) (𝔰.besselFrame b) = γ'.val (Sum.inr j) (𝔰.besselFrame b) :=
    congr_fun₂ h_rows j b
  rw [PiLp.sub_apply, h_coord, h_coord, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [h_lower]
  simp [frameVector, mul_sub, mul_comm]

/-- Reduction of frames: for every class `c` and every point `y` at the infinite places, some `u` in
the congruence group `S.classUnipotent c` of rational unipotent elements makes all entries of
`gramSchmidtMatrix` of the components of `u y` at most `S.b ^ 26` in absolute value. Here
`gramSchmidtMatrix x` is the upper unitriangular matrix expressing the frame vectors
`x⁻¹ e₁, …, x⁻¹ e_ϱ, x⁻¹ z` in their Gram–Schmidt orthogonalisation. -/
lemma exists_gramSchmidtMatrix_le [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (c : S.Classes) (y : NumberField.InfinitePlace E → 𝔰.G₁) :
    ∃ u : S.classUnipotent c, ∀ (v : NumberField.InfinitePlace E) (a b : Fin (𝔰.ϱ + 1)),
      ‖gramSchmidtMatrix (S.ratToInf u v * y v) a b‖ ≤ S.b ^ 26 := by
  obtain ⟨D, hD⟩ : ∃ D : Set (NumberField.InfinitePlace E → ℂ), S.IsResidueDomain D :=
    S.exists_isResidueDomain
  obtain ⟨u, hu⟩ : ∃ u₀ : S.classUnipotent c, ∀ u : S.classUnipotent c,
      S.ratToInf u * y ∈ S.reducedPoints D ↔ (u * u₀⁻¹).val ∈ S.classUnipotent₀ c :=
    hD.exists_mul_mem_reducedPoints_iff_rightCoset c y
  exact ⟨u, hD.norm_gramSchmidtMatrix_le ((hu u).2 (by simp))⟩

/-- The indicator of the reduced points for the chosen set of representatives is a partition of
unity in boxes (`IsBoxPartitionOfUnity`) for every class `c`. -/
lemma isBoxPartitionOfUnity_reducedIndicator [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (c : S.Classes) :
    S.IsBoxPartitionOfUnity c S.reducedIndicator :=
  IsResidueDomain.isBoxPartitionOfUnity (Classical.epsilon_spec S.exists_isResidueDomain) c

/-- Let `ω` be a partition of unity in boxes for the class `c`: a weight whose translates under
`S.classUnipotent c` add up to one modulo the subgroup fixing the frame, and which vanishes unless
the frame vectors `(y v)⁻¹ f_a` have norm at most `b ^ 27` times `besselLength (y v)`, the infimum
of `‖s (y v)‖ + 1` over `s` in the Bessel subgroup. Here `b = S.b`. If `ω y ≠ 0` and
`besselLength (y v)` is at most `b ^ (6 n + 2) R` with `n = 𝔰.n`, then the frame vectors of `y v`
have norm at most `frameBoxRadius * R`. -/
lemma IsBoxPartitionOfUnity.mem_frameBox {c : S.Classes}
    {ω : (NumberField.InfinitePlace E → 𝔰.G₁) → ℝ≥0∞}
    (hω : S.IsBoxPartitionOfUnity c ω) {y : NumberField.InfinitePlace E → 𝔰.G₁} (hy : ω y ≠ 0)
    {v : NumberField.InfinitePlace E} {R : ℝ} (hR : 0 ≤ R)
    (h_size : besselLength (y v) ≤ S.b ^ (6 * 𝔰.n + 2) * R) :
      y v ∈ frameBox (S.frameBoxRadius * R) := by
  intro a
  have hb : 1 ≤ S.b := S.one_le_b
  grw [hω.mem_frameBox_besselLength y v hy a, h_size, frameBoxRadius, ← mul_assoc, ← pow_add]
  -- Exponents of `b`: `27 + 6 n + 2 ≤ 37 n`.
  gcongr
  nlinarith [S.ten_pow_five_le_varrho]

/-- The cutoff `S.classCutoff c` of a class `c` is a cutoff for the rational unipotent elements
fixing the frame, times the indicator of the reduced points. If it is not zero at `y` and
`besselLength (y v)`, the infimum of `‖s (y v)‖ + 1` over `s` in the Bessel subgroup, is at most
`b ^ (6 n + 2) R`, with `b = S.b` and `n = 𝔰.n`, then the frame vectors `(y v)⁻¹ f_a` have norm at
most `frameBoxRadius * R`, where `frameBoxRadius = b ^ (37 n)`. -/
lemma mem_frameBox_of_classCutoff_ne_zero [HasPrimitiveRoot5040 E] [S.IsAdmissible] {c : S.Classes}
    {y : NumberField.InfinitePlace E → 𝔰.G₁} (hy : S.classCutoff c y ≠ 0)
    {v : NumberField.InfinitePlace E} {R : ℝ} (hR : 0 ≤ R)
    (h_size : besselLength (y v) ≤ S.b ^ (6 * 𝔰.n + 2) * R) :
      y v ∈ frameBox (S.frameBoxRadius * R) := by
  rw [classCutoff] at hy
  exact (isBoxPartitionOfUnity_reducedIndicator c).mem_frameBox (right_ne_zero_of_mul hy) hR h_size

/-- If the cutoff of the class `c` is not zero at `y` and all components of `y` have length at most
`S.b ^ (6 n + 2)` with `n = 𝔰.n` (`InCut`), then `y` lies in the set `boxedPoints` of reduced points
in the cut. -/
lemma mem_boxedPoints_of_classCutoff_ne_zero {c : S.Classes}
    {y : NumberField.InfinitePlace E → 𝔰.G₁} (hy : S.classCutoff c y ≠ 0)
    (h_cut : ∀ v : NumberField.InfinitePlace E, InCut (y v) S.b) : y ∈ S.boxedPoints := by
  rw [classCutoff] at hy
  exact mem_boxedPoints_of_reducedIndicator_ne_zero (right_ne_zero_of_mul hy) h_cut

/-- The translates of `S.classCutoff c` under the congruence group `S.classUnipotent c` of rational
unipotent elements add up to one at every point `y`. -/
lemma tsum_classCutoff_eq_one [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    (c : S.Classes) (y : NumberField.InfinitePlace E → 𝔰.G₁) :
    ∑' u : S.classUnipotent c, S.classCutoff c (S.ratToInf u * y) = 1 := by
  obtain ⟨β, hβ, -, hβ_sum⟩ := S.exists_classCutoff_eq_mul c
  -- The translates of `β` add up to one on each coset of `S.classUnipotent₀ c`.
  rw [hβ]
  refine (isBoxPartitionOfUnity_reducedIndicator c).tsum_mul_eq_one y
    (fun u ↦ β (S.ratToInf u * y)) fun γ ↦ ?_
  simpa [mul_assoc] using hβ_sum (S.ratToInf γ * y)

/-- Let `f = (e₁, …, e_ϱ, z)` be the frame. If the hermitian products `S.frameProducts g b a` of
`f_b` with `g f_a` equal those of `f_b` with `f_a` for all `b`, then `g` moves `f_a` only along the
vectors `e_i`: all other coordinates of `g f_a` and `f_a` agree. -/
lemma frameImage_inr_eq_of_frameProducts_eq {g : S.G E} {a : Fin (𝔰.ϱ + 1)}
    (h : ∀ b : Fin (𝔰.ϱ + 1), S.frameProducts g b a = S.frameProducts 1 b a) :
    ∀ i : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ,
      frameImage (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (Sum.inr i) a =
        frameImage 1 (Sum.inr i) a := by
  -- `h` gives the coordinates along `e*_i` and `z`. Unitarity then says that the middle part of
  -- `g f_a - f_a` is isotropic for `S.ratMiddle E`, which is anisotropic off `z`, so that part
  -- vanishes too.
  let w (i : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) : E :=
    (g - 1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (Sum.inr i) (𝔰.besselFrame a)
  have h_dual (i : Fin 𝔰.ϱ) : w (Sum.inr i) = 0 := by
    cases a using lastCases <;>
      simpa [w, frameGram, splitGram, Matrix.mul_apply, Matrix.one_apply] using h i.castSucc
  have h_z : w (Sum.inl (Sum.inr ())) = 0 := by
    cases a using lastCases <;>
      simpa [w, frameGram, splitGram, middleGram, Matrix.mul_apply, Matrix.one_apply, sub_eq_zero,
        S.N_prime.ne_zero] using h (last 𝔰.ϱ)
  have h_unitary :
      ((g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)ᴴ * (S.ratMiddle E).splitGram * g).diag
        (𝔰.besselFrame a) = (S.ratMiddle E).splitGram.diag (𝔰.besselFrame a) :=
    congr_fun₂ g.prop (𝔰.besselFrame a) (𝔰.besselFrame a)
  have h_isotropic : star (w ∘ Sum.inl) ⬝ᵥ S.ratMiddle E *ᵥ (w ∘ Sum.inl) = 0 := by
    -- Expand `h_unitary`; the terms pairing `e_i` with `e*_i` vanish by `h_dual`.
    cases a using lastCases with
    | last =>
      have h_dual_zero (i : Fin 𝔰.ϱ) : g.val (Sum.inr (Sum.inr i)) 𝔰.z = 0 := by
        simpa [w, Matrix.one_apply] using h_dual i
      have h_z_one : g.val 𝔰.z 𝔰.z = 1 := by simpa [w, sub_eq_zero] using h_z
      simpa [w, splitGram, middleGram, mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply,
        h_dual_zero, h_z_one] using h_unitary
    | cast a =>
      have h_dual_zero (i : Fin 𝔰.ϱ) : g.val (Sum.inr (Sum.inr i)) (Sum.inl a) = 0 := by
        simpa [w, Matrix.one_apply] using h_dual i
      simpa [w, splitGram, middleGram, mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply,
        h_dual_zero, mul_assoc] using h_unitary
  have h_middle : w ∘ Sum.inl = 0 := S.eq_zero_of_ratMiddle_form_eq_zero _ h_z h_isotropic
  rintro (j | i)
  · exact sub_eq_zero.1 (congr_fun h_middle j)
  · exact sub_eq_zero.1 (h_dual i)

/-- The hermitian products `S.frameProducts` of the frame vector `f_b` with `γ f_a` and with
`γ' f_a` differ, under the embedding `Φ v` at the place `v`, by at most `S.N` times the norm of
`y⁻¹ f_b` times the distance of the `a`-th frame vectors of `γ⁻¹ y` and `γ'⁻¹ y`. -/
lemma norm_Φ_frameProducts_sub_le [S.IsAdmissible]
    (γ γ' : S.G E) (y : 𝔰.G₁) (v : NumberField.InfinitePlace E) (a b : Fin (𝔰.ϱ + 1)) :
    ‖Φ v (S.frameProducts γ b a - S.frameProducts γ' b a)‖ ≤
      S.N * (‖frameVector y b‖ *
        ‖frameVector ((S.ratToInf γ v)⁻¹ * y) a - frameVector ((S.ratToInf γ' v)⁻¹ * y) a‖) := by
  let F (u : S.G E) : EuclideanSpace ℂ 𝔰.BesselIndex := frameVector ((S.ratToInf u v)⁻¹ * y) a
  let t : ℝ := S.realM v ^ (𝔰.ϱ - b) * S.realM v ^ (𝔰.ϱ - a)
  have ht : 1 ≤ |t| := by
    rw [abs_mul, abs_pow, abs_pow]
    bound [S.one_le_abs_realM]
  have hN : (S.N : ℝ) ≠ 0 := mod_cast S.N_prime.ne_zero
  have h_inner (u : S.G E) : inner ℂ (frameVector y b) (toEuclideanLin 𝔰.J₁ (F u)) =
      (t / S.N : ℝ) * Φ v (S.frameProducts u b a) := by
    rw [← realFrameGram_eq_inner, realFrameGram_ratToInf]
  have h_sub : inner ℂ (frameVector y b) (toEuclideanLin 𝔰.J₁ (F γ - F γ')) =
      (t / S.N : ℝ) * Φ v (S.frameProducts γ b a - S.frameProducts γ' b a) := by
    rw [map_sub, inner_sub_right, h_inner, h_inner, map_sub, mul_sub]
  calc _ ≤ |t| * ‖Φ v (S.frameProducts γ b a - S.frameProducts γ' b a)‖ :=
        le_mul_of_one_le_left (norm_nonneg _) ht
    _ = S.N * ‖inner ℂ (frameVector y b) (toEuclideanLin 𝔰.J₁ (F γ - F γ'))‖ := by
        rw [h_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, Nat.abs_cast]
        field
    _ ≤ S.N * (‖frameVector y b‖ * ‖F γ - F γ'‖) := by grw [norm_inner_J₁_le]

/-- For a term `γ` over `(c, s, c')`, the coordinates along the `e_a` of the images `γ f_b` of the
frame vectors `e₁, …, e_ϱ, z` are algebraic integers. -/
lemma termsOver.isIntegral_inl_besselFrame {c c' : S.Classes} {s : S.ResidueGL} {γ : S.G E}
    (hγ : γ ∈ S.termsOver c s c') (a : Fin 𝔰.ϱ) (b : Fin (𝔰.ϱ + 1)) :
    IsIntegral ℤ (γ.val (Sum.inl a) (𝔰.besselFrame b)) := by
  have h_int : (S.translateByClassReps c c' γ).val (Sum.inl a) (𝔰.besselFrame b) ∈ Ô E :=
    termsOver.isIntMatrix_translateByClassReps hγ (Sum.inl a) (𝔰.besselFrame b)
  -- The change to the lattice bases of `c` and `c'` keeps this entry.
  cases b using lastCases <;>
    simpa [coe_translateByClassReps, classBasis, toBesselH, besselLatticeBasis, Matrix.mul_apply,
      Matrix.one_apply] using h_int

/-- The scales `S.basisScale v` that normalise the basis at the place `v`
(`S.realM v ^ (ϱ - a + 1) / √N` on `e_a`, `1 / √N` on `z`) of two frame vectors differ by a factor
of at most `S.b ^ (23 ϱ)`. -/
lemma one_le_pow_mul_norm_basisScale_div [S.IsAdmissible]
    (v : NumberField.InfinitePlace E) (a b : Fin (𝔰.ϱ + 1)) :
    1 ≤ S.b ^ (23 * 𝔰.ϱ) *
      ‖S.basisScale v (𝔰.besselFrame b) / S.basisScale v (𝔰.besselFrame a)‖ := by
  have h_realM : 1 ≤ |S.realM v| := S.one_le_abs_realM v
  have hN : (√S.N : ℂ) ≠ 0 := by simp [S.N_prime.ne_zero]
  have h_quot : ‖S.basisScale v (𝔰.besselFrame b) / S.basisScale v (𝔰.besselFrame a)‖ =
      |S.realM v| ^ (𝔰.ϱ - b) / |S.realM v| ^ (𝔰.ϱ - a) := by
    rw [basisScale_besselFrame, basisScale_besselFrame, div_div_div_cancel_right₀ hN]
    simp
  rw [h_quot, ← mul_div_assoc, one_le_div₀ (by positivity)]
  calc |S.realM v| ^ (𝔰.ϱ - a) ≤ (S.b ^ 23) ^ 𝔰.ϱ := by grw [Nat.sub_le, abs_realM_le]
    _ ≤ S.b ^ (23 * 𝔰.ϱ) * |S.realM v| ^ (𝔰.ϱ - b) := by
        rw [← pow_mul]
        exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans S.one_le_b) _)
          (one_le_pow₀ h_realM)

/-- Let `f = (e₁, …, e_ϱ, z)` be the frame. Suppose that `γ f` and `γ' f` differ only along the
`e_x`, and that `γ f_b` and `γ' f_b` have the same coordinates along `e_x` for `x > a`. Then the
difference of their coordinates along `e_a`, times the ratio of the scales of `f_b` and `e_a` in
the normalised basis at `v` (`S.basisScale v`), is at most the operator norm `‖w y‖` times the
distance of the `b`-th frame vectors of `γ⁻¹ y` and `γ'⁻¹ y`, for every `w` in the unipotent
subgroup `besselU`, whose rows along the `e_a` are unitriangular. -/
lemma norm_Φ_sub_mul_norm_basisScale_div_le {γ γ' : S.G E}
    (h_rows : (frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₂ =
      (frameImage (γ' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)).toRows₂)
    {a : Fin 𝔰.ϱ} {b : Fin (𝔰.ϱ + 1)}
    (h_later : ∀ x : Fin 𝔰.ϱ, a < x →
      γ.val (Sum.inl x) (𝔰.besselFrame b) = γ'.val (Sum.inl x) (𝔰.besselFrame b))
    {w : 𝔰.G₁} (hw : w ∈ besselU) (y : 𝔰.G₁) (v : NumberField.InfinitePlace E) :
    ‖Φ v (γ.val (Sum.inl a) (𝔰.besselFrame b) - γ'.val (Sum.inl a) (𝔰.besselFrame b))‖ *
        ‖S.basisScale v (𝔰.besselFrame b) / S.basisScale v (𝔰.besselFrame a.castSucc)‖ ≤
      ‖((w * y : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ *
        ‖frameVector ((S.ratToInf γ v)⁻¹ * y) b - frameVector ((S.ratToInf γ' v)⁻¹ * y) b‖ := by
  have h_triangular (x : Fin 𝔰.ϱ) (hx : x ≤ a) :
      w.val (Sum.inl a) (𝔰.besselFrame x.castSucc) = if a = x then 1 else 0 := by
    simpa [Matrix.one_apply] using mem_besselU.1 hw (Sum.inl a) (Sum.inl x) hx
  rw [frameVector_sub_eq_sum h_rows, ← norm_mul]
  refine Eq.trans_le ?_ (norm_sum_le_mul_norm_sum_frameVector castSucc _ (Sum.inl a))
  -- Only the term `x = a` is left in row `a` of `w` applied to the combination.
  rw [Fintype.sum_eq_single a, h_triangular a le_rfl, ite_eq_left rfl, mul_one, Matrix.sub_apply]
  intro x hx
  rcases hx.lt_or_gt with h_lt | h_gt
  · rw [h_triangular x h_lt.le, ite_eq_right hx.symm, mul_zero]
  · rw [Matrix.sub_apply, h_later x h_gt, sub_self, map_zero, zero_mul, zero_mul]

variable [S.IsAdmissible]

/-- **Rigidity of frames.** Let `E` be a CM field and `S` admissible filling data over `E`
(`IsAdmissible`), with parameters `b = S.b` and `N = S.N`, a prime. Let `g` be a term over some
`(d, r, d')`: a rational element with `h_d⁻¹ g h_d'` integral and of reduction `r`, where `h_d` is
the representative of the class `d` (`termsOver`). Let `R ≥ 1`, `n = 𝔰.n` and
`ρ = frameBoxRadius * R` with `frameBoxRadius = b ^ (37 n)`. The frame is `f = (e₁, …, e_ϱ, 𝔰.z)`.
Let `z` be a point at the infinite places such that at every place the infimum `besselLength` of
`‖s z‖ + 1` over the Bessel subgroup is at most `b ^ (6 n + 2) R` and the frame vectors `z⁻¹ f_a`
have norm at most `ρ`. If the frame vectors of `g⁻¹ z` and `z` are at distance less than `(N ρ)⁻¹`
at every place, then `g` fixes the frame, that is, `g f = f`. -/
lemma frameImage_eq_frameImage_one_of_close {g : S.G E} {d : S.Classes} {r : S.ResidueGL}
    {d' : S.Classes}
    (hg : g ∈ S.termsOver d r d') {z : NumberField.InfinitePlace E → 𝔰.G₁} {R : ℝ} (hR : 1 ≤ R)
    (h_box : ∀ v : NumberField.InfinitePlace E, z v ∈ frameBox (S.frameBoxRadius * R))
    (h_size : ∀ v : NumberField.InfinitePlace E, besselLength (z v) ≤ S.b ^ (6 * 𝔰.n + 2) * R)
    (h_close : ∀ (v : NumberField.InfinitePlace E) (a : Fin (𝔰.ϱ + 1)),
      ‖frameVector ((S.ratToInf g v)⁻¹ * z v) a - frameVector (z v) a‖ <
        (S.N * (S.frameBoxRadius * R))⁻¹) :
    frameImage (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) = frameImage 1 := by
  have hb_one : 1 ≤ S.b := S.one_le_b
  have hρ : 0 < S.frameBoxRadius * R := by
    rw [frameBoxRadius]
    positivity
  have hNρ : 0 < S.N * (S.frameBoxRadius * R) := mul_pos (mod_cast S.N_prime.pos) hρ
  let δ (v : NumberField.InfinitePlace E) (a : Fin (𝔰.ϱ + 1)) : ℝ :=
    ‖frameVector ((S.ratToInf g v)⁻¹ * z v) a - frameVector ((S.ratToInf 1 v)⁻¹ * z v) a‖
  -- An integral function whose change from `1` to `g` is at most `N ρ` times the move `δ` of a
  -- frame vector does not change: the change is an algebraic integer of norm `< 1` at all places.
  have h_rigid {f : S.G E → E}
      (h_int : ∀ {c : S.Classes} {s : S.ResidueGL} {c' : S.Classes} {γ : S.G E},
        γ ∈ S.termsOver c s c' → IsIntegral ℤ (f γ))
      (a : Fin (𝔰.ϱ + 1))
      (h_le : ∀ v : NumberField.InfinitePlace E,
        ‖Φ v (f g - f 1)‖ ≤ S.N * (S.frameBoxRadius * R) * δ v a) : f g = f 1 := by
    have h_sub : IsIntegral ℤ (f g - f 1) := (h_int hg).sub (h_int (S.classUnipotent d).one_mem.2)
    refine sub_eq_zero.1 (eq_zero_of_forall_norm_lt_one h_sub fun v ↦ (h_le v).trans_lt ?_)
    rw [← lt_div_iff₀' hNρ]
    simpa [δ] using h_close v a
  have h_gram (a b : Fin (𝔰.ϱ + 1)) : S.frameProducts g b a = S.frameProducts 1 b a := by
    refine h_rigid (fun hγ ↦ isIntegral_frameProducts hγ b a) a fun v ↦ ?_
    grw [norm_Φ_frameProducts_sub_le g 1 (z v), h_box v b, ← mul_assoc]
  have h_lower (i : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) (b : Fin (𝔰.ϱ + 1)) :
      frameImage (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) (Sum.inr i) b =
        frameImage 1 (Sum.inr i) b :=
    frameImage_inr_eq_of_frameProducts_eq (h_gram b) i
  -- The coordinates along the `e_a` remain: downward induction on `a`.
  refine Matrix.ext (Sum.forall.2 ⟨fun a b ↦ ?_, h_lower⟩)
  induction a using WellFoundedGT.induction with | ind a ih => ?_
  refine h_rigid (f := fun γ ↦ γ.val (Sum.inl a) (𝔰.besselFrame b))
    (fun hγ ↦ termsOver.isIntegral_inl_besselFrame hγ a b) b fun v ↦ ?_
  obtain ⟨w, hw, hw_norm⟩ : ∃ w ∈ besselU,
      ‖((w * z v : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ S.b ^ (6 * 𝔰.n + 2) * R :=
    RealPlace.exists_norm_le_of_besselLength_le (h_size v)
  have h_exp : S.b ^ (23 * 𝔰.ϱ) * S.b ^ (6 * 𝔰.n + 2) ≤ S.frameBoxRadius := by
    rw [frameBoxRadius, ← pow_add]
    gcongr
    nlinarith [S.ten_pow_five_le_varrho]
  set ε : ℝ := ‖Φ v (g.val (Sum.inl a) (𝔰.besselFrame b) -
    (1 : S.G E).val (Sum.inl a) (𝔰.besselFrame b))‖
  calc ε ≤ ε * (S.b ^ (23 * 𝔰.ϱ) *
        ‖S.basisScale v (𝔰.besselFrame b) / S.basisScale v (𝔰.besselFrame a.castSucc)‖) :=
        le_mul_of_one_le_right (norm_nonneg _) (one_le_pow_mul_norm_basisScale_div v _ b)
    _ ≤ S.b ^ (23 * 𝔰.ϱ) * (S.b ^ (6 * 𝔰.n + 2) * R * δ v b) := by
        grw [mul_left_comm, norm_Φ_sub_mul_norm_basisScale_div_le (Matrix.ext h_lower) ih hw (z v),
          hw_norm]
    _ = S.b ^ (23 * 𝔰.ϱ) * S.b ^ (6 * 𝔰.n + 2) * R * δ v b := by ring
    _ ≤ S.N * (S.frameBoxRadius * R) * δ v b := by
        grw [h_exp, ← S.N_prime.one_le, Nat.cast_one, one_mul]

variable [HasPrimitiveRoot5040 E]

omit [HasPrimitiveRoot5040 E] in
/-- **Packing of frames.** Let `E` be a CM field, `𝔰` a shape (`𝔰.ϱ` hyperbolic planes), and `S`
admissible data of the filling theorem over `E` (`IsAdmissible`), with parameter `b = S.b`. Let
`n = 𝔰.n`, `R ≥ 1` and `frameBoxRadius = b ^ (37 n)`. The frame is `f = (e₁, …, e_ϱ, z)`, and the
frame vectors of `x ∈ 𝔰.G₁` are the `x⁻¹ f_a` (`frameVector x a`). Let `A` be a set of rational `γ`,
each in `termsOver c s c'` for the given class `c` and some `s`, `c'`. Let `y` be a point of `𝔰.G₁`
at each infinite place. Suppose that for `γ ∈ A` the point `x = (S.ratToInf γ)⁻¹ y` has, at every
place, infimum of `‖s x‖ + 1` over the Bessel subgroup (`besselLength`) at most `b ^ (6 n + 2) R`.
Suppose also that it has frame vectors of norm at most `frameBoxRadius * R` (`frameBox`), and that
the frame vectors of any two of these points differ by an element of the real subspace `V`. Then the
images `γ f` (`frameImage`) of the frame take at most `(b ^ (6 n ^ 2) R ^ 2) ^ dim V` values on
`A`. -/
theorem encard_image_frameImage_le {c : S.Classes} {y : NumberField.InfinitePlace E → 𝔰.G₁}
    {R : ℝ} (hR : 1 ≤ R) {A : Set (S.G E)}
    (h_over : ∀ γ ∈ A, ∃ (s : S.ResidueGL) (c' : S.Classes), γ ∈ S.termsOver c s c')
    (h_size : ∀ γ ∈ A, ∀ v : NumberField.InfinitePlace E,
      besselLength (((S.ratToInf γ)⁻¹ * y) v) ≤ S.b ^ (6 * 𝔰.n + 2) * R)
    (h_box : ∀ γ ∈ A, ∀ v : NumberField.InfinitePlace E,
      ((S.ratToInf γ)⁻¹ * y) v ∈ frameBox (S.frameBoxRadius * R))
    {V : Submodule ℝ
      (NumberField.InfinitePlace E → Fin (𝔰.ϱ + 1) → EuclideanSpace ℂ 𝔰.BesselIndex)}
    (hV : ∀ γ ∈ A, ∀ γ' ∈ A,
      (fun v : NumberField.InfinitePlace E ↦ frameVector (((S.ratToInf γ)⁻¹ * y) v)) -
        (fun v : NumberField.InfinitePlace E ↦ frameVector (((S.ratToInf γ')⁻¹ * y) v)) ∈ V) :
    ((fun γ : S.G E ↦ frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)) '' A).encard ≤
      ENNReal.ofReal ((S.b ^ (6 * 𝔰.n ^ 2) * R ^ 2) ^ finrank ℝ V) := by
  -- With `ρ = frameBoxRadius * R`, terms with different frames give points of `V` at distance at
  -- least `(N ρ)⁻¹` (`frameImage_eq_frameImage_one_of_close`) in the ball of radius `2 ρ`;
  -- `encard_le_of_separated` compares volumes.
  rcases A.eq_empty_or_nonempty with rfl | ⟨γ₀, hγ₀⟩
  · simp
  have hb : 1000 ≤ S.b := S.thousand_le_b
  set ρ : ℝ := S.frameBoxRadius * R with hρ_eq
  have hρ : 0 < ρ := by
    rw [hρ_eq, frameBoxRadius]
    positivity
  have hNρ : 0 < S.N * ρ := mul_pos (mod_cast S.N_prime.pos) hρ
  let frame (p : A) : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) E :=
    frameImage (p.val : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)
  obtain ⟨u, h_image, h_inj⟩ : ∃ u : Set A, frame '' u = range frame ∧ InjOn frame u :=
    exists_image_eq_injOn_of_subset_range le_rfl
  let F (γ : S.G E) (v : NumberField.InfinitePlace E) :
      Fin (𝔰.ϱ + 1) → EuclideanSpace ℂ 𝔰.BesselIndex :=
    frameVector (((S.ratToInf γ)⁻¹ * y) v)
  let f (p : A) : V := ⟨F γ₀ - F p, hV γ₀ hγ₀ p p.2⟩
  have h_sep : u.Pairwise fun p q ↦ (S.N * ρ)⁻¹ ≤ ‖f p - f q‖ := by
    refine fun p hp q hq h_ne ↦ not_lt.1 fun h_close ↦ h_ne (h_inj hp hq ?_)
    obtain ⟨s, d, hp_over⟩ : ∃ (s : S.ResidueGL) (d : S.Classes), p.val ∈ S.termsOver c s d :=
      h_over p p.2
    obtain ⟨s', d', hq_over⟩ : ∃ (s : S.ResidueGL) (d : S.Classes), q.val ∈ S.termsOver c s d :=
      h_over q q.2
    -- The inverse of the term `p⁻¹ q` sends `p⁻¹ y` to `q⁻¹ y`, whose frame vectors are close.
    refine frameImage_inv_mul_eq_iff.1 (frameImage_eq_frameImage_one_of_close
      (.mul (.inv hp_over) hq_over) hR
      (h_box p p.2) (h_size p p.2) fun v a ↦ lt_of_le_of_lt ?_ h_close)
    have h_point : (S.ratToInf (p.val⁻¹ * q.val) v)⁻¹ * ((S.ratToInf p.val)⁻¹ * y) v =
        ((S.ratToInf q.val)⁻¹ * y) v := by
      simp [mul_assoc]
    have h_diff : ‖f p - f q‖ = ‖F q - F p‖ := by
      rw [← Submodule.norm_coe, Submodule.coe_sub, ← sub_sub_sub_cancel_left (F p) (F q) (F γ₀)]
    rw [h_point, h_diff]
    exact (norm_le_pi_norm ((F q - F p) v) a).trans (norm_le_pi_norm (F q - F p) v)
  have h_norm (γ : S.G E) (hγ : γ ∈ A) : ‖F γ‖ ≤ ρ :=
    (pi_norm_le_iff_of_nonneg hρ.le).2 fun v ↦ (pi_norm_le_iff_of_nonneg hρ.le).2 (h_box γ hγ v)
  have h_ball (p : A) (_ : p ∈ u) : ‖f p‖ ≤ ρ + ρ :=
    norm_sub_le_of_le (h_norm γ₀ hγ₀) (h_norm p p.2)
  have h_one : 1 ≤ S.b ^ (60 * 𝔰.n) * ρ ^ 2 := by
    have hb_one : 1 ≤ S.b := S.one_le_b
    rw [hρ_eq, frameBoxRadius]
    bound
  have h_ratio : 1 + 2 * (ρ + ρ) / (S.N * ρ)⁻¹ ≤ S.b ^ (6 * 𝔰.n ^ 2) * R ^ 2 :=
    calc 1 + 2 * (ρ + ρ) / (S.N * ρ)⁻¹ = 1 + 4 * (S.N * ρ ^ 2) := by
          rw [div_inv_eq_mul]
          ring
      _ ≤ 5 * (S.b ^ (60 * 𝔰.n) * ρ ^ 2) := by
          grw [IsAdmissible.N_le]
          linarith
      _ ≤ S.b * (S.b ^ (60 * 𝔰.n) * ρ ^ 2) := by
          gcongr
          linarith
      _ = S.b ^ (74 * 𝔰.n + 60 * 𝔰.n + 1) * R ^ 2 := by
          rw [hρ_eq, frameBoxRadius]
          ring
      _ ≤ S.b ^ (6 * 𝔰.n ^ 2) * R ^ 2 := by
          gcongr
          · exact S.one_le_b
          · have h_large : 23 ≤ 𝔰.n := by linarith [S.ten_pow_five_le_varrho]
            nlinarith
  rw [image_eq_range, ← h_image, h_inj.encard_image]
  grw [encard_le_of_separated (inv_pos.2 hNρ) (add_pos hρ hρ).le h_sep h_ball, h_ratio]

/-- **Packing of weights.** Let `E` be a CM field with a primitive 5040-th root of unity and `S`
admissible filling data over `E` (`IsAdmissible`). Let `k p` be classes and `γ p` rational elements
with `p ↦ (k p, γ p)` injective, `w p` weights, `y` a point at the infinite places, `R ≥ 1`,
`b = S.b` and `n = 𝔰.n`. Suppose that for `p` in the support of `w` the element `γ p` is a term
over `(c, s, k p)` (`termsOver`), the point `x_p = (γ p)⁻¹ y` has at every place infimum of
`‖s x_p‖ + 1` over the Bessel subgroup (`besselLength`) at most `b ^ (6 n + 2) R`, and `w p` is at
most `x` times `S.classCutoff (k p)` at `x_p`, a cutoff for the rational unipotent elements fixing
the frame `f = (e₁, …, e_ϱ, z)` times the indicator of the reduced points. If the frame vectors
`x_p⁻¹ f_a` of any two of these points differ by an element of the real subspace `V`, then the
weights add up to at most `(b ^ (6 n ^ 2) R ^ 2) ^ dim V * x`. -/
lemma tsum_le_of_le_classCutoff_mul {c : S.Classes} {s : S.ResidueGL} {α : Type*}
    {y : NumberField.InfinitePlace E → 𝔰.G₁} {x : ℝ≥0∞} {R : ℝ}
    {k : α → S.Classes} {γ : α → S.G E} {w : α → ℝ≥0∞} (hR : 1 ≤ R)
    (h_inj : ∀ {p q : α}, k p = k q → γ p = γ q → p = q)
    (h_over : ∀ p ∈ w.support, γ p ∈ S.termsOver c s (k p))
    (h_size : ∀ p ∈ w.support, ∀ v : NumberField.InfinitePlace E,
      besselLength (((S.ratToInf (γ p))⁻¹ * y) v) ≤ S.b ^ (6 * 𝔰.n + 2) * R)
    (h_le : ∀ p ∈ w.support, w p ≤ S.classCutoff (k p) ((S.ratToInf (γ p))⁻¹ * y) * x)
    {V : Submodule ℝ
      (NumberField.InfinitePlace E → Fin (𝔰.ϱ + 1) → EuclideanSpace ℂ 𝔰.BesselIndex)}
    (hV : ∀ p ∈ w.support, ∀ q ∈ w.support,
      (fun v : NumberField.InfinitePlace E ↦ frameVector (((S.ratToInf (γ p))⁻¹ * y) v)) -
        (fun v : NumberField.InfinitePlace E ↦ frameVector (((S.ratToInf (γ q))⁻¹ * y) v)) ∈ V) :
    ∑' p : α, w p ≤ ENNReal.ofReal ((S.b ^ (6 * 𝔰.n ^ 2) * R ^ 2) ^ finrank ℝ V) * x := by
  -- Colour the terms by their frames. Terms with the same frame differ by an element of
  -- `S.classUnipotent₀`, so their weights are at most `x` times terms of a partition of unity and
  -- add up to at most `x`. The number of frames is bounded by `encard_image_frameImage_le`.
  have h_box (p : α) (hp : p ∈ w.support) (v : NumberField.InfinitePlace E) :
      ((S.ratToInf (γ p))⁻¹ * y) v ∈ frameBox (S.frameBoxRadius * R) := by
    have h_pos : 0 < S.classCutoff (k p) ((S.ratToInf (γ p))⁻¹ * y) * x :=
      (pos_iff_ne_zero.2 hp).trans_le (h_le p hp)
    exact mem_frameBox_of_classCutoff_ne_zero (left_ne_zero_of_mul h_pos.ne') (by positivity)
      (h_size p hp v)
  rw [← tsum_subtype_support]
  generalize w.support = A at *
  let frame (p : A) : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) E :=
    frameImage (γ p : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)
  refine tsum_le_of_encard_range_le
    (R := fun p q : α ↦ k p = k q ∧ (γ p)⁻¹ * γ q ∈ S.classUnipotent₀ (k p)) frame ?_
    (fun p q ↦ termsOver.eq_and_mem_classUnipotent₀ (h_over p p.2) (h_over q q.2))
    fun B hBA p hp h_rel ↦ ?_
  · -- The frames are those of the terms `γ p` with `p` in the support.
    have h_range : range frame =
        (fun g : S.G E ↦ frameImage (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E)) '' (γ '' A) := by
      rw [image_image, image_eq_range]
    rw [h_range]
    exact encard_image_frameImage_le hR
      (forall_mem_image.2 fun p hp ↦ ⟨s, k p, h_over p hp⟩) (forall_mem_image.2 h_size)
      (forall_mem_image.2 h_box)
      (forall_mem_image.2 fun p hp ↦ forall_mem_image.2 fun q hq ↦ hV p hp q hq)
  · -- The terms `B` with the same frame: `q ↦ (γ q)⁻¹ * γ p` injects `B` into the unipotent group,
    -- over which the cutoffs sum to one.
    have h_class (q : B) : k q = k p := (h_rel q q.2 p hp).1
    have h_mem (q : B) : (γ q)⁻¹ * γ p ∈ S.classUnipotent (k p) := by
      obtain ⟨h_unipotent, -⟩ : (γ q)⁻¹ * γ p ∈ S.classUnipotent₀ (k q) := (h_rel q q.2 p hp).2
      rwa [← h_class q]
    let ι (q : B) : S.classUnipotent (k p) := ⟨(γ q)⁻¹ * γ p, h_mem q⟩
    have hι : ι.Injective := fun q q' h_eq ↦
      Subtype.ext (h_inj ((h_class q).trans (h_class q').symm) (by simpa [ι] using h_eq))
    let β (u : S.classUnipotent (k p)) : ℝ≥0∞ :=
      S.classCutoff (k p) (S.ratToInf u * (S.ratToInf (γ p)⁻¹ * y))
    calc
      ∑' q : B, w q ≤ ∑' q : B, β (ι q) * x := by
        gcongr with q
        simpa [β, ι, h_class q] using h_le q (hBA q.2)
      _ ≤ (∑' u : S.classUnipotent (k p), β u) * x := by
        grw [← ENNReal.tsum_comp_le_tsum_of_injective hι, ENNReal.tsum_mul_right]
      _ = x := by rw [tsum_classCutoff_eq_one, one_mul]

/-- Let `E` be a CM field with a primitive 5040-th root of unity, `S` admissible filling data over
`E` for the shape `𝔰` (`IsAdmissible`), and `c` a class in `S.Classes`. Suppose a point `y`
satisfies `InCut` at every infinite place `v`: `besselLength (y v)`, the infimum of ‖s (y v)‖ + 1
over `s` in the Bessel subgroup, is at most `S.b ^ (6 n + 2)`, where `n = 𝔰.n`. Then some `u` in
`S.classUnipotent c`, the congruence group of rational unipotent elements attached to `c`, has
`S.ratToInf u * y` in `boxedPoints`. The boxed points are those satisfying the same bound that are
reduced: the entries above the diagonal of their triangular matrices of Gram–Schmidt coefficients,
read in the rational frame, lie in a chosen residue domain. -/
lemma exists_classUnipotent_mul_mem_boxedPoints (c : S.Classes)
    {y : NumberField.InfinitePlace E → 𝔰.G₁}
    (h_cut : ∀ v : NumberField.InfinitePlace E, InCut (y v) S.b) :
    ∃ u ∈ S.classUnipotent c, S.ratToInf u * y ∈ S.boxedPoints := by
  -- The cutoffs of the translates add up to `1`, so one of them is not zero.
  obtain ⟨u, hu⟩ : ∃ u : S.classUnipotent c, S.classCutoff c (S.ratToInf u * y) ≠ 0 :=
    ENNReal.summable.tsum_ne_zero_iff.1 ((tsum_classCutoff_eq_one c y).trans_ne one_ne_zero)
  -- Left translation by the unipotent `u` keeps `besselLength`.
  obtain ⟨hu_unipotent, -⟩ : u.val ∈ S.classUnipotent c := u.2
  have h_cut_mul (v : NumberField.InfinitePlace E) : InCut ((S.ratToInf u * y) v) S.b :=
    (besselLength_besselS_mul (mem_partialUnitriangularGroup_of_mem_besselU
      (hu_unipotent.ratToInf_mem_agreeWithOneOn v))).trans_le (h_cut v)
  exact ⟨u, u.2, mem_boxedPoints_of_classCutoff_ne_zero hu h_cut_mul⟩

/-- The cutoff of a class is measurable. -/
@[fun_prop]
lemma measurable_classCutoff (c : S.Classes) : Measurable (S.classCutoff c) := by
  obtain ⟨β, hβ, hβ_meas, -⟩ := S.exists_classCutoff_eq_mul c
  rw [hβ]
  exact hβ_meas.mul (isBoxPartitionOfUnity_reducedIndicator c).measurable

end New.Filling

end BoxPartition

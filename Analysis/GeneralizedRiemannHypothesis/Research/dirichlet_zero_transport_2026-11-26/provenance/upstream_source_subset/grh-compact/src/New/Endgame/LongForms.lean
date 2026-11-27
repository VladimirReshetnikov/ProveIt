import New.Exchange.CrudeRows
import New.Endgame.ShortAndEnough
import New.Selmer.FitTwistsExist
import New.Rows.LiftVolumeHeight

/-! Part of: The inequality (⋆): upper bound for weighted non-split primes (see New.Main).

This file: Theorem C (`Data.integral_forms_long`: a lower bound for the covolume of the lifts of an
almost spanning family of small index), and the family given by Theorems A and B. -/

open Finset LinearMap Real Submodule LevelPlaces.LevelForm

variable {P} {D : Data P} {n} {y : Fin n → _} {δ V} (i : LinearIndependent ℂ y) (hn :
  (1 - 4 / D.b ^ 2) * D.rowDim ≤ n) (I : D.IndexLe y δ) (hV : ∀ σ, covolumeSq (D.Θ 1 ∘ y) σ ≤ exp V)

/-- If the twists θ_ι satisfy `Data.IsFitFamily`, the family 𝔷(1)²/𝔷(θ_ι)² of squared ratios of
volumes (`Data.𝔷`) has height (`HeightLe`) at most 2D(2fa log⁴ b − h_main), where D is
the dimension of the rows and h_main = `Data.mainHeight`. -/
lemma Data.heightLe_volume_ratio_sq {θ} (o : D.IsFitFamily θ) : HeightLe (2 * D.rowDim *
  (2 * (D.logB * D.budget) - D.mainHeight)) fun ι ↦ D.𝔷 (1 : D.MFoldTwist) ^ 2 / D.𝔷 (θ ι) ^ 2 := by
  -- `vol : 𝔷 ϑ = ‖c ϑ‖ ^ D ∏ⱼ λⱼ ϑ`
  choose c const _ vol using D.volume_iota_eq_prod_liftVolume
  -- each of the `m` lifts has height `D k (log b B₀ - 𝖴)`; `m k B₀ = budget` and `m k 𝖴 = h_main`
  have lifts : HeightLe (D.rowDim * (D.logB * D.budget - D.mainHeight))
      (∏ j ∈ Icc 1 D.m, fun ι ↦ D.liftVolume 1 j / D.liftVolume (θ ι) j) := (HeightLe.prod
    fun j h ↦ by exact heightLe_liftVolume_ratio o ⟨j, mem_Icc.1 h⟩).mono
    (by simp [mainHeight]; field_simp [(HasLogBound.pos D).ne']; rfl) fun _ ↦ le_rfl
  -- the constants have height `2 m² t x ^ 999`
  have consts : HeightLe (2 * (D.logB * D.budget)) fun ι ↦ (‖c (θ ι) / c 1‖ ^ 2 :)⁻¹ :=
    (const θ o).mono (by simpa using D.le_of_hasLogBound) fun _ ↦ le_rfl
  exact ((lifts.pow 2).mul (consts.pow D.rowDim)).mono (by grind) fun ι ↦
    (congrArg (‖ι.2 ·‖) (by simp [vol, mul_pow, div_pow, ← pow_mul]; ring)).le

include i hn I hV

/-- Let y be n ≥ (1 − 4/b²)·dim(rows) independent rows of index ≤ δ whose untwisted lifts have
squared covolume ≤ e^V at every σ. For twists θ satisfying `Data.IsFitFamily`, the ratios
𝔷(θ_ι)/𝔷(1) have height (`HeightLe`) at most V + 2δ + b·dim(rows). -/
lemma Data.heightLe_volume_rows {θ} (o : D.IsFitFamily θ) :
    HeightLe (V + 2 * δ + D.rowDim * D.b) fun ι ↦ D.𝔷 (θ ι) / D.𝔷 (1 : D.MFoldTwist) := by
  obtain ⟨⟨e, he, I⟩, γ, hγ, s⟩ := I, D.crude_rows
  -- the basis: `z a` is the good part of the auxiliary form `ψ a`
  choose k z ψ J c using exists_extend_basis_of_span_eq_top i ((s ▸ span_image
    (D.goodProjTranslate 1)).trans (by simp [range_smul, NeZero.ne, Module.End.one_eq_id]; rfl))
  choose ψ hψ ez using ψ
  -- size and completion; the matrices of the index, extended by the scalar of the auxiliary forms
  refine (one_determinant D.Θ (by simp) J (by simpa) (fun _ ↦ norm_map_det_gram_le fun σ ↦
    Sum.comp_elim .. ▸ covolumeSq_elim_le (ez · ▸ normSqAt_goodProjTranslate_le ((hψ _).2 σ))
    (hV σ)) (by simp) (hγ θ o) he (fun _ j ↦ (integralForms ⟨j⟩).carrier) k (fun ι j _ a _ b ↦ ?_)
    fun ι j ↦ (I _ ⟨j⟩ _ (o.1 ι)).imp' ((algebraMap ..).mapMatrix · |>.fromBlocks 0 0 ((γ (θ ι) /
    γ 1 : ℂ) • 1)) fun _ ↦ .imp (by grw [·]; simp [← RingHom.map_det, -RingHom.mapMatrix_apply])
    (by simpa [Matrix.one_apply] using! And.intro · fun a ↦ ez a ▸
    goodProjTranslate_mem_integralForms ⟨j⟩ ((hψ a).1 _ _ ⟨j⟩ (o.1 ι)) 1)).mono (by
    rw [add_right_comm V, add_assoc]; simp [c, field] at *
    grw [(D.le_of_hasLogBound : _ + _ ≤ 4⁻¹ * D.b ^ 3)]; nlinarith [D.logB.exp_pos]) fun _ ↦ le_rfl
  simpa using (norm_inner_le_one _ _ ⟨j⟩
    (fun g ↦ by erw [D.classAut_eq_bot_of_le_chosenLevel (Subgroup.map_mono fun _ h ↦
    funext fun _ ↦ (h (.inl _) ⟨⟩).2) (by bound [D.card_Y_le .refl])]) a b :)

/-- Integral forms are long: if n ≥ (1 − 4/b²)D independent rows, D = dim(rows), have index at
most δ and their untwisted lifts have squared covolume ≤ e^V at all σ ∈ Aut ℂ, then D(h_main
− 3fa log⁴ b) ≤ V + 2δ. -/
lemma Data.integral_forms_long : D.rowDim * (D.mainHeight - 3 * (D.logB * D.budget)) ≤
  V + 2 * δ := by
  -- one twist `θ ι` for each `ι`, with the congruence bounds; the volumes do not vanish
  obtain ⟨⟨θ, o⟩, _, -, Z⟩ := exists_isFitFamily D, D.volume_iota_eq_prod_liftVolume
  -- `(𝔷 θ / 𝔷 1)² (𝔷 1² / 𝔷 θ²) = 1`, heights add, and the height of `1` is `≥ 0`
  have formula : 0 ≤ 2 * (V + _ + _) + _ := ((((heightLe_volume_rows i hn I hV o).pow 2).mul
    (heightLe_volume_ratio_sq o)).mono le_rfl (by simp [field]; simp [(Z _).1])).nonneg
  linarith [(by gcongr; exact D.le_of_hasLogBound : D.rowDim * D.b ≤
    D.rowDim * (D.logB * D.budget))]

omit I hV i hn

/-- There are n ≥ (1 − 4/b²)D independent rows, D = dim(rows), of index at most 5D log(1 + b²)
fa log³ b, whose untwisted lifts have squared covolume at most exp(n(h_main − m·rem + fa
log⁴ b)) at all σ ∈ Aut ℂ. -/
lemma Data.exists_family_covolumeSq_le (D : Data P) : ∃ n, ∃ y : Fin n → _, LinearIndependent ℂ y ∧
    (1 - 4 / D.b ^ 2) * D.rowDim ≤ n ∧
  (∃ δ ≤ 5 * D.rowDim * log (1 + D.b ^ 2) * D.budget, D.IndexLe y δ) ∧ ∀ σ,
  covolumeSq (D.Θ 1 ∘ y) σ ≤ exp (n * (D.mainHeight - D.m * D.remainder + D.logB * D.budget)) := by
  obtain ⟨⟨q, q0, B, hB, ⟨S, hS, sp, size⟩, index⟩, -, -, t, ht, big⟩ :=
    D.short_forms, D.enough_forms
  -- the family: a basis among the translates
  let Y := Set.image2 (B ·) t S
  obtain ⟨y, hy, -, i⟩ := exists_fun_fin_finrank_span_eq ℂ Y
  rw [(by simp [Y, ← Set.iUnion_image_left, span_iUnion₂, sp]
          simp [hB, range_smul, q0.ne'] : iSup _ = span ℂ Y)] at big
  -- index and length
  exact ⟨_, y, i, big, ⟨_, mul_le_mul_of_nonneg_right ht (HasLogBound.pos D).le, index t _ y
    (Set.image2_subset_left hS <| hy ·)⟩, fun σ ↦ covolumeSq_le
    (have ⟨s, _, φ, h, e⟩ := hy ·; by simpa [e] using size φ h s σ)⟩

import Lib.DiscreteSeries.Bessel.Basic
import Lib.DiscreteSeries.FlenstedJensen.RightDerivatives

/-!
# Haar measures on the Bessel unipotent groups 𝖴⁰ ⊆ 𝖴 and σ-finiteness on G₁

Let `𝔰` be a shape and let 𝖴⁰ ⊆ 𝖴 be the Bessel unipotent subgroups (`New.Shape.Form.besselU0`,
`New.Shape.Form.besselU`) of the unitary group `𝔰.G₁`, which is `(𝔰.middleGram 1).G` (so 𝖴⁰ is
`(𝔰.middleGram 1).besselU0`). The elements of 𝖴 are block upper unitriangular for the levels of the
basis indices, and 𝖴⁰ also fixes the frame e_0, …, e_{ϱ-1}, z. The measures `New.Shape.besselHaar₀`
on 𝖴⁰ and `New.Shape.besselHaar` on 𝖴 are images of Lebesgue measure under explicit
parametrisations.

## Main definitions and results

* `New.RealPlace.injective_freeEntries_besselU0`, `New.RealPlace.injective_freeEntries_besselU`: the
  free entries (`New.RealPlace.freeEntries`: the entries at the free positions in the rows e_a, plus
  the imaginary parts at (e_a, e*_a)) are injective on 𝖴⁰ and on 𝖴.
* `New.RealPlace.measurePreserving_freeEntries_besselHaar₀`,
  `New.RealPlace.measurePreserving_freeEntries_besselHaar`: the free entries carry these measures to
  Lebesgue measure.
* `New.RealPlace.isUnimodularHaar_besselHaar₀`: `New.Shape.besselHaar₀` is a two-sided Haar measure
  (`New.RealPlace.IsUnimodularHaar`). An instance gives the same for `New.Shape.besselHaar`.
* `New.RealPlace.eichlerVectors`, `New.RealPlace.eichlerScalars`: the matrices ω and μ that describe
  an element of 𝖴⁰ as an Eichler map with matrix entries (`New.RealPlace.eichlerMatrix`).
* `New.RealPlace.homogeneousBall`: the balls ‖ω‖ ≤ ρ, ‖μ‖ ≤ ρ² in 𝖴⁰. Radii add under multiplication
  (`New.RealPlace.mul_mem_homogeneousBall`), and the volume is proportional to a power of the radius
  (`New.RealPlace.besselHaar₀_homogeneousBall`).
* `New.RealPlace.exists_tube`: there is a compact set whose slices along 𝖴⁰ have controlled measure
  (`New.RealPlace.IsTube`).

Notions from other files:
* `New.Shape.G₁`: The unitary group of the complex hermitian form made of ϱ hyperbolic planes, the
  standard positive form on κ, and one vector z with h(z, z) = −1.
* `New.Shape.BesselIndex`: The index set of the basis e_a; x_i (i in κ), z; e*_a, where a runs over
  `Fin ϱ`. The level is a at e_a, ϱ on the middle block and 2ϱ − a at e*_a (a counted from 0).

## Relation to the literature

No Bessel model is constructed here. This file gives coordinates and Lebesgue–Haar measure on the
unipotent radical and on its subgroup fixing the frame, balls and tubes for the latter, and the
σ-finiteness of Haar measures on the ambient unitary group. Source for the setting: H. Xue, Bessel
models for real unitary groups: the tempered case, Duke Math. J. 172 (2023) 995-1031; R.
Beuzart-Plessis, Astérisque 418 (2020).
-/

/-!
## Unimodular Haar measures on 𝖴 and 𝖴⁰, dilations and tubes

Right translations act on the free entries by volume preserving maps
(`New.RealPlace.exists_measurePreserving_freeEntries`), which gives right invariance. Conjugations
by the Bessel subgroup keep Haar measure (`New.RealPlace.measurePreserving_conj_bessel`) because
dilations (`New.RealPlace.exists_dilation`) conjugate each element of 𝖴 into one fixed ball.
`New.RealPlace.IsUnimodularHaar.of_freeEntries` combines the two for a subgroup of 𝖴 cut out by
prescribing entries.
-/

section UnipotentMeasure

namespace New.RealPlace

open Matrix MeasureTheory Measure ENNReal BesselIndex Norms.L2Operator Subgroup Fintype Complex
  Function Finset Floors.FloorGroups Fin

variable {𝔰 : Shape}

/-- 𝖴⁰ is cut out by entries: an element u of G₁ lies in 𝖴⁰ if and only if its entries agree with
those of the identity matrix at every position (i, j) on or below the level diagonal
(level j ≤ level i) and at every position in a column of the frame e_0, …, e_{ϱ-1}, z. -/
lemma mem_besselU0_iff_apply {u : 𝔰.G₁} :
    u ∈ besselU0 ↔ ∀ i j : 𝔰.BesselIndex, level j ≤ level i ∨ j ∈ Set.range 𝔰.besselFrame →
      u.val.val i j = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) i j := by
  -- The two cases of the disjunction are the two conditions in the definition of 𝖴⁰.
  simp_rw [or_imp, forall_and]
  rfl

/-- The embedding `New.RealPlace.embedH` of U(κ) in G₁ is continuous. -/
@[fun_prop]
lemma continuous_embedH : Continuous (embedH (𝔰 := 𝔰)) := by
  simp only [continuous_U_iff_matrix, coe_embedH, actOnCols]
  fun_prop

/-- The measure ν on the subgroup S of G₁ is a σ-finite left Haar measure that is also right
invariant, invariant under inversion, and satisfies `New.HasCutoff` for the action of S on G₁: some
measurable weight on G₁ has integral one over each orbit. -/
class IsUnimodularHaar {S : Subgroup 𝔰.G₁} (ν : Measure S) : Prop extends ν.IsHaarMeasure,
  ν.IsMulRightInvariant, ν.IsInvInvariant, SigmaFinite ν, HasCutoff ν 𝔰.G₁

/-! ### The dilation and conjugation invariance -/

/-- Dilations. For T ≥ 1 there is a d in G₁ such that conjugation u ↦ d⁻¹ud multiplies the matrix
entry (i, j) by T^{level i − level j}, and ‖d⁻¹ud‖ ≤ 1 + r²‖u‖/T for u in the Bessel unipotent group
𝖴 (`besselU`). Here ϱ is the number of hyperbolic planes, r = `𝔰.r` the number of basis indices, and
the level is a at e_a, ϱ on the middle block and 2ϱ − a at e*_a, with a counted from 0. -/
theorem exists_dilation {T : ℝ} (hT : 1 ≤ T) :
    ∃ d : 𝔰.G₁,
      -- (a) conjugation by `d` rescales each entry by a power of `T`
      (∀ (u : 𝔰.G₁) (i j : 𝔰.BesselIndex),
        (d⁻¹ * u * d).val.val i j = T ^ (level i - level j : ℤ) * u.val.val i j) ∧
      -- (b) on `besselU`, conjugation by `d` brings the norm close to `1` when `T` is large
      ∀ u ∈ besselU, ‖(d⁻¹ * u * d).val.val‖ ≤ 1 + 𝔰.r ^ 2 * (‖u.val.val‖ / T) := by
  -- `d` is the diagonal matrix with entries `T ^ (𝔰.ϱ - level i)`.
  have hT_pos : 0 < T := by linarith
  have hT_ne : (T : ℂ) ≠ 0 := mod_cast hT_pos.ne'
  obtain ⟨d, hd⟩ : ∃ d : 𝔰.G₁,
      d.val.val = diagonal fun i : 𝔰.BesselIndex ↦ (T : ℂ) ^ (𝔰.ϱ - level i : ℤ) := by
    refine exists_U_coe_eq ?_
    -- The form pairs e_a with e*_a, and the exponents at these two indices add up to `0`.
    simp [← ext_iff, level, ← zpow_add₀ hT_ne]
    grind [zpow_zero]
  have h_conj (u : 𝔰.G₁) (i j : 𝔰.BesselIndex) :
      (d⁻¹ * u * d).val.val i j = T ^ (level i - level j : ℤ) * u.val.val i j := by
    simp [inv_diagonal, Ring.inverse, Pi.isUnit_iff, zpow_sub₀, field, hd, hT_ne]
  refine ⟨d, h_conj, fun u hu ↦ ?_⟩
  -- For `u` in `besselU` the entries of `d⁻¹ * u * d - 1` vanish unless `level i < level j`,
  -- and are then those of `u` divided by a positive power of `T`.
  have h_entry (i j : 𝔰.BesselIndex) : ‖((d⁻¹ * u * d).val.val - 1) i j‖ ≤ ‖u.val.val‖ / T := by
    rw [Matrix.sub_apply, h_conj]
    obtain hij | hij := le_or_gt (level j) (level i)
    · rw [mem_besselU.1 hu i j hij]
      by_cases h_eq : i = j <;> simp [h_eq, div_nonneg, hT_pos.le]
    · suffices T ^ (level i - level j : ℤ) * ‖u.val.val i j‖ ≤ ‖u.val.val‖ / T by
        simpa [ne_of_apply_ne level hij.ne, abs_of_pos hT_pos]
      grw [norm_apply_le_l2_opNorm, show (level i - level j : ℤ) ≤ -1 by lia]
      simp [field]
  calc ‖(d⁻¹ * u * d).val.val‖
      ≤ ‖(1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ + ‖(d⁻¹ * u * d).val.val - 1‖ :=
        norm_le_insert' _ 1
    _ ≤ 1 + 𝔰.r ^ 2 * (‖u.val.val‖ / T) := by grw [norm_one, l2_opNorm_le_of_apply h_entry, sq]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod Finset.univ in
/-- Let `S` be a subgroup of G₁ cut out by asking that the entries at the positions `P` be those of
`1`, and let the Bessel subgroup `New.Shape.Form.besselS` normalise `S`; each of its elements is an
element of 𝖴 times an element `toBesselH w`. Conjugation by an element `s` of the Bessel subgroup
preserves every Haar measure of `S`. -/
lemma measurePreserving_conj_bessel {S : Subgroup 𝔰.G₁} {P : 𝔰.BesselIndex → 𝔰.BesselIndex → Prop}
    (hS : ∀ {u : 𝔰.G₁}, u ∈ S ↔
      ∀ i j : 𝔰.BesselIndex, P i j → u.val.val i j = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) i j)
    {μ : Measure S} {s : (𝔰.middleGram (1 : ℂ)).G} [IsHaarMeasure μ]
    (h_norm : besselS ≤ normalizer S) (hs : s ∈ besselS) :
    MeasurePreserving (fun u : S ↦ ⟨s * u.val * s⁻¹, (h_norm hs u).mp u.2⟩) μ μ := by
  -- Let `χ t` be the factor by which conjugation by `t` scales `μ`. The supremum `b` of
  -- `χ t * μ (ball 2)` over `besselS` is positive and finite, and `χ s * b = b`; so `χ s = 1`.
  have h_closed : IsClosed (S : Set 𝔰.G₁) := isClosed_of_entries_eq_one hS
  let conj (t : normalizer (S : Set 𝔰.G₁)) : S ≃ₜ* S := by
    use S.normalizerMonoidHom t <;> exact .subtype_mk (by fun_prop) _
  let χ : normalizer (S : Set 𝔰.G₁) →* NNRealˣ :=
    .mk' (fun t ↦ Units.mk0 _ (mulEquivHaarChar_pos (conj t)).ne') fun t t' ↦ by
      -- `conj (t * t')` is by definition the composite of `conj t'` and `conj t`.
      rw [mul_comm (Units.mk0 ..)]
      simp [Units.ext_iff, ← mulEquivHaarChar_trans, conj]
      rfl
  let ball (r : ℝ) : Set S := {y | ‖y.val.val.val‖ ≤ r}
  let C : ℝ := 1 + 𝔰.r ^ 2
  have h_bound (t : besselS) : χ (inclusion h_norm t) * μ (ball 2) ≤ μ (ball (C * 2 * C)) := by
    obtain ⟨t, ht⟩ := t
    obtain ⟨u, hu, w, rfl⟩ := exists_besselU_mul_toBesselH ht isUnit_one
    -- The dilation `d` with `T = ‖u‖` rescales entries, so it normalises `S`.
    obtain ⟨d, d_entry, d_norm⟩ := exists_dilation (U.one_le_norm u)
    have hd : d ∈ normalizer (S : Set 𝔰.G₁) := by
      refine mem_normalizer_iff''.2 fun v ↦ ?_
      simp_rw [hS, d_entry, one_apply]
      congr! 3
      -- The factor is `1` on the diagonal and nonzero elsewhere.
      split <;> simp [*, zpow_ne_zero]
    -- As `χ` has commuting values, `χ (u * h) = χ (h * (d⁻¹ * u * d))`, and this last element
    -- `z` has norm at most `C`, so conjugation by it maps `ball 2` into `ball (C * 2 * C)`.
    let u' : normalizer (S : Set 𝔰.G₁) :=
      ⟨u, h_norm (mem_partialUnitriangularGroup_of_mem_besselU hu)⟩
    let h : normalizer (S : Set 𝔰.G₁) :=
      ⟨_, h_norm (mem_partialUnitriangularGroup_of_mem_floorGroup (toBesselH_mem w))⟩
    let z : normalizer (S : Set 𝔰.G₁) := h * (⟨d, hd⟩⁻¹ * u' * ⟨d, hd⟩)
    have h_scale : χ (u' * h) = χ z := by simp [z, mul_comm (χ u'), mul_assoc]
    have hz : ‖z.val.val.val‖ ≤ C := (norm_embedH_mul _).trans_le <|
      (d_norm u hu).trans (by grw [div_self_le_one, mul_one])
    have h_maps : ball 2 ⊆ conj z ⁻¹' ball (C * 2 * C) := fun y hy ↦
      norm_mul_le_of_le (norm_mul_le_of_le hz hy) ((U.norm_inv _).trans_le hz)
    calc χ (u' * h) * μ (ball 2)
        ≤ χ z * μ (conj z ⁻¹' ball (C * 2 * C)) := by grw [h_scale, h_maps]
      _ = μ (ball (C * 2 * C)) := mulEquivHaarChar_smul_preimage ..
  let b : ℝ≥0∞ := ⨆ t : besselS, χ (inclusion h_norm t) * μ (ball 2)
  have hb_pos : b ≠ 0 := by simpa [b] using measure_sublevel_ne_zero μ (by simp)
  have hb_fin : b ≠ ∞ :=
    ne_top_of_le_ne_top (isCompact_U_norm_le _).preimage_val.measure_ne_top (iSup_le h_bound)
  -- Left multiplication by `s` permutes `besselS`.
  have h_fix : χ (inclusion h_norm ⟨s, hs⟩) * b = b :=
    .trans (by simp [b, mul_iSup, mul_assoc]) (Equiv.mulLeft (⟨s, hs⟩ : besselS)).iSup_comp
  have χ_eq : mulEquivHaarChar (conj ⟨s, h_norm hs⟩) = 1 :=
    mod_cast (ENNReal.mul_eq_right hb_pos hb_fin).1 h_fix
  have h_map : μ.map (conj ⟨s, h_norm hs⟩) = μ := by
    simpa [χ_eq] using mulEquivHaarChar_smul_map μ (conj ⟨s, h_norm hs⟩)
  exact ⟨by fun_prop, h_map⟩

/-! ### Lebesgue measure in the free entries is a two-sided Haar measure -/

open scoped Classical in
/-- Let `S` be cut out by prescribing the entries at the positions `P` to be those of `1`, and let
`p` be the free positions: the pairs `(a, i)` outside `P` in a row e_a with level i < 2ϱ − a. Right
multiplication by `g` in 𝖴 acts on the coordinates `New.RealPlace.freeEntries p` of the elements of
`S` (the entries at the positions in `p` and the imaginary parts of the entries at (e_a, e*_a))
through a volume preserving map `T`. -/
theorem exists_measurePreserving_freeEntries {S : Subgroup 𝔰.G₁}
    {P : 𝔰.BesselIndex → 𝔰.BesselIndex → Prop}
    (hS : ∀ {u : 𝔰.G₁}, u ∈ S ↔
      ∀ i j : 𝔰.BesselIndex, P i j → u.val.val i j = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) i j)
    {p : Fin 𝔰.ϱ × 𝔰.BesselIndex → Prop}
    (hp : ∀ (a : Fin 𝔰.ϱ) (i : 𝔰.BesselIndex), p (a, i) ↔ ¬P (.inl a) i ∧ level i < 2 * 𝔰.ϱ - a)
    {g : 𝔰.G₁} (hg : g ∈ besselU) :
    ∃ T : (Subtype p → ℂ) × (Fin 𝔰.ϱ → ℝ) → (Subtype p → ℂ) × (Fin 𝔰.ϱ → ℝ),
      MeasurePreserving T ∧ ∀ u ∈ S, freeEntries p (u * g) = T (freeEntries p u) := by
  -- `gCol a j ⬝ᵥ v` reads `v` as row `a` of a matrix and pairs it with column `j` of `g - 1`. The
  -- linear part `linPart` of `T` adds these to the coordinates. On the complex coordinates it is
  -- the matrix `linMatrix`, unitriangular for the levels; on the real ones it is a shear.
  let gCol (a : Fin 𝔰.ϱ) (j : 𝔰.BesselIndex) (x : Subtype p) : ℂ :=
    if x.val.1 = a then (g.val.val - 1) x.val.2 j else 0
  let linMatrix : Matrix (Subtype p) (Subtype p) ℂ := 1 + of fun x ↦ gCol x.val.1 x.val.2
  have h_det : linMatrix.det = 1 :=
    det_eq_one_of_unitriangular (lev := fun x ↦ -(level x.1.2 : ℤ)) fun x y hxy ↦ by
      simp [linMatrix, gCol, mem_besselU.1 hg y.val.2 x.val.2 (by lia)]
  let linPart (q : (Subtype p → ℂ) × (Fin 𝔰.ϱ → ℝ)) : (Subtype p → ℂ) × (Fin 𝔰.ϱ → ℝ) :=
    (linMatrix *ᵥ q.1, q.2 + fun a ↦ (gCol a (eStar a) ⬝ᵥ q.1).im)
  have h_linPart : MeasurePreserving linPart :=
    .skew_product (f := linMatrix.mulVec)
      ⟨by fun_prop, by simp [Fock.map_mulVec_addHaar_eq_smul, h_det]⟩
      (g := fun v w ↦ w + fun a ↦ (gCol a (eStar a) ⬝ᵥ v).im) (by fun_prop)
      (.of_forall fun v ↦ map_add_right_eq_self _ _)
  -- This instance is not found by search.
  have : (volume (α := (Subtype p → ℂ) × (Fin 𝔰.ϱ → ℝ))).IsAddHaarMeasure :=
    prod.instIsAddHaarMeasure ..
  refine ⟨fun q ↦ linPart (q - freeEntries p 1) + freeEntries p g,
    (h_linPart.comp (measurePreserving_sub_right _ _)).add_right _ _, fun u hu ↦ ?_⟩
  have h_row (a : Fin 𝔰.ϱ) (j : 𝔰.BesselIndex) (hj : level j ≤ 2 * 𝔰.ϱ - a) :
      gCol a j ⬝ᵥ (freeEntries p (u - 1)).1 = ((u.val.val - 1) * (g.val.val - 1)) (.inl a) j := by
    -- A nonzero summand `i` of the matrix product lies at a position `(a, i)` in `p`.
    have h_free (i : 𝔰.BesselIndex) (hui : (u.val.val - 1) (.inl a) i ≠ 0)
        (hgi : (g.val.val - 1) i j ≠ 0) : p (a, i) := by
      have h_level : level i < level j :=
        lt_of_not_ge fun h_ge ↦ hgi (sub_eq_zero.2 (mem_besselU.1 hg i j h_ge))
      exact (hp a i).2 ⟨fun hP ↦ hui (sub_eq_zero.2 (hS.1 hu _ i hP)), h_level.trans_le hj⟩
    have h_fst {x : Subtype p} (hx : gCol a j x * (freeEntries p (u - 1)).1 x ≠ 0) :
        x.val.1 = a := of_not_not fun hne ↦ hx (by simp [gCol, hne])
    refine sum_bij_ne_zero (fun x _ _ ↦ x.val.2) (by simp) (fun x _ hx y _ hy hxy ↦ ?_)
      (fun i _ hi ↦ ?_) fun x _ hx ↦ by simp [gCol, h_fst hx, mul_comm, Matrix.one_apply]
    · exact Subtype.ext (Prod.ext ((h_fst hx).trans (h_fst hy).symm) hxy)
    · obtain ⟨hui, hgi⟩ := mul_ne_zero_iff.1 hi
      exact ⟨⟨(a, i), h_free i hui hgi⟩, mem_univ _, by simpa [gCol, mul_comm] using hi, rfl⟩
  have key : linPart (freeEntries p (u - 1)) =
      freeEntries p (u - 1) + freeEntries p ((u - 1) * (g - 1)) := by
    ext x
    · -- a complex coordinate, at a position in `p`
      have hx_level : level x.val.2 ≤ 2 * 𝔰.ϱ - x.val.1 := ((hp ..).1 x.property).2.le
      simp [linPart, linMatrix, add_mulVec, ← h_row _ _ hx_level, -map_sub]
      -- An entry of `M *ᵥ v` is by definition the dot product of a row of `M` with `v`.
      rfl
    · -- a real coordinate, at a position `(a, e*_a)`
      simp [linPart, ← h_row x (eStar x) le_rfl, -map_sub]
  simp only [← map_sub, key, ← map_add]
  congr 1
  noncomm_ring

open scoped Classical in
/-- Let S ≤ 𝖴 be a subgroup of G₁ that is normalised by the Bessel subgroup and is cut out by
prescribing the entries at the positions P to be those of the identity matrix. Give each basis index
a level: i for e_i, ϱ on the middle block, and 2ϱ − i for e*_i. Let p consist of the positions (a,
i) of row e_a that are not in P and have level i < 2ϱ − a. If the coordinates
`New.RealPlace.freeEntries p` are injective on S and carry ν to Lebesgue measure, then ν is a
σ-finite left Haar measure on S that is also right invariant and inversion invariant, and some
measurable weight on G₁ has integral one over each S-orbit (`New.RealPlace.IsUnimodularHaar`). -/
theorem IsUnimodularHaar.of_freeEntries {S : Subgroup 𝔰.G₁}
    {P : 𝔰.BesselIndex → 𝔰.BesselIndex → Prop}
    (hS : ∀ {u : 𝔰.G₁}, u ∈ S ↔
      ∀ i j : 𝔰.BesselIndex, P i j → u.val.val i j = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) i j)
    {p : Fin 𝔰.ϱ × 𝔰.BesselIndex → Prop}
    (hp : ∀ (a : Fin 𝔰.ϱ) (i : 𝔰.BesselIndex), p (a, i) ↔ ¬P (.inl a) i ∧ level i < 2 * 𝔰.ϱ - a)
    (h_norm : besselS ≤ normalizer S.carrier) (h_le : S ≤ besselU) {ν : Measure S}
    (h_inj : Injective fun u : S ↦ freeEntries p u)
    (hν : MeasurePreserving (fun u : S ↦ freeEntries p u) ν) :
    IsUnimodularHaar ν := by
  have h_closed : IsClosed (S : Set 𝔰.G₁) := isClosed_of_entries_eq_one hS
  have := h_closed.polishSpace
  -- Conjugation by `g⁻¹` keeps the left Haar measure, so it is right invariant too.
  have h_haar_right : (haar : Measure S).IsMulRightInvariant := ⟨fun ⟨g, hg⟩ ↦ by
    have h_conj := measurePreserving_conj_bessel (μ := (haar : Measure S)) hS h_norm
      (mem_partialUnitriangularGroup_of_mem_besselU (h_le (inv_mem hg)))
    -- `x * g` is `g` times the conjugate `g⁻¹ * x * g`.
    convert (h_conj.mul_left _ (⟨g, hg⟩ : S)).map_eq using 2
    exact funext fun x ↦ Subtype.ext (by simp [mul_assoc])⟩
  -- Right translation acts on the coordinates by a volume preserving map.
  have h_right : ν.IsMulRightInvariant := ⟨fun g ↦ by
    obtain ⟨T, hT, hT_act⟩ := exists_measurePreserving_freeEntries hS hp (h_le g.property)
    refine (hν.measurable.measurableEmbedding h_inj).map_injective ?_
    simpa [map_map hν.measurable, measurable_mul_const, hν.map_eq, comp_def, hT_act] using
      (hT.comp hν).map_eq⟩
  have := hν.sigmaFinite
  obtain ⟨c, rfl⟩ : ∃ c : ℝ≥0∞, ν = c • haar := exists_eq_smul_haar haar h_right
  -- A Gaussian in the coordinates has integral `1`, so `c` is neither `0` nor `∞`.
  have : (volume (α := (Subtype p → ℂ) × (Fin 𝔰.ϱ → ℝ))).IsAddHaarMeasure :=
    prod.instIsAddHaarMeasure ..
  have hc : c ≠ 0 ∧ c ≠ ∞ := by
    have h_int := (hν.lintegral_comp (by fun_prop)).trans
      (lintegral_gaussian_eq_one (V := (Subtype p → ℂ) × (Fin 𝔰.ϱ → ℝ)))
    rw [lintegral_smul_measure, smul_eq_mul] at h_int
    exact isUnit_iff.1 (.of_mul_eq_one _ h_int)
  have := IsHaarMeasure.smul (G := S) haar hc.1 hc.2
  exact { hasCutoff_of_proper with }

/-- `New.RealPlace.unipotentOf`, the parametrisation of 𝖴⁰, is continuous. -/
@[fun_prop]
lemma continuous_unipotentOf : Continuous (unipotentOf (𝔰 := 𝔰)) := by
  simp only [continuous_U_iff_matrix, unipotentOf]
  fun_prop

/-- `New.RealPlace.liftUnitriangular`, the lift to G₁ (into 𝖴) of the unitriangular (ϱ + 1)×(ϱ + 1)
matrices: its block on the frame e_0, …, e_{ϱ-1}, z has the entries `x : UpperEntries 𝔰.n` above
the diagonal. It is continuous. -/
@[fun_prop]
theorem continuous_liftUnitriangular : Continuous (liftUnitriangular (𝔰 := 𝔰)) := by
  simp only [continuous_U_iff_matrix, liftUnitriangular]
  fun_prop

/-- The free positions of 𝖴 in row e_a are the columns of level strictly between a and 2ϱ − a. -/
lemma isFreeEntry_iff_level (a : Fin 𝔰.ϱ) (i : 𝔰.BesselIndex) :
    IsFreeEntry (a, i) ↔ ¬level i ≤ level (.inl a : 𝔰.BesselIndex) ∧ level i < 2 * 𝔰.ϱ - a := by
  -- By cases on the column: e_b, x_k, z or e*_b, the condition is an inequality of levels.
  obtain b | (k | _) | b := i <;> simp [IsFreeEntry, level] <;> lia

/-- The free positions of 𝖴⁰ in row e_a are the columns outside the frame e_0, …, e_{ϱ-1}, z of
level strictly between a and 2ϱ − a. -/
lemma isFreeEntry₀_iff_level (a : Fin 𝔰.ϱ) (i : 𝔰.BesselIndex) :
    IsFreeEntry₀ (a, i) ↔
      ¬(level i ≤ level (Sum.inl a : 𝔰.BesselIndex) ∨ i ∈ Set.range 𝔰.besselFrame) ∧
        level i < 2 * 𝔰.ϱ - a := by
  -- By cases on the column: e_b, x_k, z or e*_b, the condition is an inequality of levels.
  obtain b | (k | _) | b := i <;> simp [level, exists_fin_succ'] <;> lia

open scoped Classical in
/-- A sum over the free positions of 𝖴⁰. Let `w` be a function of the positions (row e_a, column i)
and `y` a square array such that `w` at (e_a, e*_b) is `y b a + y a b` for `a < b`. The sum of `w`
over the free positions and of `y` over the diagonal is the sum of `w` over the columns x_i (i in κ)
and of all entries of `y`. -/
lemma sum_isFreeEntry₀_add_sum_diag (w : Fin 𝔰.ϱ × 𝔰.BesselIndex → ℝ) (y : Fin 𝔰.ϱ → Fin 𝔰.ϱ → ℝ)
    (h_pair : ∀ a b : Fin 𝔰.ϱ, a < b → w (a, eStar b) = y b a + y a b) :
    ∑ x : Subtype IsFreeEntry₀, w x.val + ∑ a : Fin 𝔰.ϱ, y a a =
      ∑ a : Fin 𝔰.ϱ, ∑ i : 𝔰.κ, w (a, 𝔰.indexX₀ i) + ∑ a : Fin 𝔰.ϱ, ∑ b : Fin 𝔰.ϱ, y b a := by
  have h_split : ∑ x : Subtype IsFreeEntry₀, w x.val =
      ∑ a, ∑ i, w (a, 𝔰.indexX₀ i) + ∑ a, ∑ b ∈ Ioi a, (y b a + y a b) := by
    simp +contextual [← subtype_univ, sum_filter, sum_prod_type, ← filter_lt_eq_Ioi, h_pair,
      ite_add_zero, sum_add_distrib]
  -- The pairs `a < b` give the entries of `y` off the diagonal.
  rw [h_split, sum_sum_Ioi_add_eq_sum_sum_off_diag, add_assoc]
  simp [compl_eq_univ_sdiff]

open scoped Classical in
/-- For q = (a, b) in `𝔰.UnipotentParams`, with a a complex ϱ×κ matrix and b a real ϱ×ϱ matrix, take
the matrix X(aWᴴ + (sk b)Dᴴ) from the linear part of `New.RealPlace.unipotentOf`. Here X, W, D have
columns e_i, x_i, e*_i, and sk is `New.skewOfReal`, the skew-hermitian matrix with real coordinates
b. Its coordinates `New.RealPlace.freeEntries` at the free entries of 𝖴⁰ (`IsFreeEntry₀`: row e_a
with column x_i or e*_b for a < b, plus the imaginary parts at (e_a, e*_a)) are given by a volume
preserving ℝ-linear isomorphism `E` from `𝔰.UnipotentParams` onto
`(Subtype IsFreeEntry₀ → ℂ) × (Fin 𝔰.ϱ → ℝ)`. -/
lemma exists_measurePreserving_linearEquiv_freeEntries :
    ∃ E : 𝔰.UnipotentParams ≃ₗ[ℝ] (Subtype (IsFreeEntry₀ (𝔰 := 𝔰)) → ℂ) × (Fin 𝔰.ϱ → ℝ),
      MeasurePreserving E ∧
      ∀ q : 𝔰.UnipotentParams, E q = freeEntries IsFreeEntry₀
        (𝔰.isotropicCols * (q.1 * 𝔰.definiteColsᴴ + skewOfReal q.2 * 𝔰.dualColsᴴ)) := by
  -- The map keeps the sum of squares of the coordinates, and the dimensions agree.
  let rows : 𝔰.UnipotentParams →ₗ[ℝ] Matrix (Fin 𝔰.ϱ) 𝔰.BesselIndex ℂ :=
    (mulRightLinearMap _ ℝ 𝔰.definiteColsᴴ).coprod (mulRightLinearMap _ ℝ 𝔰.dualColsᴴ ∘ₗ skewOfReal)
  let E₀ : 𝔰.UnipotentParams →ₗ[ℝ] (Subtype (IsFreeEntry₀ (𝔰 := 𝔰)) → ℂ) × (Fin 𝔰.ϱ → ℝ) :=
    (freeEntries IsFreeEntry₀).toLinearMap ∘ₗ mulLeftLinearMap _ ℝ 𝔰.isotropicCols ∘ₗ rows
  have h_definite (q : 𝔰.UnipotentParams) (a : Fin 𝔰.ϱ) (i : 𝔰.κ) :
      rows q a (𝔰.indexX₀ i) = q.1 a i := by simp [rows, mul_apply, inclMatrix, Matrix.one_apply]
  have h_dual (q : 𝔰.UnipotentParams) (a b : Fin 𝔰.ϱ) :
      rows q a (eStar b) = skewOfReal q.2 a b := by
    simp [rows, mul_apply, inclMatrix, Matrix.one_apply]
  have hE₀ (q : 𝔰.UnipotentParams) : E₀ q = (fun x ↦ rows q x.1.1 x.1.2, fun a ↦ q.2 a a) := by
    simp [E₀, mul_apply, h_dual, skewOfReal, inclMatrix, Prod.ext_iff, funext_iff, Matrix.one_apply]
  have h_isometry (q : 𝔰.UnipotentParams) : ∑ x, ‖(E₀ q).1 x‖ ^ 2 + ∑ a, (E₀ q).2 a ^ 2 =
      ∑ a, ∑ i, ‖q.1 a i‖ ^ 2 + ∑ a, ∑ b, q.2 a b ^ 2 := by
    -- `skewOfReal` turns the real entries `(a, b)`, `(b, a)` into one complex entry with the same
    -- sum of squares.
    have h_pair (a b : Fin 𝔰.ϱ) (hab : a < b) :
        ‖rows q a (eStar b)‖ ^ 2 = q.2 a b ^ 2 + q.2 b a ^ 2 := by
      suffices ((q.2 a b - q.2 b a) ^ 2 + (q.2 a b + q.2 b a) ^ 2) / 2 =
          q.2 a b ^ 2 + q.2 b a ^ 2 by
        simpa [h_dual, skewOfReal, hab.ne, div_pow, RCLike.norm_sq_eq_def, ← sq]
      ring
    simpa only [hE₀, h_definite] using sum_isFreeEntry₀_add_sum_diag
      (fun x ↦ ‖rows q x.1 x.2‖ ^ 2) (fun a b ↦ q.2 b a ^ 2) h_pair
  have h_inj : Injective E₀ := (injective_iff_map_eq_zero E₀).2 fun q hq ↦ by
    have h_zero : ∑ a, ∑ i, ‖q.1 a i‖ ^ 2 + ∑ a, ∑ b, q.2 a b ^ 2 = 0 := by simp [← h_isometry, hq]
    rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)] at h_zero
    simpa [Finset.sum_eq_zero_iff_of_nonneg, Finset.sum_nonneg, sq_nonneg, ← Matrix.ext_iff,
      Prod.ext_iff] using h_zero
  -- Each complex coordinate counts twice in the dimension.
  have h_dim : Module.finrank ℝ 𝔰.UnipotentParams =
      Module.finrank ℝ ((Subtype (IsFreeEntry₀ (𝔰 := 𝔰)) → ℂ) × (Fin 𝔰.ϱ → ℝ)) := by
    rify
    simpa [Module.finrank_matrix, mul_assoc, Module.finrank_pi_fintype] using
      (sum_isFreeEntry₀_add_sum_diag (𝔰 := 𝔰) (fun _ ↦ 2) (fun _ _ ↦ 1)
        fun _ _ _ ↦ one_add_one_eq_two.symm).symm
  have : (volume (α := (Subtype (IsFreeEntry₀ (𝔰 := 𝔰)) → ℂ) × (Fin 𝔰.ϱ → ℝ))).IsAddHaarMeasure :=
    prod.instIsAddHaarMeasure ..
  have : (volume (α := 𝔰.UnipotentParams)).IsAddHaarMeasure := prod.instIsAddHaarMeasure ..
  exact ⟨E₀.linearEquivOfInjective h_inj h_dim, HasGaussianIntegral.measurePreserving _ h_isometry,
    fun q ↦ rfl⟩

open scoped Classical in
/-- The parametrisation `New.RealPlace.unipotentOf` sends q = (a, b), with a a complex ϱ×κ matrix
and b a real ϱ×ϱ matrix, to an element of the frame-fixing unipotent group 𝖴⁰. Read it in the free
entries of 𝖴⁰ (`New.RealPlace.freeEntries` at `New.RealPlace.IsFreeEntry₀`): the complex entries in
row e_a and column x_i (i ∈ κ) or e*_b with a < b, together with the imaginary parts at (e_a, e*_a).
In these coordinates it is a shear (a, b) ↦ (a, b + c(a)) with c continuous, followed by a volume
preserving linear isomorphism E. -/
lemma exists_freeEntries_unipotentOf_eq_shear :
    ∃ (E : 𝔰.UnipotentParams ≃ₗ[ℝ] (Subtype (IsFreeEntry₀ (𝔰 := 𝔰)) → ℂ) × (Fin 𝔰.ϱ → ℝ))
      (c : Matrix (Fin 𝔰.ϱ) 𝔰.κ ℂ → Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ),
      MeasurePreserving E ∧ Continuous c ∧
      ∀ q : 𝔰.UnipotentParams,
        freeEntries IsFreeEntry₀ (unipotentOf q : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) =
          E (q.1, q.2 + c q.1) := by
  -- `E (a, b)` consists of the free entries of the linear part `X(aWᴴ + (sk b)Dᴴ)`.
  obtain ⟨E, hE, hE_apply⟩ := exists_measurePreserving_linearEquiv_freeEntries (𝔰 := 𝔰)
  -- The quadratic term of `unipotentOf (a, b)` only shifts `b`, by the amount `(shift a).2`.
  let shift (a : Matrix (Fin 𝔰.ϱ) 𝔰.κ ℂ) : 𝔰.UnipotentParams :=
    E.symm.toLinearMap (freeEntries IsFreeEntry₀ (unipotentOf (a, 0)).val.val)
  refine ⟨E, fun a ↦ (shift a).2, hE,
    (E.symm.toLinearMap.continuous_of_finiteDimensional.comp (by fun_prop)).snd, fun q ↦ ?_⟩
  have h_shift : E (shift q.1) = freeEntries IsFreeEntry₀ (unipotentOf (q.1, 0)).val.val :=
    E.apply_symm_apply _
  -- The entries in the columns x_i show that `shift` keeps the first parameter.
  have h_fst : (shift q.1).1 = q.1 := by
    ext a i
    have h_entry : (E (shift q.1)).1 ⟨(a, 𝔰.indexX₀ i), by simp⟩ =
        (unipotentOf (q.1, 0)).val.val (.inl a) (𝔰.indexX₀ i) :=
      congrFun (congrArg Prod.fst h_shift) _
    simpa [hE_apply, unipotentOf, mul_apply, inclMatrix, Matrix.one_apply] using h_entry
  -- The free entries of `unipotentOf q` are affine in `q.2`, with linear part `b ↦ E (0, b)`.
  have h_affine : freeEntries IsFreeEntry₀ (unipotentOf q).val.val =
      freeEntries IsFreeEntry₀ (unipotentOf (q.1, 0)).val.val + E (0, q.2) := by
    have h_matrix : (unipotentOf q).val.val = (unipotentOf (q.1, 0)).val.val +
        𝔰.isotropicCols * (skewOfReal q.2 * 𝔰.dualColsᴴ) := by
      simp [unipotentOf, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, sub_eq_neg_add,
        add_assoc]
    rw [h_matrix, map_add, hE_apply, Matrix.zero_mul, zero_add]
  rw [h_affine, ← h_shift, ← map_add]
  exact congrArg E (Prod.ext (by simp [h_fst]) (add_comm _ _))

/-- The free-entry coordinates (`New.RealPlace.freeEntries` at `New.RealPlace.IsFreeEntry₀`: the
entries in row e_a and column x_i or e*_b with b > a, together with the imaginary parts at
(e_a, e*_a)) are injective on the unipotent group 𝖴⁰ (`New.Shape.Form.besselU0`) of G₁. -/
theorem injective_freeEntries_besselU0 :
    Injective fun u : (𝔰.middleGram (1 : ℂ)).besselU0 ↦
      freeEntries IsFreeEntry₀ (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) := by
  classical
  obtain ⟨E, c, -, -, h_coord⟩ := exists_freeEntries_unipotentOf_eq_shear (𝔰 := 𝔰)
  rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
  -- Every element of 𝖴⁰ is some `unipotentOf q`, and `E` and the shear are injective.
  obtain ⟨p, rfl⟩ := mem_besselU0_iff_unipotentOf.1 hu
  obtain ⟨q, rfl⟩ := mem_besselU0_iff_unipotentOf.1 hv
  have h_image : E (p.1, p.2 + c p.1) = E (q.1, q.2 + c q.1) := by simpa only [h_coord] using huv
  obtain ⟨h_fst, h_snd⟩ := Prod.mk.inj (E.injective h_image)
  obtain rfl : p = q := Prod.ext h_fst (by simpa [h_fst] using h_snd)
  rfl

open scoped Classical in
/-- The free-entry coordinates (`New.RealPlace.freeEntries` at `New.RealPlace.IsFreeEntry₀`: the
entries in row e_a and column x_i or e*_b with b > a, together with the imaginary parts at (e_a,
e*_a)) carry `New.Shape.besselHaar₀`, the image of Lebesgue measure under
`New.RealPlace.unipotentOf`, to Lebesgue measure. -/
theorem measurePreserving_freeEntries_besselHaar₀ :
    MeasurePreserving (fun u : (𝔰.middleGram (1 : ℂ)).besselU0 ↦
      freeEntries IsFreeEntry₀ (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)) 𝔰.besselHaar₀ := by
  obtain ⟨E, c, hE, hc_cont, h_coord⟩ := exists_freeEntries_unipotentOf_eq_shear (𝔰 := 𝔰)
  -- The shear translates each fibre of the first projection, so it preserves volume.
  have h_shear : MeasurePreserving fun q : 𝔰.UnipotentParams ↦ (q.1, q.2 + c q.1) :=
    .skew_product (.id _) (g := fun a b ↦ b + c a) (Continuous.measurable (by fun_prop))
      (.of_forall fun a ↦ map_add_right_eq_self _ _)
  have h_param : MeasurePreserving fun q : 𝔰.UnipotentParams ↦
      freeEntries IsFreeEntry₀ (unipotentOf q).val.val :=
    (hE.comp h_shear).congr (by fun_prop) (.of_forall fun q ↦ (h_coord q).symm)
  exact .map_of_comp h_param (by fun_prop) (by fun_prop)

open scoped Classical in
/-- The free entries are coordinates on 𝖴⁰ in which `New.Shape.besselHaar₀` is Lebesgue measure:
they are injective on 𝖴⁰ (`New.RealPlace.injective_freeEntries_besselU0`) and carry this measure
to Lebesgue measure (`New.RealPlace.measurePreserving_freeEntries_besselHaar₀`). -/
theorem injective_measurePreserving_freeEntries₀ :
    (Injective fun u : (𝔰.middleGram (1 : ℂ)).besselU0 ↦
      freeEntries IsFreeEntry₀ (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)) ∧
    MeasurePreserving (fun u : (𝔰.middleGram (1 : ℂ)).besselU0 ↦
      freeEntries IsFreeEntry₀ (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)) 𝔰.besselHaar₀ :=
  ⟨injective_freeEntries_besselU0, measurePreserving_freeEntries_besselHaar₀⟩

/-- `New.Shape.besselHaar₀` is a two-sided Haar measure on 𝖴⁰ with a cutoff for the action on G₁,
in the sense of `New.RealPlace.IsUnimodularHaar`. -/
instance isUnimodularHaar_besselHaar₀ : IsUnimodularHaar 𝔰.besselHaar₀ :=
  .of_freeEntries mem_besselU0_iff_apply isFreeEntry₀_iff_level besselS_le_normalizer_besselU0
    inf_le_left injective_freeEntries_besselU0 measurePreserving_freeEntries_besselHaar₀

/-- Call e_a, for a < ϱ, the first ϱ basis vectors of the Bessel basis e, x_i, z, e*
(`New.Shape.BesselIndex`). The coordinates `New.RealPlace.freeEntries` at
`New.RealPlace.IsFreeEntry` are injective on the Bessel unipotent group 𝖴 (`New.Shape.Form.besselU`)
of G₁. These are the complex entries in row e_a and column e_b or e*_b with b > a, or any column
x_i, z of the middle block, together with the imaginary parts at (e_a, e*_a). -/
theorem injective_freeEntries_besselU :
    Injective fun u : (𝔰.middleGram (1 : ℂ)).besselU ↦
      freeEntries IsFreeEntry (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) := by
  intro u v huv
  classical
  -- Multiply on the right by `v⁻¹`: the element `w = u * v⁻¹` has the coordinates of `1`.
  obtain ⟨T, -, hT_act⟩ : ∃ T, MeasurePreserving T volume volume ∧ ∀ x ∈ besselU,
      freeEntries IsFreeEntry (x * (v⁻¹).val).val.val = T (freeEntries IsFreeEntry x.val.val) :=
    exists_measurePreserving_freeEntries mem_besselU isFreeEntry_iff_level v⁻¹.property
  let w : 𝔰.G₁ := u * v⁻¹
  have hw_one : freeEntries IsFreeEntry w.val.val = freeEntries IsFreeEntry 1 := by
    simpa [w, ← hT_act] using congrArg T huv
  have hw_entry {a : Fin 𝔰.ϱ} {j : 𝔰.BesselIndex} (h_free : IsFreeEntry (a, j)) :
      w.val.val (.inl a) j = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (.inl a) j :=
    congrFun (congrArg Prod.fst hw_one) ⟨(a, j), h_free⟩
  -- The frame columns above the level diagonal are free entries, so `w` fixes the frame.
  have h_frame : ∀ i j : 𝔰.BesselIndex, level i < level j → j ∈ Set.range 𝔰.besselFrame →
      ∃ a : Fin 𝔰.ϱ, i = .inl a ∧ IsFreeEntry (a, j) := by
    -- An index outside the rows e_a has level at least ϱ, and the frame has level at most ϱ.
    simp [IsFreeEntry, level, exists_fin_succ']
    lia
  have hw_mem : w ∈ besselU0 := by
    refine mem_besselU0_iff_apply.2 fun i j hij ↦ ?_
    obtain h_le | h_lt := le_or_gt (level j) (level i)
    · exact mem_besselU.1 (mul_mem u.property (inv_mem v.property)) i j h_le
    · obtain ⟨a, rfl, h_free⟩ := h_frame i j h_lt (hij.resolve_left h_lt.not_ge)
      exact hw_entry h_free
  -- On 𝖴⁰ the coordinates are injective, and its free positions are among those of 𝖴.
  have h_sub : ∀ x : Fin 𝔰.ϱ × 𝔰.BesselIndex, IsFreeEntry₀ x → IsFreeEntry x := by simp
  have hw_one₀ : freeEntries IsFreeEntry₀ w.val.val = freeEntries IsFreeEntry₀ 1 :=
    Prod.ext (funext fun x ↦ hw_entry (h_sub _ x.property)) (congrArg Prod.snd hw_one :)
  -- So `w = 1`, that is `u = v`.
  have h_eq : (⟨w, hw_mem⟩ : (𝔰.middleGram (1 : ℂ)).besselU0) = 1 :=
    injective_freeEntries_besselU0 hw_one₀
  simpa [w, mul_inv_eq_one] using h_eq

open scoped Classical in
/-- The free entries of 𝖴 are those of 𝖴⁰ together with the entries above the diagonal
(`UpperEntries 𝔰.n`, with n = ϱ + 1) of the block on the frame e_0, …, e_{ϱ-1}, z. Regrouping
the coordinates accordingly preserves volume. -/
lemma exists_measurableEquiv_freeEntries_eq_prod :
    ∃ regroup : (Subtype (IsFreeEntry (𝔰 := 𝔰)) → ℂ) × (Fin 𝔰.ϱ → ℝ) ≃ᵐ
        UpperEntries 𝔰.n × (Subtype (IsFreeEntry₀ (𝔰 := 𝔰)) → ℂ) × (Fin 𝔰.ϱ → ℝ),
      MeasurePreserving regroup ∧
      ∀ M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ, regroup (freeEntries IsFreeEntry M) =
        (fun y : {y : Fin 𝔰.n × Fin 𝔰.n // y.1 < y.2} ↦
          M (𝔰.besselFrame y.val.1) (𝔰.besselFrame y.val.2), freeEntries IsFreeEntry₀ M) := by
  -- As `y.1 < y.2`, row `y.1` of the frame is some e_a and not the last vector z.
  let frame (y : {y : Fin 𝔰.n × Fin 𝔰.n // y.1 < y.2}) : Fin 𝔰.ϱ × 𝔰.BesselIndex :=
    (y.val.1.castPred (Fin.ne_last_of_lt y.property), 𝔰.besselFrame y.val.2)
  have h_free : ∀ x : {y : Fin 𝔰.n × Fin 𝔰.n // y.1 < y.2} ⊕ Subtype IsFreeEntry₀,
      IsFreeEntry (Sum.elim frame Subtype.val x) := by
    -- The columns of the frame to the right of row a have level between a + 1 and ϱ.
    simp [frame, IsFreeEntry, forall_fin_succ']
    lia
  have h_bij : Bijective (Subtype.coind (Sum.elim frame Subtype.val) h_free) := by
    refine ⟨?_, ?_⟩
    · -- The columns of the frame are not free positions of 𝖴⁰.
      simp [frame, Injective, Subtype.coind, forall_fin_succ']
      lia
    · -- A free position of 𝖴 has its column in the frame or is free for 𝖴⁰.
      simp [frame, Surjective, Subtype.coind, exists_fin_succ']
      lia
  let idx := Equiv.ofBijective _ h_bij
  let splitEntries : (Subtype (IsFreeEntry (𝔰 := 𝔰)) → ℂ) ≃ᵐ
      UpperEntries 𝔰.n × (Subtype (IsFreeEntry₀ (𝔰 := 𝔰)) → ℂ) :=
    (MeasurableEquiv.piCongrLeft (fun _ ↦ ℂ) idx).symm.trans (.sumPiEquivProdPi _)
  have h_split : MeasurePreserving splitEntries :=
    (volume_measurePreserving_sumPiEquivProdPi _).comp
      (volume_measurePreserving_piCongrLeft _ idx).symm
  refine ⟨(splitEntries.prodCongr (.refl _)).trans .prodAssoc,
    volume_preserving_prodAssoc.comp (h_split.prod (.id _)), fun M ↦ ?_⟩
  refine Prod.ext (funext fun y ↦ ?_) rfl
  change M (.inl (frame y).1) (frame y).2 = M (𝔰.besselFrame y.val.1) (𝔰.besselFrame y.val.2)
  rw [← besselFrame_castSucc, castSucc_castPred]

open scoped Classical in
/-- Let 𝖴 be the Bessel unipotent group of G₁ (`New.Shape.Form.besselU` for
`New.Shape.middleGram 1`). Its elements are the isometries of the hermitian form made of ϱ
hyperbolic planes (basis e_a, e*_a), the standard positive form on κ and a vector z with
h(z, z) = −1, that are block upper unitriangular in the basis e_0, …, e_{ϱ-1}, x_i, z,
e*_{ϱ-1}, …, e*_0. The free-entry coordinates (`New.RealPlace.freeEntries` at
`New.RealPlace.IsFreeEntry`) carry `New.Shape.besselHaar` on 𝖴 to Lebesgue measure. These
coordinates are the complex entries in row e_a and column e_b or e*_b with b > a, or any middle
column x_i or z, together with the imaginary parts of the entries at (e_a, e*_a). -/
theorem measurePreserving_freeEntries_besselHaar :
    MeasurePreserving (fun u : (𝔰.middleGram (1 : ℂ)).besselU ↦
      freeEntries IsFreeEntry (u : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)) 𝔰.besselHaar := by
  -- `besselHaar` is the image of a product measure under `(x, u) ↦ u * liftUnitriangular x`.
  -- `regroup` sends the free entries of a matrix to its frame entries above the diagonal and its
  -- free entries for 𝖴⁰, and preserves volume.
  obtain ⟨regroup, h_regroup, h_apply⟩ := exists_measurableEquiv_freeEntries_eq_prod (𝔰 := 𝔰)
  let coord (x : UpperEntries 𝔰.n) (u : (𝔰.middleGram 1).besselU0) :=
    freeEntries IsFreeEntry₀ (u.val * liftUnitriangular x).val.val
  have h_fibre (x : UpperEntries 𝔰.n) : 𝔰.besselHaar₀.map (coord x) = volume := by
    -- In the coordinates of 𝖴⁰, right translation by `liftUnitriangular x` is a volume preserving
    -- `T`.
    obtain ⟨T, hT, hT_act⟩ := exists_measurePreserving_freeEntries mem_besselU0_iff_apply
      isFreeEntry₀_iff_level (liftUnitriangular_mem_besselU x)
    exact ((hT.comp measurePreserving_freeEntries_besselHaar₀).congr (by fun_prop)
      (.of_forall fun u ↦ (hT_act u u.property).symm)).map_eq
  have h_skew : MeasurePreserving (fun q ↦ (q.1, coord q.1 q.2)) (volume.prod 𝔰.besselHaar₀) :=
    .skew_product (.id _) (by fun_prop) (.of_forall h_fibre)
  let entries (q : UpperEntries 𝔰.n × (𝔰.middleGram 1).besselU0) :=
    freeEntries IsFreeEntry (q.2.val * liftUnitriangular q.1).val.val
  have h_eq (q) : (q.1, coord q.1 q.2) = regroup (entries q) := by
    rw [h_apply]
    refine Prod.ext (funext fun y ↦ ?_) rfl
    -- The frame block of `u * liftUnitriangular x` is that of `liftUnitriangular x`, whose entries
    -- above the diagonal are `x`.
    change q.1 y = frameMatrix (q.2.val * liftUnitriangular q.1) y.val.1 y.val.2
    rw [frameMatrix_mul (liftUnitriangular_mem_besselU q.1)]
    simp [mem_besselU0_iff.1, unitriangularMatrix, y.2]
  have h_entries : MeasurePreserving entries (volume.prod 𝔰.besselHaar₀) :=
    h_regroup.comp_left_iff.1 (h_skew.congr (by fun_prop) (.of_forall h_eq))
  exact .map_of_comp h_entries (by fun_prop) (by fun_prop)

/-- `New.Shape.besselHaar` is a two-sided Haar measure on 𝖴 with a cutoff for the action on G₁, in
the sense of `New.RealPlace.IsUnimodularHaar`. -/
instance : IsUnimodularHaar 𝔰.besselHaar :=
  .of_freeEntries mem_besselU isFreeEntry_iff_level besselS_le_normalizer_besselU le_rfl
    injective_freeEntries_besselU measurePreserving_freeEntries_besselHaar

/-!
### Balls in 𝖴⁰ and tubes along 𝖴⁰

Write e, x, e* for the rows of basis vectors (e_a), (x_i), (e*_a); there are ϱ = n − 1 vectors e_a
and k = |κ| vectors x_i. An element of 𝖴⁰ acts like an Eichler map with matrix entries: it is given
by a k×ϱ matrix ω and a ϱ×ϱ matrix μ with μ + μᴴ = ωᴴ ω. The inverse of (ω, μ) is (−ω, μᴴ), so the
balls are symmetric.
-/

/-- The matrix of the Eichler map of a pair (ω, μ). It sends e* to e* − x ω − e μ and x to
x + e ωᴴ, and it fixes the frame e_0, …, e_{ϱ-1}, z. -/
def eichlerMatrix (ω : Matrix 𝔰.κ (Fin 𝔰.ϱ) ℂ) (μ : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℂ) :
    Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ :=
  1 + 𝔰.isotropicCols * ωᴴ * 𝔰.definiteColsᴴ - 𝔰.definiteCols * ω * 𝔰.dualColsᴴ -
    𝔰.isotropicCols * μ * 𝔰.dualColsᴴ

/-- The group law: the product of (ω, μ) and (ω', μ') is (ω + ω', μ + μ' + ωᴴ ω'). -/
lemma eichlerMatrix_mul (ω ω' : Matrix 𝔰.κ (Fin 𝔰.ϱ) ℂ) (μ μ' : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℂ) :
    eichlerMatrix ω μ * eichlerMatrix ω' μ' = eichlerMatrix (ω + ω') (μ + μ' + ωᴴ * ω') := by
  -- Multiply out. The basis columns are orthonormal, so the only product of two terms other than
  -- `1` that survives is that of the term with `ωᴴ` and the term with `ω'`.
  simp [eichlerMatrix, Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_sub,
    Matrix.add_mul, Matrix.sub_mul, inclMatrix_gram_mul_eq_self, inclMatrix_gram_mul_eq_zero]
  abel

/-- For q = (a, b), the element `New.RealPlace.unipotentOf q` is the Eichler map with ω = aᴴ and
μ = ½ a aᴴ − sk b, where sk is `New.skewOfReal`. So b gives the skew-hermitian part of μ. -/
lemma coe_unipotentOf_eq_eichlerMatrix (q : 𝔰.UnipotentParams) :
    (unipotentOf q).val.val = eichlerMatrix q.1ᴴ ((2⁻¹ : ℂ) • (q.1 * q.1ᴴ) - skewOfReal q.2) := by
  rw [eichlerMatrix, val_unipotentOf_coe, conjTranspose_conjTranspose, ← neg_sub (skewOfReal q.2),
    Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]

/-- Minus the block of u in the rows x_i and the columns e*_a. For u in 𝖴⁰ this is the matrix ω in
u e* = e* − x ω − e μ; its columns are vectors of the span X₀ of the x_i. -/
def eichlerVectors (u : 𝔰.G₁) : Matrix 𝔰.κ (Fin 𝔰.ϱ) ℂ :=
  -(𝔰.definiteColsᴴ * u.val.val * 𝔰.dualCols)

/-- Minus the block of u in the rows e_a and the columns e*_b. For u in 𝖴⁰ this is the matrix μ in
u e* = e* − x ω − e μ. -/
def eichlerScalars (u : 𝔰.G₁) : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℂ :=
  -(𝔰.isotropicColsᴴ * u.val.val * 𝔰.dualCols)

@[fun_prop]
lemma continuous_eichlerVectors : Continuous (eichlerVectors (𝔰 := 𝔰)) := by
  fun_prop [eichlerVectors]

@[fun_prop]
lemma continuous_eichlerScalars : Continuous (eichlerScalars (𝔰 := 𝔰)) := by
  fun_prop [eichlerScalars]

section

variable {u : 𝔰.G₁} {ω : Matrix 𝔰.κ (Fin 𝔰.ϱ) ℂ} {μ : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℂ}

lemma eichlerVectors_eq_of_coe_eq (hu : u.val.val = eichlerMatrix ω μ) : eichlerVectors u = ω := by
  simp [eichlerVectors, hu, eichlerMatrix, Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_sub,
    Matrix.sub_mul, inclMatrix_gram_mul_eq_self, inclMatrix_gram_mul_eq_zero,
    inclMatrix_gram_eq_one, inclMatrix_gram_eq_zero]

lemma eichlerScalars_eq_of_coe_eq (hu : u.val.val = eichlerMatrix ω μ) : eichlerScalars u = μ := by
  simp [eichlerScalars, hu, eichlerMatrix, Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_sub,
    Matrix.add_mul, Matrix.sub_mul, inclMatrix_gram_mul_eq_self, inclMatrix_gram_mul_eq_zero,
    inclMatrix_gram_eq_one, inclMatrix_gram_eq_zero]

end

lemma eichlerVectors_unipotentOf (q : 𝔰.UnipotentParams) : eichlerVectors (unipotentOf q) = q.1ᴴ :=
  eichlerVectors_eq_of_coe_eq (coe_unipotentOf_eq_eichlerMatrix q)

lemma eichlerScalars_unipotentOf (q : 𝔰.UnipotentParams) :
    eichlerScalars (unipotentOf q) = (2⁻¹ : ℂ) • (q.1 * q.1ᴴ) - skewOfReal q.2 :=
  eichlerScalars_eq_of_coe_eq (coe_unipotentOf_eq_eichlerMatrix q)

/-- An element of 𝖴⁰ is the Eichler map of its pair (ω, μ). -/
lemma coe_eq_eichlerMatrix_of_mem_besselU0 {u : 𝔰.G₁} (hu : u ∈ besselU0) :
    u.val.val = eichlerMatrix (eichlerVectors u) (eichlerScalars u) := by
  obtain ⟨q, rfl⟩ := mem_besselU0_iff_unipotentOf.1 hu
  rw [eichlerVectors_unipotentOf, eichlerScalars_unipotentOf, coe_unipotentOf_eq_eichlerMatrix]

/-- The group law for two elements of 𝖴⁰, in terms of their pairs (ω, μ). -/
lemma coe_mul_eq_eichlerMatrix {u v : 𝔰.G₁} (hu : u ∈ besselU0) (hv : v ∈ besselU0) :
    (u * v).val.val = eichlerMatrix (eichlerVectors u + eichlerVectors v)
      (eichlerScalars u + eichlerScalars v + (eichlerVectors u)ᴴ * eichlerVectors v) := by
  rw [← eichlerMatrix_mul, ← coe_eq_eichlerMatrix_of_mem_besselU0 hu,
    ← coe_eq_eichlerMatrix_of_mem_besselU0 hv, Subgroup.coe_mul, Units.val_mul]

/-- The ball of radius ρ in 𝖴⁰, in which ω has degree one and μ degree two: ‖ω‖ ≤ ρ and ‖μ‖ ≤ ρ²,
in the operator norm. -/
def homogeneousBall (ρ : ℝ) : Set (𝔰.middleGram (1 : ℂ)).besselU0 :=
  {u : besselU0 (T := 𝔰.middleGram (1 : ℂ)) |
    ‖eichlerVectors (u : 𝔰.G₁)‖ ≤ ρ ∧ ‖eichlerScalars (u : 𝔰.G₁)‖ ≤ ρ ^ 2}

lemma isClosed_homogeneousBall (ρ : ℝ) : IsClosed (homogeneousBall (𝔰 := 𝔰) ρ) := by
  apply IsClosed.and <;> exact isClosed_le (by fun_prop) continuous_const

/-- Radii add under multiplication: the product of an element of the ball of radius ρ and an element
of the ball of radius ρ' lies in the ball of radius ρ + ρ'. -/
lemma mul_mem_homogeneousBall {ρ ρ' : ℝ} {u v : (𝔰.middleGram (1 : ℂ)).besselU0}
    (hu : u ∈ homogeneousBall ρ) (hv : v ∈ homogeneousBall ρ') :
    u * v ∈ homogeneousBall (ρ + ρ') := by
  obtain ⟨hu_ω, hu_μ⟩ := hu
  obtain ⟨hv_ω, hv_μ⟩ := hv
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hu_ω
  have h_mul := coe_mul_eq_eichlerMatrix u.property v.property
  constructor
  · rw [Subgroup.coe_mul, eichlerVectors_eq_of_coe_eq h_mul]
    exact norm_add_le_of_le hu_ω hv_ω
  · rw [Subgroup.coe_mul, eichlerScalars_eq_of_coe_eq h_mul]
    calc ‖eichlerScalars u.val + eichlerScalars v.val +
          (eichlerVectors u.val)ᴴ * eichlerVectors v.val‖ ≤ ρ ^ 2 + ρ' ^ 2 + ρ * ρ' := by
          grw [norm_add₃_le, l2_opNorm_mul, l2_opNorm_conjTranspose, hu_ω, hu_μ, hv_ω, hv_μ]
      _ ≤ (ρ + ρ') ^ 2 := by nlinarith [mul_nonneg hρ ((norm_nonneg _).trans hv_ω)]

/-- On the frame-fixing unipotent group 𝖴⁰, the measure `besselHaar₀` is the pushforward of Lebesgue
measure under `unipotentOf`. For ρ > 0 it gives `homogeneousBall ρ` (‖ω‖ ≤ ρ, ‖μ‖ ≤ ρ² in operator
norm) mass ρ ^ (2ϱ(k + ϱ)) times that of the ball of radius one, where ϱ = n − 1 is the number of
hyperbolic planes and k = |κ|. -/
theorem besselHaar₀_homogeneousBall {ρ : ℝ} (hρ : 0 < ρ) :
    𝔰.besselHaar₀ (homogeneousBall ρ) =
      .ofReal (ρ ^ (2 * 𝔰.ϱ * (𝔰.k + 𝔰.ϱ))) * 𝔰.besselHaar₀ (homogeneousBall 1) := by
  -- In the parameters (a, b), where ω = aᴴ and μ = ½ a aᴴ − sk b, the measure is Lebesgue measure
  -- and the dilation (ω, μ) ↦ (ρ ω, ρ² μ) is the linear map `D (a, b) = (ρ a, ρ² b)`.
  let param (q : 𝔰.UnipotentParams) : (𝔰.middleGram (1 : ℂ)).besselU0 :=
    ⟨unipotentOf q, unipotentOf_mem_besselU0 q⟩
  have h_volume (t : ℝ) :
      𝔰.besselHaar₀ (homogeneousBall t) = volume (param ⁻¹' homogeneousBall t) :=
    map_apply (by fun_prop) (isClosed_homogeneousBall t).measurableSet
  let D : 𝔰.UnipotentParams →ₗ[ℝ] 𝔰.UnipotentParams := .prodMap (ρ • .id) (ρ ^ 2 • .id)
  have h_det : D.det = ρ ^ (2 * 𝔰.ϱ * (𝔰.k + 𝔰.ϱ)) := by
    simp [D, LinearMap.det_prodMap, Module.finrank_matrix]
    ring
  have h_vectors (q : 𝔰.UnipotentParams) :
      eichlerVectors (unipotentOf (D q)) = ρ • eichlerVectors (unipotentOf q) := by
    simp [D, eichlerVectors_unipotentOf, star_trivial ρ]
  have h_scalars (q : 𝔰.UnipotentParams) :
      eichlerScalars (unipotentOf (D q)) = ρ ^ 2 • eichlerScalars (unipotentOf q) := by
    simp [D, eichlerScalars_unipotentOf]
    module
  have h_ball : D ⁻¹' (param ⁻¹' homogeneousBall ρ) = param ⁻¹' homogeneousBall 1 := by
    ext q
    simp [param, homogeneousBall, h_vectors, h_scalars, norm_smul, hρ, abs_of_pos]
  have h_surj : Surjective D := (D.equivOfDetNeZero (h_det.trans_ne (by positivity))).surjective
  have : (volume (α := 𝔰.UnipotentParams)).IsAddHaarMeasure := prod.instIsAddHaarMeasure ..
  rw [h_volume, h_volume, ← h_ball, ← abs_of_pos (pow_pos hρ _), ← h_det,
    ← addHaar_image_linearMap, Set.image_preimage_eq _ h_surj]

lemma besselHaar₀_homogeneousBall_ne_zero {ρ : ℝ} (hρ : 0 < ρ) :
    𝔰.besselHaar₀ (homogeneousBall ρ) ≠ 0 := by
  -- The ball is a neighbourhood of `1`, where ω and μ vanish.
  have h_nhds : homogeneousBall ρ ∈ nhds (1 : (𝔰.middleGram (1 : ℂ)).besselU0) := by
    apply Filter.Eventually.and <;> apply (ContinuousAt.tendsto (by fun_prop)).eventually_le_const
    · simpa [eichlerVectors, inclMatrix_gram_eq_zero]
    · simpa [eichlerScalars, inclMatrix_gram_eq_zero] using pow_pos hρ 2
  exact (measure_pos_of_mem_nhds _ h_nhds).ne'

/-- An element of 𝖴⁰ of operator norm at most t lies in the ball of radius t. -/
lemma mem_homogeneousBall_of_norm_le {t : ℝ} {u : (𝔰.middleGram (1 : ℂ)).besselU0}
    (hu : ‖(u : 𝔰.G₁).val.val‖ ≤ t) : u ∈ homogeneousBall t := by
  -- Up to sign, ω and μ are blocks of the matrix of `u`; and `t ≤ t ^ 2`, as `1 ≤ ‖u‖ ≤ t`.
  have h_block {m : Type} [Fintype m] [DecidableEq m] {e : m → 𝔰.BesselIndex} (he : Injective e) :
      ‖-((inclMatrix ℂ e)ᴴ * (u : 𝔰.G₁).val.val * 𝔰.dualCols)‖ ≤ t := by
    grw [norm_neg, l2_opNorm_mul, l2_opNorm_mul, l2_opNorm_conjTranspose, norm_inclMatrix_le_one he,
      norm_inclMatrix_le_one (by simp [Injective]), one_mul, mul_one, hu]
  exact ⟨h_block (by simp [Injective]), (h_block Sum.inl_injective).trans
    (le_self_pow₀ ((U.one_le_norm _).trans hu) two_ne_zero)⟩

/-- On the ball of radius ρ the operator norm is at most (1 + ρ)². -/
lemma norm_le_of_mem_homogeneousBall {ρ : ℝ} {u : (𝔰.middleGram (1 : ℂ)).besselU0}
    (hu : u ∈ homogeneousBall ρ) : ‖(u : 𝔰.G₁).val.val‖ ≤ (1 + ρ) ^ 2 := by
  obtain ⟨hu_ω, hu_μ⟩ := hu
  -- In the Eichler form of `u` the four terms have norms at most `1`, `‖ω‖`, `‖ω‖` and `‖μ‖`.
  have h_block {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
      {e : m → 𝔰.BesselIndex} {e' : n → 𝔰.BesselIndex} (he : Injective e) (he' : Injective e')
      (A : Matrix m n ℂ) : ‖inclMatrix ℂ e * A * (inclMatrix ℂ e')ᴴ‖ ≤ ‖A‖ := by
    grw [l2_opNorm_mul, l2_opNorm_mul, l2_opNorm_conjTranspose, norm_inclMatrix_le_one he,
      norm_inclMatrix_le_one he', one_mul, mul_one]
  have h_definite : Injective 𝔰.indexX₀ := by simp [Injective]
  have h_dual : Injective (eStar : Fin 𝔰.ϱ → 𝔰.BesselIndex) := by simp [Injective]
  calc ‖u.val.val.val‖
      ≤ 1 + ‖(eichlerVectors u.val)ᴴ‖ + ‖eichlerVectors u.val‖ + ‖eichlerScalars u.val‖ := by
        grw [coe_eq_eichlerMatrix_of_mem_besselU0 u.property, eichlerMatrix, norm_sub_le,
          norm_sub_le, norm_add_le, norm_one, h_block Sum.inl_injective h_definite,
          h_block h_definite h_dual, h_block Sum.inl_injective h_dual]
    _ ≤ 1 + ρ + ρ + ρ ^ 2 := by grw [l2_opNorm_conjTranspose, hu_ω, hu_μ]
    _ = (1 + ρ) ^ 2 := by ring

lemma isCompact_homogeneousBall (ρ : ℝ) : IsCompact (homogeneousBall (𝔰 := 𝔰) ρ) :=
  .of_isClosed_subset ((isCompact_U_norm_le ((1 + ρ) ^ 2)).preimage_val
    (isClosed_of_entries_eq_one mem_besselU0_iff_apply)) (isClosed_homogeneousBall ρ)
    fun _ ↦ norm_le_of_mem_homogeneousBall

/-- Enlarging the radius from r² t to r² t + t, where r is the number of basis indices, at most
triples the volume of a ball. -/
lemma besselHaar₀_homogeneousBall_add_le {t : ℝ} (ht : 0 < t) :
    𝔰.besselHaar₀ (homogeneousBall (𝔰.r ^ 2 * t + t)) ≤
      3 * 𝔰.besselHaar₀ (homogeneousBall (𝔰.r ^ 2 * t)) := by
  -- The radius grows by the factor `1 + 1 / r ^ 2`, and the exponent `d` is at most `r ^ 2`.
  have hr_pos : (0 : ℝ) < 𝔰.r := mod_cast card_pos
  set d : ℕ := 2 * 𝔰.ϱ * (𝔰.k + 𝔰.ϱ) with hd_def
  have hd : d ≤ 𝔰.r ^ 2 := by
    rw [hd_def, show 𝔰.r = 𝔰.ϱ + (𝔰.k + 1 + 𝔰.ϱ) by simp]
    nlinarith
  have h_factor : ((𝔰.r ^ 2 : ℝ)⁻¹ + 1) ^ d ≤ 3 :=
    calc ((𝔰.r ^ 2 : ℝ)⁻¹ + 1) ^ d ≤ Real.exp (d * (𝔰.r ^ 2 : ℝ)⁻¹) := by
          grw [Real.add_one_le_exp, Real.exp_nat_mul]
      _ ≤ Real.exp 1 := Real.exp_le_exp.2 (mul_inv_le_one_of_le₀ (mod_cast hd) (by positivity))
      _ ≤ 3 := Real.exp_one_lt_three.le
  rw [besselHaar₀_homogeneousBall (by positivity),
    besselHaar₀_homogeneousBall (ρ := 𝔰.r ^ 2 * t) (by positivity), ← mul_assoc]
  grw [show 𝔰.r ^ 2 * t + t = ((𝔰.r ^ 2 : ℝ)⁻¹ + 1) * (𝔰.r ^ 2 * t) by field, mul_pow, h_factor,
    ENNReal.ofReal_mul zero_le_three, ENNReal.ofReal_ofNat]

open scoped Pointwise in
/-- If ‖y‖ ≤ T and u y lies in the product of the ball of radius ρ in 𝖴⁰ with the set of elements
of G₁ of norm at most T, then u lies in the ball of radius ρ + T². -/
lemma mem_homogeneousBall_of_mul_mem_smul {ρ T : ℝ} {u : (𝔰.middleGram (1 : ℂ)).besselU0}
    {y : 𝔰.G₁} (hy : ‖y.val.val‖ ≤ T)
    (huy : (u : 𝔰.G₁) * y ∈ homogeneousBall (𝔰 := 𝔰) ρ • {g : 𝔰.G₁ | ‖g.val.val‖ ≤ T}) :
    u ∈ homogeneousBall (ρ + T ^ 2) := by
  -- If `u * y = u₁ * g`, then `u₁⁻¹ * u = g * y⁻¹` has norm at most `T ^ 2`.
  obtain ⟨u₁, hu₁, g, hg, h_eq⟩ := huy
  have h_norm : ‖(u₁⁻¹ * u).val.val.val‖ ≤ T ^ 2 := by
    rw [show (u₁⁻¹ * u).val = g * y⁻¹ by
      simp [eq_mul_inv_iff_mul_eq, mul_assoc, ← h_eq, Subgroup.smul_def], sq]
    exact norm_mul_le_of_le hg ((U.norm_inv y).trans_le hy)
  simpa using mul_mem_homogeneousBall hu₁ (mem_homogeneousBall_of_norm_le h_norm)

/-- `B` is a tube of size `T` along 𝖴⁰ with base `Ω`: a compact set in G₁ of norm at most `T ^ 10`
that contains the `Ω`-translates of the elements of norm at most `T` and meets every orbit of 𝖴⁰ in
measure at most three times that of `Ω`. The measure is `New.Shape.besselHaar₀`, and norms are
operator norms of matrices. -/
structure IsTube (T : ℝ) (B : Set 𝔰.G₁) (Ω : Set (𝔰.middleGram (1 : ℂ)).besselU0) : Prop where
  /-- The tube is compact. -/
  isCompact : IsCompact B
  /-- The base is measurable. -/
  measurableSet : MeasurableSet Ω
  /-- The base has nonzero measure. -/
  measure_ne_zero : 𝔰.besselHaar₀ Ω ≠ 0
  /-- The base has finite measure. -/
  measure_ne_top : 𝔰.besselHaar₀ Ω ≠ ∞
  /-- The elements of the tube have norm at most `T ^ 10`. -/
  norm_le : ∀ y ∈ B, ‖(y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ T ^ 10
  /-- The tube contains `u * y` for `u` in the base and `y` of norm at most `T`. -/
  mul_mem : ∀ u ∈ Ω, ∀ y : 𝔰.G₁,
    ‖(y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ T → (u : 𝔰.G₁) * y ∈ B
  /-- For each `y`, the `u` in 𝖴⁰ with `u * y` in the tube have measure at most three times that
  of the base. -/
  measure_slice_le : ∀ y : 𝔰.G₁,
    𝔰.besselHaar₀ {u : (𝔰.middleGram (1 : ℂ)).besselU0 | (u : 𝔰.G₁) * y ∈ B} ≤
      3 * 𝔰.besselHaar₀ Ω

/-- Let `B` be a tube of size `T` along 𝖴⁰ with base `Ω` (`New.RealPlace.IsTube`). For every y in
G₁, the `New.Shape.besselHaar₀`-measure of {u ∈ 𝖴⁰ : u·y ∈ B}, written as the integral of the
indicator of `B`, is at most 3 times the measure of `Ω`. -/
lemma IsTube.lintegral_indicator_le {T : ℝ} {B : Set 𝔰.G₁}
    {Ω : Set (𝔰.middleGram (1 : ℂ)).besselU0} (h_tube : IsTube T B Ω) (y : 𝔰.G₁) :
    ∫⁻ u : (𝔰.middleGram (1 : ℂ)).besselU0, B.indicator 1 ((u : 𝔰.G₁) * y) ∂𝔰.besselHaar₀ ≤
      3 * 𝔰.besselHaar₀ Ω :=
  (lintegral_indicator_one_le _).trans (h_tube.measure_slice_le y)

open scoped Pointwise in
/-- Tubes exist. If `T ≥ 8 r`, where r is the number of basis indices of `𝔰.G₁`, then there are a
set `B` in the unitary group G₁ and a set `Ω` in 𝖴⁰ (the elements of the Bessel unipotent group
fixing each frame vector) with the following properties. `B` is compact, its elements have operator
norm at most `T ^ 10`, and it contains the `Ω`-translates of the elements of norm at most `T`. It
also meets every 𝖴⁰-orbit in `New.Shape.besselHaar₀`-measure at most three times that of `Ω`. -/
theorem exists_tube {T : ℝ} (hT : 8 * 𝔰.r ≤ T) :
    ∃ (B : Set 𝔰.G₁) (Ω : Set (𝔰.middleGram (1 : ℂ)).besselU0), IsTube T B Ω := by
  -- Take for `Ω` the ball of radius `ρ = r ^ 2 T ^ 2` and put `B = Ω • {‖y‖ ≤ T}`.
  have hr_one : (1 : ℝ) ≤ 𝔰.r := mod_cast card_pos
  have hT_one : 1 ≤ T := by linarith
  let ρ : ℝ := 𝔰.r ^ 2 * T ^ 2
  have hρ_one : 1 ≤ ρ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr_one) (one_le_pow₀ hT_one)
  let Ω : Set (𝔰.middleGram (1 : ℂ)).besselU0 := homogeneousBall ρ
  have hΩ : IsCompact Ω := isCompact_homogeneousBall ρ
  let B : Set 𝔰.G₁ := Ω • {y : 𝔰.G₁ | ‖(y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ T}
  refine ⟨B, Ω,
    { isCompact := hΩ.smul_set (isCompact_U_norm_le T)
      measurableSet := hΩ.measurableSet
      measure_ne_zero := besselHaar₀_homogeneousBall_ne_zero (one_pos.trans_le hρ_one)
      measure_ne_top := hΩ.measure_ne_top
      norm_le := ?_
      mul_mem := fun u hu y hy ↦ Set.smul_mem_smul hu hy
      measure_slice_le := fun y ↦ ?_ }⟩
  · rintro _ ⟨u, hu, z, hz, rfl⟩
    have hρ_le : 1 + ρ ≤ T ^ 4 :=
      calc 1 + ρ ≤ (8 * 𝔰.r) ^ 2 * T ^ 2 := by linarith
        _ ≤ T ^ 4 := by grw [hT, ← pow_add]
    calc _ ≤ (1 + ρ) ^ 2 * T := norm_mul_le_of_le (norm_le_of_mem_homogeneousBall hu) hz
      _ ≤ (T ^ 4) ^ 2 * T ^ 2 := by grw [hρ_le, ← le_self_pow₀ hT_one two_ne_zero]
      _ = T ^ 10 := by ring
  · -- If the orbit of `y` meets `B`, say `u * y = s * z`, it has the point `z = g * y` of norm at
    -- most `T`, where `g = s⁻¹ * u`; and `v * y = v / g * z`. So a right translate of the slice
    -- lies in the ball of radius `ρ + T ^ 2`, and the measure is right invariant.
    let slice : Set (𝔰.middleGram (1 : ℂ)).besselU0 := {u | u * y ∈ B}
    have h_translate : ∀ u ∈ slice, ∃ g : (𝔰.middleGram (1 : ℂ)).besselU0,
        ∀ v ∈ slice, v / g ∈ homogeneousBall (ρ + T ^ 2) := by
      rintro u ⟨s, -, z, hz, huy⟩
      refine ⟨s⁻¹ * u, fun v hv ↦ mem_homogeneousBall_of_mul_mem_smul hz ?_⟩
      rwa [show (v / (s⁻¹ * u)).val * z = v * y by
        simp [eq_inv_mul_of_mul_eq huy, div_eq_mul_inv, mul_assoc]]
    calc 𝔰.besselHaar₀ slice
        ≤ 𝔰.besselHaar₀ (homogeneousBall (ρ + T ^ 2)) := measure_le_of_div_mem h_translate
      _ ≤ 3 * 𝔰.besselHaar₀ Ω := besselHaar₀_homogeneousBall_add_le (by positivity)

end New.RealPlace

end UnipotentMeasure

/-! ## σ-finiteness of Haar measures on G₁ -/

section RealMeasures

open MeasureTheory

/-- A Haar measure on `New.Shape.G₁` is σ-finite. -/
instance New.sigmaFinite_G₁ {𝔰 : Shape} {μ : Measure 𝔰.G₁} [μ.IsHaarMeasure] : SigmaFinite μ :=
  inferInstance

end RealMeasures

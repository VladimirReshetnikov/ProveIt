import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.SplitIfs
import MoserWorm.UpperBound.PathOrder

/-!
# Opposite support faces and visiting ranks

The support-selection proof uses connectedness rather than a generic-position
assumption.  The two possible rank comparisons are finite unions of closed
sets of angles.  At a transition both comparisons hold; their four contacts
give the required strict rank bracket, including simultaneous support ties.
-/

open Set

noncomputable section

namespace MoserWorm.UpperBound

/-- Projection onto the rotating unit normal `(cos θ, sin θ)`. -/
def supportProjection (θ : ℝ) (z : Plane) : ℝ :=
  Real.cos θ * z.re + Real.sin θ * z.im

def IsUpperContact {n : ℕ} (v : Fin n → Plane) (θ : ℝ) (i : Fin n) : Prop :=
  ∀ j, supportProjection θ (v j) ≤ supportProjection θ (v i)

def IsLowerContact {n : ℕ} (v : Fin n → Plane) (θ : ℝ) (i : Fin n) : Prop :=
  ∀ j, supportProjection θ (v i) ≤ supportProjection θ (v j)

theorem supportProjection_add_pi (θ : ℝ) (z : Plane) :
    supportProjection (θ + Real.pi) z = -supportProjection θ z := by
  simp [supportProjection, Real.cos_add_pi, Real.sin_add_pi]
  ring

theorem IsUpperContact.add_pi {n : ℕ} {v : Fin n → Plane} {θ : ℝ} {i : Fin n}
    (h : IsUpperContact v θ i) : IsLowerContact v (θ + Real.pi) i := by
  intro j
  simpa only [supportProjection_add_pi, neg_le_neg_iff] using h j

theorem IsLowerContact.add_pi {n : ℕ} {v : Fin n → Plane} {θ : ℝ} {i : Fin n}
    (h : IsLowerContact v θ i) : IsUpperContact v (θ + Real.pi) i := by
  intro j
  simpa only [supportProjection_add_pi, neg_le_neg_iff] using h j

private def upperFirst {n : ℕ} (v : Fin n → Plane) (rank : Fin n → ℕ) :
    Set ℝ :=
  {θ | ∃ i j, IsUpperContact v θ i ∧ IsLowerContact v θ j ∧ rank i < rank j}

private theorem upperFirst_closed {n : ℕ} (v : Fin n → Plane) (rank : Fin n → ℕ) :
    IsClosed (upperFirst v rank) := by
  have hu (i : Fin n) : IsClosed {θ | IsUpperContact v θ i} := by
    simp only [IsUpperContact, ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le (by unfold supportProjection; fun_prop)
      (by unfold supportProjection; fun_prop)
  have hl (j : Fin n) : IsClosed {θ | IsLowerContact v θ j} := by
    simp only [IsLowerContact, ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (by unfold supportProjection; fun_prop)
      (by unfold supportProjection; fun_prop)
  have he : upperFirst v rank =
      ⋃ i : Fin n, ⋃ j : Fin n,
        ({θ | IsUpperContact v θ i} ∩ {θ | IsLowerContact v θ j}) ∩
          {θ : ℝ | rank i < rank j} := by
    ext θ
    simp only [upperFirst, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    aesop
  rw [he]
  apply isClosed_iUnion_of_finite
  intro i
  apply isClosed_iUnion_of_finite
  intro j
  exact ((hu i).inter (hl j)).inter (isClosed_const)

/-- Actual finite support contacts with a strict visiting-rank bracket.
The positive-width hypothesis is geometric; it says the finite set is not
contained in a line perpendicular to any rotating normal. -/
theorem exists_bracketing_supports_of_positive_width {n : ℕ}
    (v : Fin n → Plane) (rank : Fin n → ℕ) (hrank : Function.Injective rank)
    (hwidth : ∀ θ : ℝ, ∃ i j, supportProjection θ (v i) < supportProjection θ (v j)) :
    ∃ θ : ℝ, ∃ a b c : Fin n,
      IsLowerContact v θ a ∧ IsLowerContact v θ b ∧ IsUpperContact v θ c ∧
      rank a < rank c ∧ rank c < rank b ∧
      supportProjection θ (v a) < supportProjection θ (v c) := by
  classical
  obtain ⟨i₀, j₀, _⟩ := hwidth 0
  let : Nonempty (Fin n) := ⟨i₀⟩
  have hneq {θ : ℝ} {i j : Fin n} (hi : IsUpperContact v θ i)
      (hj : IsLowerContact v θ j) : rank i ≠ rank j := by
    intro he
    have hij := hrank he
    obtain ⟨a, b, hab⟩ := hwidth θ
    have := hi b
    have := hj a
    subst j
    linarith
  let A := upperFirst v rank
  let B : Set ℝ := {θ | ∃ i j,
    IsUpperContact v θ i ∧ IsLowerContact v θ j ∧ rank j < rank i}
  have hA : IsClosed A := upperFirst_closed v rank
  have hB : IsClosed B := by
    have he : B = (fun θ : ℝ => θ + Real.pi) ⁻¹' A := by
      ext θ
      simp only [B, A, upperFirst, mem_ofPred_eq, mem_preimage]
      constructor
      · rintro ⟨i, j, hi, hj, hji⟩
        exact ⟨j, i, hj.add_pi, hi.add_pi, hji⟩
      · rintro ⟨i, j, hi, hj, hij⟩
        refine ⟨j, i, ?_, ?_, hij⟩
        · intro k
          simpa only [supportProjection_add_pi, neg_le_neg_iff] using hj k
        · intro k
          simpa only [supportProjection_add_pi, neg_le_neg_iff] using hi k
    rw [he]
    exact hA.preimage (by fun_prop)
  have hcover : ∀ θ : ℝ, θ ∈ A ∨ θ ∈ B := by
    intro θ
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
      (fun i => supportProjection θ (v i)) Finset.univ_nonempty
    obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ
      (fun j => supportProjection θ (v j)) Finset.univ_nonempty
    have htop : IsUpperContact v θ i := fun k => hi k (Finset.mem_univ k)
    have hbot : IsLowerContact v θ j := fun k => hj k (Finset.mem_univ k)
    rcases lt_or_gt_of_ne (hneq htop hbot) with hij | hji
    · exact Or.inl ⟨i, j, htop, hbot, hij⟩
    · exact Or.inr ⟨i, j, htop, hbot, hji⟩
  have hAB : A.Nonempty ∧ B.Nonempty := by
    rcases hcover 0 with ⟨i, j, hi, hj, hij⟩ | ⟨i, j, hi, hj, hji⟩
    · exact ⟨⟨0, i, j, hi, hj, hij⟩,
        ⟨0 + Real.pi, j, i, hj.add_pi, hi.add_pi, hij⟩⟩
    · exact ⟨⟨0 + Real.pi, j, i, hj.add_pi, hi.add_pi, hji⟩,
        ⟨0, i, j, hi, hj, hji⟩⟩
  have hmeet : (A ∩ B).Nonempty := by
    by_contra hn
    have hd : Disjoint A B := Set.disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
    have hsplit := (isPreconnected_iff_subset_of_fully_disjoint_closed
      (s := (Set.univ : Set ℝ)) isClosed_univ).mp isPreconnected_univ A B hA hB
      (fun θ _ => hcover θ) hd
    rcases hsplit with hall | hall
    · obtain ⟨θ, hθ⟩ := hAB.2
      exact Set.disjoint_left.mp hd (hall (mem_univ θ)) hθ
    · obtain ⟨θ, hθ⟩ := hAB.1
      exact Set.disjoint_left.mp hd hθ (hall (mem_univ θ))
  obtain ⟨θ, ⟨i, j, hi, hj, hij⟩, ⟨k, l, hk, hl, hlk⟩⟩ := hmeet
  have hstrict {ψ : ℝ} {a c : Fin n} (ha : IsLowerContact v ψ a)
      (hc : IsUpperContact v ψ c) :
      supportProjection ψ (v a) < supportProjection ψ (v c) := by
    obtain ⟨s, t, hst⟩ := hwidth ψ
    exact lt_of_le_of_lt (ha s) (lt_of_lt_of_le hst (hc t))
  rcases lt_or_gt_of_ne (hneq hi hl) with hil | hli
  · exact ⟨θ + Real.pi, i, k, l, hi.add_pi, hk.add_pi, hl.add_pi,
      hil, hlk, hstrict hi.add_pi hl.add_pi⟩
  · exact ⟨θ, l, j, i, hl, hj, hi, hli, hij, hstrict hl hi⟩

/-- A constant projection onto a unit normal puts the set on an actual affine
line. This discharges the width hypothesis from noncollinearity. -/
theorem collinear_of_constant_projection {S : Set Plane} (θ : ℝ) (c : ℝ)
    (h : ∀ z ∈ S, supportProjection θ z = c) : Collinear ℝ S := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact collinear_empty ℝ Plane
  rw [collinear_iff_of_mem hz₀]
  refine ⟨⟨-Real.sin θ, Real.cos θ⟩, ?_⟩
  intro z hz
  let dx := z.re - z₀.re
  let dy := z.im - z₀.im
  have hp : Real.cos θ * dx + Real.sin θ * dy = 0 := by
    have h₁ := h z hz
    have h₂ := h z₀ hz₀
    dsimp [supportProjection] at h₁ h₂
    dsimp [dx, dy]
    linarith
  let r := Real.cos θ * dy - Real.sin θ * dx
  have hu := Real.cos_sq_add_sin_sq θ
  have hrx : r * (-Real.sin θ) = dx := by
    dsimp [r]
    linear_combination -(Real.cos θ) * hp + dx * hu
  have hry : r * Real.cos θ = dy := by
    dsimp [r]
    linear_combination -(Real.sin θ) * hp + dy * hu
  refine ⟨r, ?_⟩
  change z = r • (⟨-Real.sin θ, Real.cos θ⟩ : Plane) + z₀
  apply Complex.ext
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    rw [hrx]
    dsimp [dx]
    ring
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    rw [hry]
    dsimp [dy]
    ring

theorem positive_width_of_not_collinear {n : ℕ} (v : Fin n → Plane)
    (hnc : ¬ Collinear ℝ (Set.range v)) (θ : ℝ) :
    ∃ i j, supportProjection θ (v i) < supportProjection θ (v j) := by
  classical
  by_contra! h
  apply hnc
  rcases (Set.range v).eq_empty_or_nonempty with he | ⟨z, i₀, rfl⟩
  · rw [he]
    exact collinear_empty ℝ Plane
  · apply collinear_of_constant_projection θ (supportProjection θ (v i₀))
    rintro z ⟨i, rfl⟩
    exact le_antisymm (h i₀ i) (h i i₀)

/-- Rotating opposite supports produces the paper's strict visiting-rank
bracket for every noncollinear finite vertex family. No general-position
assumption about the supporting directions is made. -/
theorem exists_bracketing_supports {n : ℕ} (v : Fin n → Plane)
    (rank : Fin n → ℕ) (hrank : Function.Injective rank)
    (hnc : ¬ Collinear ℝ (Set.range v)) :
    ∃ θ : ℝ, ∃ a b c : Fin n,
      IsLowerContact v θ a ∧ IsLowerContact v θ b ∧ IsUpperContact v θ c ∧
      rank a < rank c ∧ rank c < rank b ∧
      supportProjection θ (v a) < supportProjection θ (v c) :=
  exists_bracketing_supports_of_positive_width v rank hrank
    (positive_width_of_not_collinear v hnc)

/-- A rotation taking the chosen support normal to the vertical direction. -/
def supportRotation (θ : ℝ) : Plane ≃ᵢ Plane :=
  (rotation (Circle.exp (Real.pi / 2 - θ))).toIsometryEquiv

theorem supportRotation_im (θ : ℝ) (z : Plane) :
    (supportRotation θ z).im = supportProjection θ z := by
  change ((Circle.exp (Real.pi / 2 - θ) : ℂ) * z).im = _
  rw [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [supportProjection, Complex.mul_im, Real.cos_sub, Real.sin_sub]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, Complex.ofReal_re]
  ring

/-- Reflection in the vertical axis; it preserves the floor and top heights. -/
def verticalReflection : Plane ≃ᵢ Plane :=
  (Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ)).toIsometryEquiv

theorem verticalReflection_re (z : Plane) : (verticalReflection z).re = -z.re := by
  change (-((starRingEnd ℂ) z)).re = -z.re
  simp

theorem verticalReflection_im (z : Plane) : (verticalReflection z).im = z.im := by
  change (-((starRingEnd ℂ) z)).im = z.im
  simp

/-- The normal form in actual Cartesian coordinates, obtained by a rigid
motion. The two floor vertices and the opposite top vertex have the required
strict visiting-rank order. -/
theorem normal_form_exists {n : ℕ} (v : Fin n → Plane)
    (hv : Function.Injective v) (rank : Fin n → ℕ) (hrank : Function.Injective rank)
    (hnc : ¬ Collinear ℝ (Set.range v)) :
    ∃ g : Plane ≃ᵢ Plane, ∃ a b c : Fin n,
      rank a < rank c ∧ rank c < rank b ∧
      (g (v a)).im = 0 ∧ (g (v b)).im = 0 ∧
      (g (v a)).re < (g (v b)).re ∧
      0 < (g (v c)).im ∧
      (∀ i, 0 ≤ (g (v i)).im ∧ (g (v i)).im ≤ (g (v c)).im) := by
  obtain ⟨θ, a, b, c, ha, hb, hc, hac, hcb, hheight⟩ :=
    exists_bracketing_supports v rank hrank hnc
  let g₀ := (supportRotation θ).trans
    (IsometryEquiv.addRight (-(supportRotation θ (v a))))
  have him (i : Fin n) :
      (g₀ (v i)).im = supportProjection θ (v i) - supportProjection θ (v a) := by
    change (supportRotation θ (v i) + -(supportRotation θ (v a))).im = _
    simp only [Complex.add_im, Complex.neg_im, supportRotation_im, sub_eq_add_neg]
  have hia : (g₀ (v a)).im = 0 := by rw [him]; ring
  have hib : (g₀ (v b)).im = 0 := by
    rw [him]
    have he : supportProjection θ (v b) = supportProjection θ (v a) :=
      le_antisymm (hb a) (ha b)
    rw [he, sub_self]
  have hic : 0 < (g₀ (v c)).im := by rw [him]; linarith
  have hbounds (i : Fin n) :
      0 ≤ (g₀ (v i)).im ∧ (g₀ (v i)).im ≤ (g₀ (v c)).im := by
    rw [him, him]
    constructor
    · exact sub_nonneg.mpr (ha i)
    · exact sub_le_sub_right (hc i) _
  have hne : (g₀ (v a)).re ≠ (g₀ (v b)).re := by
    intro he
    have hp : g₀ (v a) = g₀ (v b) := Complex.ext he (hia.trans hib.symm)
    have hab := hv (g₀.injective hp)
    subst b
    omega
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact ⟨g₀, a, b, c, hac, hcb, hia, hib, hab, hic, hbounds⟩
  · refine ⟨g₀.trans verticalReflection, a, b, c, hac, hcb, ?_, ?_, ?_, ?_, ?_⟩
    · change (verticalReflection (g₀ (v a))).im = 0
      rw [verticalReflection_im, hia]
    · change (verticalReflection (g₀ (v b))).im = 0
      rw [verticalReflection_im, hib]
    · change (verticalReflection (g₀ (v a))).re <
        (verticalReflection (g₀ (v b))).re
      rw [verticalReflection_re, verticalReflection_re]
      linarith
    · change 0 < (verticalReflection (g₀ (v c))).im
      rw [verticalReflection_im]
      exact hic
    · intro i
      change 0 ≤ (verticalReflection (g₀ (v i))).im ∧
        (verticalReflection (g₀ (v i))).im ≤ (verticalReflection (g₀ (v c))).im
      simp only [verticalReflection_im]
      exact hbounds i

theorem collinear_affine_image {S : Set Plane} (hS : Collinear ℝ S)
    (f : Plane →ᵃ[ℝ] Plane) : Collinear ℝ (f '' S) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hS ⊢
  obtain ⟨p, v, hp⟩ := hS
  refine ⟨f p, f.linear v, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, hr⟩ := hp x hx
  refine ⟨r, ?_⟩
  rw [hr, f.map_vadd, map_smul]

/-- For an extreme-vertex polygon the selected floor face has exactly its two
endpoint vertices. Thus the normal form selects a polygon edge, not merely
two possibly redundant points on a support line. -/
theorem normal_form_exists_extreme {n : ℕ} (v : Fin n → Plane)
    (hv : Function.Injective v) (rank : Fin n → ℕ) (hrank : Function.Injective rank)
    (hnc : ¬ Collinear ℝ (Set.range v))
    (hex : ∀ i, v i ∈ extremePoints ℝ (convexHull ℝ (Set.range v))) :
    ∃ g : Plane ≃ᵢ Plane, ∃ a b c : Fin n,
      rank a < rank c ∧ rank c < rank b ∧
      (g (v a)).im = 0 ∧ (g (v b)).im = 0 ∧
      (g (v a)).re < (g (v b)).re ∧
      0 < (g (v c)).im ∧
      (∀ i, 0 ≤ (g (v i)).im ∧ (g (v i)).im ≤ (g (v c)).im) ∧
      (∀ i, (g (v i)).im = 0 ↔ i = a ∨ i = b) := by
  obtain ⟨g, a, b, c, hac, hcb, ha, hb, hab, hc, hbounds⟩ :=
    normal_form_exists v hv rank hrank hnc
  let S : Set Plane := {z | z ∈ Set.range v ∧ (g z).im = 0}
  have hcolg : Collinear ℝ (g '' S) := by
    apply collinear_of_constant_projection (Real.pi / 2) 0
    rintro _ ⟨z, hz, rfl⟩
    simpa only [supportProjection, Real.cos_pi_div_two, Real.sin_pi_div_two,
      zero_mul, one_mul, zero_add] using hz.2
  have hcol : Collinear ℝ S := by
    have h := collinear_affine_image hcolg
      g.symm.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap
    change Collinear ℝ (g.symm '' (g '' S)) at h
    simpa only [Set.image_image, Function.comp_def, g.symm_apply_apply, Set.image_id'] using h
  have hS : S ⊆ extremePoints ℝ (convexHull ℝ (Set.range v)) := by
    rintro z ⟨⟨i, rfl⟩, _⟩
    exact hex i
  have hva : v a ∈ S := ⟨mem_range_self a, ha⟩
  have hvb : v b ∈ S := ⟨mem_range_self b, hb⟩
  have hvab : v a ≠ v b := by
    intro he
    have := hv he
    subst b
    omega
  have hsub := collinear_extreme_subset_pair hS hcol hva hvb hvab
  refine ⟨g, a, b, c, hac, hcb, ha, hb, hab, hc, hbounds, ?_⟩
  intro i
  constructor
  · intro hi
    rcases hsub ⟨mem_range_self i, hi⟩ with hi | hi
    · exact Or.inl (hv hi)
    · exact Or.inr (hv hi)
  · rintro (rfl | rfl) <;> assumption

/-- Geometric input after normalization. This structure contains no boundary
order or contact-order assumption. -/
structure FloorPolygon (n : ℕ) where
  vertex : Fin n → Plane
  injective : Function.Injective vertex
  extreme : ∀ i, vertex i ∈ extremePoints ℝ (convexHull ℝ (Set.range vertex))
  base : Fin n
  tip : Fin n
  base_zero : vertex base = 0
  tip_im : (vertex tip).im = 0
  tip_re : 0 < (vertex tip).re
  nonneg : ∀ i, 0 ≤ (vertex i).im
  floor_only : ∀ i, (vertex i).im = 0 → i = base ∨ i = tip

namespace FloorPolygon

variable {n : ℕ} (F : FloorPolygon n)

theorem base_ne_tip : F.base ≠ F.tip := by
  intro h
  have : F.vertex F.tip = 0 := h ▸ F.base_zero
  have := F.tip_re
  simp_all

theorem im_pos {i : Fin n} (ha : i ≠ F.base) (hb : i ≠ F.tip) :
    0 < (F.vertex i).im := lt_of_le_of_ne (F.nonneg i) (by
  intro h
  exact (F.floor_only i h.symm).elim ha hb)

/-- The two floor vertices precede all other vertices. The remaining order
is the increasing slope `-x/y`; all those denominators are strictly positive. -/
def key (i : Fin n) : WithBot (WithBot ℝ) :=
  if i = F.base then ⊥ else if i = F.tip then ↑(⊥ : WithBot ℝ)
  else ↑(↑(-(F.vertex i).re / (F.vertex i).im) : WithBot ℝ)

@[simp] theorem key_base : F.key F.base = ⊥ := by simp [key]
@[simp] theorem key_tip : F.key F.tip = ↑(⊥ : WithBot ℝ) := by
  simp [key, F.base_ne_tip.symm]

theorem key_other {i : Fin n} (ha : i ≠ F.base) (hb : i ≠ F.tip) :
    F.key i = ↑(↑(-(F.vertex i).re / (F.vertex i).im) : WithBot ℝ) := by
  simp [key, ha, hb]

theorem key_base_lt {i : Fin n} (ha : i ≠ F.base) : F.key F.base < F.key i := by
  simp only [key, if_neg ha]
  split_ifs <;> exact WithBot.bot_lt_coe _

theorem key_lt_iff_turn_pos {i j : Fin n} (hia : i ≠ F.base) (hja : j ≠ F.base) :
    F.key i < F.key j ↔ 0 < turn 0 (F.vertex i) (F.vertex j) := by
  by_cases hi : i = F.tip
  · subst i
    by_cases hj : j = F.tip
    · subst j; simp [turn, cross_apply, mul_comm]
    · rw [F.key_tip, F.key_other hja hj]
      simp only [WithBot.coe_lt_coe, WithBot.bot_lt_coe, true_iff]
      simpa [turn, cross_apply, F.tip_im] using mul_pos F.tip_re (F.im_pos hja hj)
  · by_cases hj : j = F.tip
    · subst j
      rw [F.key_other hia hi, F.key_tip]
      simp only [WithBot.coe_lt_coe, WithBot.not_lt_bot, false_iff, not_lt]
      have hh := mul_pos (F.im_pos hia hi) F.tip_re
      simp only [turn, cross_apply, sub_zero, F.tip_im, mul_zero, zero_sub]
      linarith
    · rw [F.key_other hia hi, F.key_other hja hj]
      simp only [WithBot.coe_lt_coe]
      rw [div_lt_div_iff₀ (F.im_pos hia hi) (F.im_pos hja hj)]
      simp only [turn, cross_apply, sub_zero]
      constructor <;> intro h <;> nlinarith

theorem key_injective : Function.Injective F.key := by
  intro i j he
  by_contra hij
  by_cases hi : i = F.base
  · subst i; exact (ne_of_lt (F.key_base_lt (Ne.symm hij))) he
  by_cases hj : j = F.base
  · subst j; exact (ne_of_lt (F.key_base_lt hi)) he.symm
  have ht : turn 0 (F.vertex i) (F.vertex j) = 0 := by
    have h₁ := mt (F.key_lt_iff_turn_pos hi hj).mpr (not_lt_of_ge he.ge)
    have h₂ := mt (F.key_lt_iff_turn_pos hj hi).mpr (not_lt_of_ge he.le)
    have hs : turn 0 (F.vertex j) (F.vertex i) = -turn 0 (F.vertex i) (F.vertex j) := by
      simp only [turn, cross_apply, sub_zero]; ring
    rw [hs] at h₂
    linarith
  have hcol := collinear_of_turn_eq_zero ht
  rw [← F.base_zero] at hcol
  exact inGenPos_of_extreme F.injective F.extreme F.base i j (Ne.symm hi) (Ne.symm hj) hij hcol

/-- An actual boundary enumeration, constructed by sorting the finite slopes. -/
theorem exists_boundary : ∃ e : Equiv.Perm (Fin n),
    StrictMono (F.key ∘ e) ∧
    (∀ i j k, i < j → j < k → 0 < turn (F.vertex (e i)) (F.vertex (e j)) (F.vertex (e k))) := by
  obtain ⟨e, he⟩ := exists_sorted_permutation F.key F.key_injective
  refine ⟨e, he, ?_⟩
  intro i j k hij hjk
  have hj : e j ≠ F.base := by
    intro h
    have hh := he hij
    simp only [Function.comp_apply, h, F.key_base, not_lt_bot] at hh
  have hk : e k ≠ F.base := by
    intro h
    have hh := he hjk
    simp only [Function.comp_apply, h, F.key_base, not_lt_bot] at hh
  have htjk := (F.key_lt_iff_turn_pos hj hk).mp (he hjk)
  by_cases hi : e i = F.base
  · simpa only [hi, F.base_zero] using htjk
  · have htij := (F.key_lt_iff_turn_pos hi hj).mp (he hij)
    have htik := (F.key_lt_iff_turn_pos hi hk).mp (he (hij.trans hjk))
    have hzero : (0 : Plane) ∈ convexHull ℝ (Set.range F.vertex) := by
      rw [← F.base_zero]; exact (F.extreme F.base).1
    exact turn_pos_of_radial_order (convex_convexHull ℝ _) hzero (F.extreme (e i)).1
      (F.extreme (e j)) (F.extreme (e k)).1 htij htjk htik

end FloorPolygon

/-- Affine isometries preserve actual extreme points. -/
theorem extreme_isometry_image {Q : Set Plane} {x : Plane}
    (hx : x ∈ extremePoints ℝ Q) (g : Plane ≃ᵢ Plane) :
    g x ∈ extremePoints ℝ (g '' Q) := by
  have hh := mem_extremePoints_iff_forall_segment.mp hx
  apply mem_extremePoints_iff_forall_segment.mpr
  refine ⟨mem_image_of_mem g hh.1, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hs
  have himage := image_segment ℝ g.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap y z
  change g '' segment ℝ y z = segment ℝ (g y) (g z) at himage
  rw [← himage] at hs
  obtain ⟨w, hw, he⟩ := hs
  have hwx := g.injective he
  rw [hwx] at hw
  rcases hh.2 y hy z hz hw with h | h
  · exact Or.inl (congrArg g h)
  · exact Or.inr (congrArg g h)

/-- The actual polygon-to-floor-normal-form endpoint. -/
theorem floorPolygon_exists {n : ℕ} (v : Fin n → Plane)
    (hv : Function.Injective v) (rank : Fin n → ℕ) (hrank : Function.Injective rank)
    (hnc : ¬ Collinear ℝ (Set.range v))
    (hex : ∀ i, v i ∈ extremePoints ℝ (convexHull ℝ (Set.range v))) :
    ∃ (g : Plane ≃ᵢ Plane) (F : FloorPolygon n) (top : Fin n),
      (∀ i, F.vertex i = g (v i)) ∧ rank F.base < rank top ∧ rank top < rank F.tip ∧
      0 < (F.vertex top).im ∧ (∀ i, (F.vertex i).im ≤ (F.vertex top).im) := by
  obtain ⟨g, a, b, c, hac, hcb, ha, hb, hab, hc, hbound, hfloor⟩ :=
    normal_form_exists_extreme v hv rank hrank hnc hex
  let g' := g.trans (IsometryEquiv.addRight (-(g (v a))))
  let w : Fin n → Plane := fun i => g' (v i)
  have hw (i : Fin n) : w i = g (v i) - g (v a) := rfl
  have him (i : Fin n) : (w i).im = (g (v i)).im := by
    rw [hw, Complex.sub_im, ha, sub_zero]
  have hzero : w a = 0 := by rw [hw, sub_self]
  have hHull : convexHull ℝ (Set.range w) = g' '' convexHull ℝ (Set.range v) := by
    have hh := g'.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap.image_convexHull (Set.range v)
    change g' '' convexHull ℝ (Set.range v) = convexHull ℝ (g' '' Set.range v) at hh
    rw [hh]
    congr 1
    exact Set.range_comp g' v
  have hwex (i : Fin n) : w i ∈ extremePoints ℝ (convexHull ℝ (Set.range w)) := by
    rw [hHull]
    exact extreme_isometry_image (hex i) g'
  let F : FloorPolygon n := {
    vertex := w
    injective := g'.injective.comp hv
    extreme := hwex
    base := a
    tip := b
    base_zero := hzero
    tip_im := (him b).trans hb
    tip_re := by rw [hw, Complex.sub_re]; linarith
    nonneg := fun i => (him i).symm ▸ (hbound i).1
    floor_only := fun i hi => (hfloor i).mp ((him i).symm ▸ hi) }
  exact ⟨g', F, c, fun _ => rfl, hac, hcb, by change 0 < (w c).im; simpa only [him] using hc,
    fun i => by change (w i).im ≤ (w c).im; simpa only [him] using (hbound i).2⟩

namespace FloorPolygon

variable {n : ℕ} (F : FloorPolygon n)

/-- Coordinate form of the actual support-maximizer condition. -/
def Supports (u : Plane) (i : Fin n) : Prop :=
  ∀ j, u.re * (F.vertex j).re + u.im * (F.vertex j).im ≤
    u.re * (F.vertex i).re + u.im * (F.vertex i).im

theorem supports_iff_inner (u : Plane) (i : Fin n) : F.Supports u i ↔
    ∀ j, inner ℝ u (F.vertex j) ≤ inner ℝ u (F.vertex i) := by
  have hinner (x : Plane) : inner ℝ u x = u.re * x.re + u.im * x.im := by
    change (x * starRingEnd ℂ u).re = _
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simp only [Supports, hinner]

theorem exists_support (u : Plane) : ∃ i, F.Supports u i := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => u.re * (F.vertex i).re + u.im * (F.vertex i).im)
    ⟨F.base, Finset.mem_univ _⟩
  exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩

theorem support_nonneg {u : Plane} {i : Fin n} (h : F.Supports u i) :
    0 ≤ u.re * (F.vertex i).re + u.im * (F.vertex i).im := by
  simpa only [F.base_zero, Complex.zero_re, Complex.zero_im, mul_zero, zero_add] using h F.base

theorem right_support_ne_base {u : Plane} {i : Fin n}
    (hu : 0 < u.re) (h : F.Supports u i) : i ≠ F.base := by
  intro he
  have hh := h F.tip
  rw [he, F.base_zero, F.tip_im] at hh
  simp only [Complex.zero_re, Complex.zero_im, mul_zero, add_zero] at hh
  nlinarith [F.tip_re]

theorem left_support_ne_tip {u : Plane} {i : Fin n}
    (hu : u.re < 0) (h : F.Supports u i) : i ≠ F.tip := by
  intro he
  have hh := F.support_nonneg h
  rw [he, F.tip_im, mul_zero, add_zero] at hh
  nlinarith [F.tip_re]

theorem key_le_of_turn_nonneg {i j : Fin n} (hi : i ≠ F.base) (hj : j ≠ F.base)
    (ht : 0 ≤ turn 0 (F.vertex i) (F.vertex j)) : F.key i ≤ F.key j := by
  apply le_of_not_gt
  intro h
  have hh := (F.key_lt_iff_turn_pos hj hi).mp h
  have hs : turn 0 (F.vertex j) (F.vertex i) = -turn 0 (F.vertex i) (F.vertex j) := by
    simp only [turn, cross_apply, sub_zero]; ring
  rw [hs] at hh
  linarith

/-- A right support contact precedes every vertex above it in radial order. -/
theorem turn_nonneg_right {u : Plane} {i j : Fin n} (hu : 0 < u.re)
    (hs : F.Supports u i) (hy : (F.vertex i).im ≤ (F.vertex j).im) :
    0 ≤ turn 0 (F.vertex i) (F.vertex j) := by
  have h₁ := mul_nonneg (F.nonneg i) (sub_nonneg.mpr (hs j))
  have h₂ := mul_nonneg (sub_nonneg.mpr hy) (F.support_nonneg hs)
  have hid : u.re * turn 0 (F.vertex i) (F.vertex j) =
      (F.vertex i).im * ((u.re * (F.vertex i).re + u.im * (F.vertex i).im) -
        (u.re * (F.vertex j).re + u.im * (F.vertex j).im)) +
      ((F.vertex j).im - (F.vertex i).im) *
        (u.re * (F.vertex i).re + u.im * (F.vertex i).im) := by
    simp only [turn, cross_apply, sub_zero]; ring
  have hh : 0 ≤ u.re * turn 0 (F.vertex i) (F.vertex j) := by rw [hid]; linarith
  nlinarith

/-- A left support contact follows every vertex above it in radial order. -/
theorem turn_nonneg_left {u : Plane} {i j : Fin n} (hu : u.re < 0)
    (hs : F.Supports u j) (hy : (F.vertex j).im ≤ (F.vertex i).im) :
    0 ≤ turn 0 (F.vertex i) (F.vertex j) := by
  have h₁ := mul_nonneg (F.nonneg j) (sub_nonneg.mpr (hs i))
  have h₂ := mul_nonneg (sub_nonneg.mpr hy) (F.support_nonneg hs)
  have hid : (-u.re) * turn 0 (F.vertex i) (F.vertex j) =
      (F.vertex j).im * ((u.re * (F.vertex j).re + u.im * (F.vertex j).im) -
        (u.re * (F.vertex i).re + u.im * (F.vertex i).im)) +
      ((F.vertex i).im - (F.vertex j).im) *
        (u.re * (F.vertex j).re + u.im * (F.vertex j).im) := by
    simp only [turn, cross_apply, sub_zero]; ring
  have hh : 0 ≤ (-u.re) * turn 0 (F.vertex i) (F.vertex j) := by rw [hid]; linarith
  nlinarith

/-- Strict angular order of right normals gives weak height order even when
several normals select the same extreme vertex. -/
theorem right_support_height {u v : Plane} {i j : Fin n}
    (hu : 0 < u.re) (hv : 0 < v.re) (huv : 0 < cross u v)
    (hi : F.Supports u i) (hj : F.Supports v j) :
    (F.vertex i).im ≤ (F.vertex j).im := by
  have h₁ := mul_nonneg hu.le (sub_nonneg.mpr (hj i))
  have h₂ := mul_nonneg hv.le (sub_nonneg.mpr (hi j))
  have hid : cross u v * ((F.vertex j).im - (F.vertex i).im) =
      u.re * ((v.re * (F.vertex j).re + v.im * (F.vertex j).im) -
        (v.re * (F.vertex i).re + v.im * (F.vertex i).im)) +
      v.re * ((u.re * (F.vertex i).re + u.im * (F.vertex i).im) -
        (u.re * (F.vertex j).re + u.im * (F.vertex j).im)) := by
    simp only [cross_apply]; ring
  have hh : 0 ≤ cross u v * ((F.vertex j).im - (F.vertex i).im) := by rw [hid]; linarith
  nlinarith

theorem left_support_height {u v : Plane} {i j : Fin n}
    (hu : u.re < 0) (hv : v.re < 0) (huv : 0 < cross u v)
    (hi : F.Supports u i) (hj : F.Supports v j) :
    (F.vertex j).im ≤ (F.vertex i).im := by
  have h₁ := mul_nonneg (neg_nonneg.mpr hu.le) (sub_nonneg.mpr (hj i))
  have h₂ := mul_nonneg (neg_nonneg.mpr hv.le) (sub_nonneg.mpr (hi j))
  have hid : cross u v * ((F.vertex i).im - (F.vertex j).im) =
      (-u.re) * ((v.re * (F.vertex j).re + v.im * (F.vertex j).im) -
        (v.re * (F.vertex i).re + v.im * (F.vertex i).im)) +
      (-v.re) * ((u.re * (F.vertex i).re + u.im * (F.vertex i).im) -
        (u.re * (F.vertex j).re + u.im * (F.vertex j).im)) := by
    simp only [cross_apply]; ring
  have hh : 0 ≤ cross u v * ((F.vertex i).im - (F.vertex j).im) := by rw [hid]; linarith
  nlinarith

/-- The final copy of the floor base is placed after every other boundary
vertex, allowing coincident left contacts at the cyclic cut. -/
def endKey (i : Fin n) : WithTop (WithBot (WithBot ℝ)) :=
  if i = F.base then ⊤ else ↑(F.key i)

@[simp] theorem endKey_base : F.endKey F.base = ⊤ := by simp [endKey]

theorem endKey_le {i j : Fin n} (hi : i ≠ F.base) (hj : j ≠ F.base)
    (h : F.key i ≤ F.key j) : F.endKey i ≤ F.endKey j := by
  simpa only [endKey, if_neg hi, if_neg hj, WithTop.coe_le_coe] using h

theorem endKey_tip_le (j : Fin n) : F.endKey F.tip ≤ F.endKey j := by
  by_cases ha : j = F.base
  · rw [ha, F.endKey_base]; exact le_top
  apply F.endKey_le F.base_ne_tip.symm ha
  by_cases hb : j = F.tip
  · rw [hb]
  · rw [F.key_tip, F.key_other ha hb]
    exact WithBot.coe_le_coe.mpr bot_le

theorem endKey_right {u v : Plane} {i j : Fin n}
    (hu : 0 < u.re) (hv : 0 < v.re) (huv : 0 < cross u v)
    (hi : F.Supports u i) (hj : F.Supports v j) : F.endKey i ≤ F.endKey j := by
  have hia := F.right_support_ne_base hu hi
  have hja := F.right_support_ne_base hv hj
  exact F.endKey_le hia hja (F.key_le_of_turn_nonneg hia hja
    (F.turn_nonneg_right hu hi (F.right_support_height hu hv huv hi hj)))

theorem endKey_left {u v : Plane} {i j : Fin n}
    (hu : u.re < 0) (hv : v.re < 0) (huv : 0 < cross u v)
    (hi : F.Supports u i) (hj : F.Supports v j) : F.endKey i ≤ F.endKey j := by
  have hy := F.left_support_height hu hv huv hi hj
  by_cases hja : j = F.base
  · rw [hja, F.endKey_base]; exact le_top
  have hia : i ≠ F.base := by
    intro he
    rw [he, F.base_zero, Complex.zero_im] at hy
    have heq := le_antisymm hy (F.nonneg j)
    exact (F.floor_only j heq).elim hja (F.left_support_ne_tip hv hj)
  exact F.endKey_le hia hja (F.key_le_of_turn_nonneg hia hja (F.turn_nonneg_left hv hj hy))

theorem endKey_right_top {u : Plane} {i top : Fin n} (hu : 0 < u.re)
    (hi : F.Supports u i) (ht : 0 < (F.vertex top).im)
    (hmax : ∀ j, (F.vertex j).im ≤ (F.vertex top).im) : F.endKey i ≤ F.endKey top := by
  have hia := F.right_support_ne_base hu hi
  have hta : top ≠ F.base := by intro h; rw [h, F.base_zero] at ht; exact lt_irrefl 0 ht
  exact F.endKey_le hia hta (F.key_le_of_turn_nonneg hia hta (F.turn_nonneg_right hu hi (hmax i)))

theorem endKey_top_left {u : Plane} {j top : Fin n} (hu : u.re < 0)
    (hj : F.Supports u j) (ht : 0 < (F.vertex top).im)
    (hmax : ∀ i, (F.vertex i).im ≤ (F.vertex top).im) : F.endKey top ≤ F.endKey j := by
  by_cases hja : j = F.base
  · rw [hja, F.endKey_base]; exact le_top
  have hta : top ≠ F.base := by intro h; rw [h, F.base_zero] at ht; exact lt_irrefl 0 ht
  exact F.endKey_le hta hja (F.key_le_of_turn_nonneg hta hja (F.turn_nonneg_left hu hj (hmax j)))

end FloorPolygon

namespace FloorPolygon

/-- Actual support contacts are weakly ordered around the closed boundary.
All tie handling is in the proof; no order assumption on the contacts occurs. -/
theorem contact_endKey_order {n kR kL : ℕ} (F : FloorPolygon n)
    (top : Fin n) (ht : 0 < (F.vertex top).im)
    (hmax : ∀ i, (F.vertex i).im ≤ (F.vertex top).im)
    (contact : ContactIndex kR kL → Fin n)
    (_hbase : contact (floorMinus kR kL) = F.base)
    (htip : contact (floorPlus kR kL) = F.tip)
    (htop : contact (topIndex kR kL) = top)
    (uR : Fin kR → Plane) (uL : Fin kL → Plane)
    (hRsign : ∀ i, 0 < (uR i).re) (hLsign : ∀ i, (uL i).re < 0)
    (hRangle : ∀ i j, i < j → 0 < cross (uR i) (uR j))
    (hLangle : ∀ i j, i < j → 0 < cross (uL i) (uL j))
    (hR : ∀ i, F.Supports (uR i) (contact (rightIndex kL i)))
    (hL : ∀ i, F.Supports (uL i) (contact (leftIndex kR i))) :
    ∀ a b, a ≤ b → a ≠ floorMinus kR kL →
      F.endKey (contact a) ≤ F.endKey (contact b) := by
  intro a b hab ha
  have hRt (i : Fin kR) : F.endKey (contact (rightIndex kL i)) ≤ F.endKey top :=
    F.endKey_right_top (hRsign i) (hR i) ht hmax
  have htL (i : Fin kL) : F.endKey top ≤ F.endKey (contact (leftIndex kR i)) :=
    F.endKey_top_left (hLsign i) (hL i) ht hmax
  rcases contactIndex_cases a with he | he | ⟨i, he⟩ | he | ⟨i, he⟩
  · exact False.elim (ha he)
  · rw [he, htip]; exact F.endKey_tip_le _
  · subst a
    rcases contactIndex_cases b with he | he | ⟨j, he⟩ | he | ⟨j, he⟩
    · subst b; change i.val + 2 ≤ 0 at hab; omega
    · subst b; change i.val + 2 ≤ 1 at hab; omega
    · subst b
      change i.val + 2 ≤ j.val + 2 at hab
      have hij : i ≤ j := by change i.val ≤ j.val; omega
      rcases hij.eq_or_lt with h | h
      · rw [h]
      · exact F.endKey_right (hRsign i) (hRsign j) (hRangle i j h) (hR i) (hR j)
    · rw [he, htop]; exact hRt i
    · rw [he]; exact (hRt i).trans (htL j)
  · subst a
    rcases contactIndex_cases b with he | he | ⟨j, he⟩ | he | ⟨j, he⟩
    · subst b; change kR + 2 ≤ 0 at hab; omega
    · subst b; change kR + 2 ≤ 1 at hab; omega
    · subst b; change kR + 2 ≤ j.val + 2 at hab; omega
    · rw [he]
    · rw [he, htop]; exact htL j
  · subst a
    rcases contactIndex_cases b with he | he | ⟨j, he⟩ | he | ⟨j, he⟩
    · subst b; change kR + 3 + i.val ≤ 0 at hab; omega
    · subst b; change kR + 3 + i.val ≤ 1 at hab; omega
    · subst b; change kR + 3 + i.val ≤ j.val + 2 at hab; omega
    · subst b; change kR + 3 + i.val ≤ kR + 2 at hab; omega
    · subst b
      change kR + 3 + i.val ≤ kR + 3 + j.val at hab
      have hij : i ≤ j := by change i.val ≤ j.val; omega
      rcases hij.eq_or_lt with h | h
      · rw [h]
      · exact F.endKey_left (hLsign i) (hLsign j) (hLangle i j h) (hL i) (hL j)

variable {k : ℕ} (F : FloorPolygon (k + 1))

theorem sorted_base (e : Equiv.Perm (Fin (k + 1))) (he : StrictMono (F.key ∘ e)) :
    e 0 = F.base := by
  have h : (F.key ∘ e) (e.symm F.base) ≤ (F.key ∘ e) 0 := by
    simp only [Function.comp_apply, e.apply_symm_apply, F.key_base]
    exact bot_le
  have hh := he.le_iff_le.mp h
  have hzero : e.symm F.base = 0 := Fin.ext (Nat.le_zero.mp hh)
  simpa only [e.apply_symm_apply] using congrArg e hzero.symm

/-- Boundary position with the base placed at the final, repeated index. -/
def endPosition (e : Equiv.Perm (Fin (k + 1))) (i : Fin (k + 1)) : Fin (k + 2) :=
  if i = F.base then ⟨k + 1, by omega⟩ else (e.symm i).castSucc

theorem endPosition_mono (e : Equiv.Perm (Fin (k + 1))) (he : StrictMono (F.key ∘ e))
    {i j : Fin (k + 1)} (h : F.endKey i ≤ F.endKey j) : F.endPosition e i ≤ F.endPosition e j := by
  by_cases hj : j = F.base
  · simp only [endPosition, if_pos hj]
    split_ifs <;> change _ ≤ k + 1 <;> omega
  have hi : i ≠ F.base := by
    intro hi
    simp only [endKey, if_pos hi, if_neg hj] at h
    exact WithTop.not_top_le_coe _ h
  simp only [endPosition, if_neg hi, if_neg hj, Fin.castSucc_le_castSucc_iff]
  apply he.le_iff_le.mp
  simpa only [endKey, if_neg hi, if_neg hj, WithTop.coe_le_coe,
    Function.comp_apply, e.apply_symm_apply] using h

theorem endPosition_vertex (e : Equiv.Perm (Fin (k + 1))) (he : StrictMono (F.key ∘ e))
    (i : Fin (k + 1)) : e (closedBoundaryIndex k (F.endPosition e i)) = i := by
  by_cases hi : i = F.base
  · simp only [endPosition, if_pos hi, closedBoundaryIndex, Fin.val_mk, ↓reduceIte]
    exact (F.sorted_base e he).trans hi.symm
  · simp only [endPosition, if_neg hi]
    have hh : closedBoundaryIndex k (e.symm i).castSucc = e.symm i := by
      apply Fin.ext
      exact closedBoundaryIndex_of_lt _ (e.symm i).isLt
    rw [hh, e.apply_symm_apply]

/-- Completed prefixes of a shortest path, for actual support contacts of an
actual extreme polygon. The theorem constructs and discharges both boundary
order and weak contact order, including the repeated floor base. -/
theorem support_completed_prefix {V : Set Plane} (P : ShortestVertexPath V)
    (F : FloorPolygon (P.edges + 1)) (hvertex : ∀ i, P.vertex i = F.vertex i)
    {kR kL : ℕ} (top : Fin (P.edges + 1)) (ht : 0 < (F.vertex top).im)
    (hmax : ∀ i, (F.vertex i).im ≤ (F.vertex top).im)
    (contact : ContactIndex kR kL → Fin (P.edges + 1))
    (hbase : contact (floorMinus kR kL) = F.base)
    (htip : contact (floorPlus kR kL) = F.tip)
    (htop : contact (topIndex kR kL) = top)
    (uR : Fin kR → Plane) (uL : Fin kL → Plane)
    (hRsign : ∀ i, 0 < (uR i).re) (hLsign : ∀ i, (uL i).re < 0)
    (hRangle : ∀ i j, i < j → 0 < cross (uR i) (uR j))
    (hLangle : ∀ i j, i < j → 0 < cross (uL i) (uL j))
    (hR : ∀ i, F.Supports (uR i) (contact (rightIndex kL i)))
    (hL : ∀ i, F.Supports (uL i) (contact (leftIndex kR i))) (r : ℕ) :
    IsBoundaryInterval (completedPrefix (fun l => (contact l).val) r) := by
  obtain ⟨e, he, hturn⟩ := F.exists_boundary
  let boundary := F.vertex ∘ e
  have hrange : Set.range boundary = Set.range F.vertex := by
    rw [Set.range_comp, e.surjective.range_eq, Set.image_univ]
  have hboundary (a b c d : Fin (P.edges + 1))
      (h : alternatingChords a.val b.val c.val d.val) :
      (segment ℝ (boundary a) (boundary b) ∩ segment ℝ (boundary c) (boundary d)).Nonempty :=
    alternating_segments_intersect boundary
      (fun i => by rw [hrange]; exact F.extreme (e i)) hturn h
  have hPF : Set.range F.vertex = V := by
    exact (congrArg Set.range (funext fun i => (hvertex i).symm)).trans P.range_eq
  have hV : V ⊆ extremePoints ℝ (convexHull ℝ V) := by
    rw [← hPF]
    rintro _ ⟨i, rfl⟩
    exact F.extreme i
  let lift : ContactIndex kR kL → Fin (P.edges + 2) := fun l =>
    if l = floorMinus kR kL then 0 else F.endPosition e (contact l)
  have hlift : Monotone lift := by
    intro a b hab
    by_cases ha : a = floorMinus kR kL
    · simp only [lift, if_pos ha]; exact Fin.zero_le _
    have hb : b ≠ floorMinus kR kL := by
      intro hb
      have hb0 : b.val = 0 := congrArg Fin.val hb
      change a.val ≤ b.val at hab
      have ha0 : a.val = 0 := by omega
      exact ha (Fin.ext ha0)
    simp only [lift, if_neg ha, if_neg hb]
    exact F.endPosition_mono e he (F.contact_endKey_order top ht hmax contact hbase htip htop
      uR uL hRsign hLsign hRangle hLangle hR hL a b hab ha)
  have hliftVertex (l : ContactIndex kR kL) :
      e (closedBoundaryIndex P.edges (lift l)) = contact l := by
    by_cases hl : l = floorMinus kR kL
    · simp only [lift, if_pos hl]
      have hz : closedBoundaryIndex P.edges 0 = 0 := by
        apply Fin.ext; simp [closedBoundaryIndex]
      rw [hz, F.sorted_base e he, hl, hbase]
    · simp only [lift, if_neg hl]
      exact F.endPosition_vertex e he _
  have hpath := P.contact_prefix_boundaryInterval hV boundary e.symm
    (fun i => by simpa only [boundary, Function.comp_apply, e.apply_symm_apply] using hvertex i)
    hboundary lift hlift r
  simpa only [Equiv.symm_symm, hliftVertex] using hpath

end FloorPolygon

/-- The finite normalized witness consumed by the upper certificate argument.
Every geometric field is constructed by `normalized_witness_exists`. -/
structure NormalizedWitness (K : Set Plane) where
  vertices : Set Plane
  finite : vertices.Finite
  path : ShortestVertexPath vertices
  polygon : FloorPolygon (path.edges + 1)
  vertex_eq : ∀ i, path.vertex i = polygon.vertex i
  top : Fin (path.edges + 1)
  base_before_top : polygon.base.val < top.val
  top_before_tip : top.val < polygon.tip.val
  top_pos : 0 < (polygon.vertex top).im
  top_max : ∀ i, (polygon.vertex i).im ≤ (polygon.vertex top).im
  uncovered : ¬ CoversSet K (convexHull ℝ vertices)
  length_le : pathLen (natExt path.vertex) path.edges ≤ 1

/-- Failure to cover an actual unit arc produces the finite normal-form
witness, with rank bracket and shortest-path length bound proved rather than
postulated. This is the entry point for the combined upper-bound theorem. -/
theorem normalized_witness_exists {K : Set Plane} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hsegment : ContainsUnitSegment K)
    {γ : ℝ → Plane} (hγ : IsUnitArc γ) (hmiss : ¬ Covers K γ) :
    Nonempty (NormalizedWitness K) := by
  obtain ⟨V, _, hext, hnc, hmissV, P, hlen⟩ :=
    finite_witness_noncollinear hK hconv hsegment hγ hmiss
  have hncP : ¬ Collinear ℝ (Set.range P.vertex) := by
    simpa only [P.range_eq] using hnc
  have hexP (i : Fin (P.edges + 1)) :
      P.vertex i ∈ extremePoints ℝ (convexHull ℝ (Set.range P.vertex)) := by
    have hh := hext.subset (P.range_eq.subset (mem_range_self i))
    simpa only [P.range_eq] using hh
  obtain ⟨g, F, top, hF, hbt, htt, htp, htm⟩ :=
    floorPolygon_exists P.vertex P.injective (fun i => i.val) Fin.val_injective hncP hexP
  have hHull : convexHull ℝ (g '' (V : Set Plane)) = g '' convexHull ℝ (V : Set Plane) := by
    exact (g.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap.image_convexHull _).symm
  refine ⟨{
    vertices := g '' (V : Set Plane)
    finite := V.finite_toSet.image g
    path := P.mapIsometry g
    polygon := F
    vertex_eq := fun i => (hF i).symm
    top := top
    base_before_top := hbt
    top_before_tip := htt
    top_pos := htp
    top_max := htm
    uncovered := ?_
    length_le := ?_ }⟩
  · intro hc
    rw [hHull] at hc
    exact hmissV ((coversSet_isometry_image_iff K _ g).mp hc)
  · simpa only [P.mapIsometry_length g] using hlen

/-- Evaluation at a contact rank agrees with the corresponding polygon vertex;
this connects directly to `Length.completed_prefix_length_bound`. -/
theorem NormalizedWitness.contact_point {K : Set Plane} (W : NormalizedWitness K)
    (i : Fin (W.path.edges + 1)) :
    natExt W.path.vertex i.val = W.polygon.vertex i := by
  rw [natExt_of_le W.path.vertex (by omega)]
  exact W.vertex_eq i

/-- Packaged geometric contact-prefix endpoint for the final upper theorem. -/
theorem NormalizedWitness.support_completed_prefix {K : Set Plane} (W : NormalizedWitness K)
    {kR kL : ℕ} (contact : ContactIndex kR kL → Fin (W.path.edges + 1))
    (hbase : contact (floorMinus kR kL) = W.polygon.base)
    (htip : contact (floorPlus kR kL) = W.polygon.tip)
    (htop : contact (topIndex kR kL) = W.top)
    (uR : Fin kR → Plane) (uL : Fin kL → Plane)
    (hRsign : ∀ i, 0 < (uR i).re) (hLsign : ∀ i, (uL i).re < 0)
    (hRangle : ∀ i j, i < j → 0 < cross (uR i) (uR j))
    (hLangle : ∀ i j, i < j → 0 < cross (uL i) (uL j))
    (hR : ∀ i, W.polygon.Supports (uR i) (contact (rightIndex kL i)))
    (hL : ∀ i, W.polygon.Supports (uL i) (contact (leftIndex kR i))) (r : ℕ) :
    IsBoundaryInterval (completedPrefix (fun l => (contact l).val) r) :=
  W.polygon.support_completed_prefix W.path W.vertex_eq W.top W.top_pos W.top_max
    contact hbase htip htop uR uL hRsign hLsign hRangle hLangle hR hL r

end MoserWorm.UpperBound

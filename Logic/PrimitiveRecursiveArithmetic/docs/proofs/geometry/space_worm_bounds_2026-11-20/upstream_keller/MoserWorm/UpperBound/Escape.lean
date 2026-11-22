import MoserWorm.Common.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Support expansions, the corner translation criterion, and strict weighted rows. -/

open Set Finset

noncomputable section

namespace MoserWorm.UpperBound

/-- Support of a set in a given normal direction. -/
def support (C : Set Plane) (u : Plane) : ℝ :=
  sSup ((fun x => inner ℝ u x) '' C)

theorem support_attained {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    (u : Plane) : ∃ x ∈ C, inner ℝ u x = support C u := by
  have hi : IsCompact ((fun x => inner ℝ u x) '' C) := hC.image (by fun_prop)
  exact hi.isClosed.csSup_mem (hne.image _) hi.bddAbove

theorem le_support {C : Set Plane} (hC : IsCompact C) {x : Plane} (hx : x ∈ C)
    (u : Plane) : inner ℝ u x ≤ support C u :=
  le_csSup ((hC.image (show Continuous (fun y : Plane => inner ℝ u y) by
    fun_prop)).bddAbove) (mem_image_of_mem _ hx)

theorem support_le_iff {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    (u : Plane) (b : ℝ) :
    support C u ≤ b ↔ ∀ x ∈ C, inner ℝ u x ≤ b :=
  ⟨fun h x hx => (le_support hC hx u).trans h,
    fun h => csSup_le (hne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)⟩

theorem support_translate {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    (u t : Plane) :
    support ((fun x => x + t) '' C) u = support C u + inner ℝ u t := by
  have hi : IsCompact ((fun x => inner ℝ u x) '' C) := hC.image (by fun_prop)
  simpa only [support, image_image, inner_add_right, OrderIso.addRight_apply] using
    ((OrderIso.addRight (inner ℝ u t)).map_csSup' (hne.image _) hi.bddAbove).symm

theorem support_isometry (C : Set Plane) (M : Plane ≃ₗᵢ[ℝ] Plane) (u : Plane) :
    support (M.symm '' C) u = support C (M u) := by
  unfold support
  congr 1
  rw [image_image]
  congr 1
  funext x
  rw [← LinearIsometryEquiv.inner_map_map M u (M.symm x),
    LinearIsometryEquiv.apply_symm_apply]

/-- A nonnegative expansion of a normal gives an upper bound on its support. -/
theorem support_expansion_le {ι : Type*} [Fintype ι] {C : Set Plane}
    (hC : IsCompact C) (hne : C.Nonempty)
    (u : ι → Plane) (κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    support C (∑ i, κ i • u i) ≤ ∑ i, κ i * support C (u i) := by
  apply (support_le_iff hC hne _ _).mpr
  intro x hx
  rw [sum_inner]
  apply sum_le_sum
  intro i _
  rw [real_inner_smul_left]
  exact mul_le_mul_of_nonneg_left (le_support hC hx (u i)) (hκ i)

/-- The expansion bound evaluated at the named support contacts. -/
theorem support_contact_expansion_le {ι : Type*} [Fintype ι] {C : Set Plane}
    (hC : IsCompact C) (hne : C.Nonempty)
    (u P : ι → Plane) (κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hcontact : ∀ i, support C (u i) = inner ℝ (u i) (P i))
    {w : Plane} (hexpand : w = ∑ i, κ i • u i) :
    support C w ≤ ∑ i, κ i * inner ℝ (u i) (P i) := by
  rw [hexpand]
  simpa only [hcontact] using support_expansion_le hC hne u κ hκ

theorem support_row {C : Set Plane} (hC : IsCompact C)
    {u p q : Plane} (hq : q ∈ C) (hp : support C u = inner ℝ u p) :
    0 ≤ inner ℝ u (p - q) := by
  rw [inner_sub_right]
  have h := le_support hC hq u
  rw [hp] at h
  linarith

theorem inner_plane (u v : Plane) :
    inner ℝ u v = u.re * v.re + u.im * v.im := by
  change (v * starRingEnd ℂ u).re = _
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The intersection of two zero-offset and two positive-offset walls. -/
def fourWalls (n₀ n₁ n₂ n₃ : Plane) (Dₐ Dᵦ : ℝ) : Set Plane :=
  {x | inner ℝ n₀ x ≤ 0 ∧ inner ℝ n₁ x ≤ 0 ∧
    inner ℝ n₂ x ≤ Dₐ ∧ inner ℝ n₃ x ≤ Dᵦ}

/-- Translation making the first two support values zero. -/
def cornerTranslation (u v : Plane) (s t : ℝ) : Plane :=
  ⟨(t * u.im - s * v.im) / (u.re * v.im - u.im * v.re),
    (s * v.re - t * u.re) / (u.re * v.im - u.im * v.re)⟩

theorem cornerTranslation_inner (u v : Plane) (s t : ℝ)
    (hdet : u.re * v.im - u.im * v.re ≠ 0) :
    inner ℝ u (cornerTranslation u v s t) = -s ∧
      inner ℝ v (cornerTranslation u v s t) = -t := by
  simp only [inner_plane, cornerTranslation]
  constructor <;>
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff hdet] <;> ring

private theorem translated_support_le {C : Set Plane}
    (hC : IsCompact C) (hne : C.Nonempty) {u t : Plane} {b : ℝ}
    (h : ∀ x ∈ C, inner ℝ u (x + t) ≤ b) :
    support C u + inner ℝ u t ≤ b := by
  obtain ⟨x, hx, he⟩ := support_attained hC hne u
  simpa only [inner_add_right, he] using h x hx

/-- The two positive normal balances make the corner placement optimal for
both remaining walls. This is the manuscript's translation criterion. -/
theorem translation_criterion {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    (n₀ n₁ n₂ n₃ : Plane) (a₀ a₁ b₀ b₁ Dₐ Dᵦ : ℝ)
    (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁)
    (hdet : n₀.re * n₁.im - n₀.im * n₁.re ≠ 0)
    (ha : a₀ • n₀ + a₁ • n₁ + n₂ = 0)
    (hb : b₀ • n₀ + b₁ • n₁ + n₃ = 0) :
    (∃ t : Plane, (fun x => x + t) '' C ⊆ fourWalls n₀ n₁ n₂ n₃ Dₐ Dᵦ) ↔
      a₀ * support C n₀ + a₁ * support C n₁ + support C n₂ ≤ Dₐ ∧
      b₀ * support C n₀ + b₁ * support C n₁ + support C n₃ ≤ Dᵦ := by
  have hbal (t : Plane) :
      a₀ * inner ℝ n₀ t + a₁ * inner ℝ n₁ t + inner ℝ n₂ t = 0 ∧
      b₀ * inner ℝ n₀ t + b₁ * inner ℝ n₁ t + inner ℝ n₃ t = 0 := by
    constructor
    · simpa only [inner_add_left, real_inner_smul_left, inner_zero_left] using
        congrArg (fun z => inner ℝ z t) ha
    · simpa only [inner_add_left, real_inner_smul_left, inner_zero_left] using
        congrArg (fun z => inner ℝ z t) hb
  constructor
  · rintro ⟨t, ht⟩
    have h₀ := translated_support_le hC hne (fun x hx => (ht ⟨x, hx, rfl⟩).1)
    have h₁ := translated_support_le hC hne (fun x hx => (ht ⟨x, hx, rfl⟩).2.1)
    have h₂ := translated_support_le hC hne (fun x hx => (ht ⟨x, hx, rfl⟩).2.2.1)
    have h₃ := translated_support_le hC hne (fun x hx => (ht ⟨x, hx, rfl⟩).2.2.2)
    obtain ⟨ha', hb'⟩ := hbal t
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left h₀ ha₀.le,
        mul_le_mul_of_nonneg_left h₁ ha₁.le]
    · nlinarith [mul_le_mul_of_nonneg_left h₀ hb₀.le,
        mul_le_mul_of_nonneg_left h₁ hb₁.le]
  · rintro ⟨hA, hB⟩
    let t := cornerTranslation n₀ n₁ (support C n₀) (support C n₁)
    obtain ⟨ht₀, ht₁⟩ := cornerTranslation_inner n₀ n₁
      (support C n₀) (support C n₁) hdet
    obtain ⟨ha', hb'⟩ := hbal t
    change inner ℝ n₀ t = _ at ht₀
    change inner ℝ n₁ t = _ at ht₁
    rw [ht₀, ht₁] at ha' hb'
    refine ⟨t, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h₀ := le_support hC hx n₀
    have h₁ := le_support hC hx n₁
    have h₂ := le_support hC hx n₂
    have h₃ := le_support hC hx n₃
    change inner ℝ n₀ (x + t) ≤ 0 ∧ inner ℝ n₁ (x + t) ≤ 0 ∧
      inner ℝ n₂ (x + t) ≤ Dₐ ∧ inner ℝ n₃ (x + t) ≤ Dᵦ
    simp only [inner_add_right, ht₀, ht₁]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Failure of congruent coverage gives one strict escape alternative for
every orthogonal map, including reflections. -/
theorem escape_of_uncovered {C : Set Plane} (hC : IsCompact C) (hne : C.Nonempty)
    (n₀ n₁ n₂ n₃ : Plane) (a₀ a₁ b₀ b₁ Dₐ Dᵦ : ℝ)
    (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁)
    (hdet : n₀.re * n₁.im - n₀.im * n₁.re ≠ 0)
    (ha : a₀ • n₀ + a₁ • n₁ + n₂ = 0)
    (hb : b₀ • n₀ + b₁ • n₁ + n₃ = 0)
    (hmiss : ¬ ∃ g : Plane ≃ᵢ Plane, g '' C ⊆ fourWalls n₀ n₁ n₂ n₃ Dₐ Dᵦ)
    (M : Plane ≃ₗᵢ[ℝ] Plane) :
    Dₐ < a₀ * support C (M n₀) + a₁ * support C (M n₁) + support C (M n₂) ∨
      Dᵦ < b₀ * support C (M n₀) + b₁ * support C (M n₁) + support C (M n₃) := by
  by_contra! h
  have hs :
      a₀ * support (M.symm '' C) n₀ + a₁ * support (M.symm '' C) n₁ +
          support (M.symm '' C) n₂ ≤ Dₐ ∧
      b₀ * support (M.symm '' C) n₀ + b₁ * support (M.symm '' C) n₁ +
          support (M.symm '' C) n₃ ≤ Dᵦ := by
    simpa only [support_isometry] using h
  obtain ⟨t, ht⟩ := (translation_criterion (hC.image M.symm.continuous)
    (hne.image _) n₀ n₁ n₂ n₃ a₀ a₁ b₀ b₁ Dₐ Dᵦ
    ha₀ ha₁ hb₀ hb₁ hdet ha hb).mpr hs
  apply hmiss
  refine ⟨M.symm.toIsometryEquiv.trans (IsometryEquiv.addRight t), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ht ⟨M.symm x, mem_image_of_mem _ hx, rfl⟩

/-- A positive weighted right side forces a positively weighted strict row.
Non-escape rows have right side zero in the application. -/
theorem strict_weighted_rows {κ : Type*} [Fintype κ]
    (μ lhs rhs : κ → ℝ) (hμ : ∀ k, 0 ≤ μ k)
    (hrow : ∀ k, rhs k ≤ lhs k)
    (hstrict : ∀ k, 0 < rhs k → rhs k < lhs k)
    (hB : 0 < ∑ k, μ k * rhs k) :
    (∑ k, μ k * rhs k) < ∑ k, μ k * lhs k := by
  classical
  obtain ⟨k, _, hk⟩ := exists_lt_of_sum_lt
    (show (∑ _ : κ, (0 : ℝ)) < ∑ k, μ k * rhs k by simpa using hB)
  have hrk : 0 < rhs k := pos_of_mul_pos_right hk (hμ k)
  have hmk : 0 < μ k := pos_of_mul_pos_left hk hrk.le
  exact sum_lt_sum (fun k _ => mul_le_mul_of_nonneg_left (hrow k) (hμ k))
    ⟨k, mem_univ k, mul_lt_mul_of_pos_left (hstrict k hrk) hmk⟩

/-- Aggregating vector coefficients agrees with aggregating the linear rows. -/
theorem weighted_rows_identity {κ ι : Type*} [Fintype κ] [Fintype ι]
    (μ : κ → ℝ) (c : κ → ι → Plane) (P : ι → Plane) :
    (∑ l, inner ℝ (∑ k, μ k • c k l) (P l)) =
      ∑ k, μ k * ∑ l, inner ℝ (c k l) (P l) := by
  simp only [sum_inner, real_inner_smul_left, mul_sum]
  exact sum_comm

/-- The leaf threshold `B ≥ 1` gives a strict contact-functional bound. -/
theorem weighted_rows_gt_one {κ ι : Type*} [Fintype κ] [Fintype ι]
    (μ rhs : κ → ℝ) (c : κ → ι → Plane) (P : ι → Plane)
    (hμ : ∀ k, 0 ≤ μ k)
    (hrow : ∀ k, rhs k ≤ ∑ l, inner ℝ (c k l) (P l))
    (hstrict : ∀ k, 0 < rhs k → rhs k < ∑ l, inner ℝ (c k l) (P l))
    (hB : 1 ≤ ∑ k, μ k * rhs k) :
    1 < ∑ l, inner ℝ (∑ k, μ k • c k l) (P l) := by
  rw [weighted_rows_identity]
  exact hB.trans_lt (strict_weighted_rows μ _ rhs hμ hrow hstrict
    (lt_of_lt_of_le zero_lt_one hB))

end MoserWorm.UpperBound

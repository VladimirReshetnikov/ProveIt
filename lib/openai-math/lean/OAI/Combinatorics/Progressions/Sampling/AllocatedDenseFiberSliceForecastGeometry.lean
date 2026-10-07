/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Lattices.AffineIntervalNormalizedBounds
import OAI.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw

namespace OAI

section

namespace Erdos3.ResidueBoxSlice

theorem denseCoordinate_geometry {X : Type*} {N : X → ℕ} {q : ℕ}
    (S : ResidueBoxSlice N q) (i : X) {cost : ℝ}
    (hq : 0 < q) (hN : 0 < N i)
    (hdense : Real.exp (-cost) * (N i : ℝ) ≤ S.length i)
    (hfloor : 2 ≤ Real.exp (-cost) * (N i : ℝ)) :
    2 ≤ S.length i ∧
      0 ≤ (S.start i : ℝ) / N i ∧
      Real.exp (-cost) / 2 ≤ (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i ∧
      (S.start i : ℝ) / N i +
        (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i < 1 ∧
      (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i ≤ 1 ∧
      (q : ℝ) ≤ 2 * Real.exp cost := by
  have hlenR : (2 : ℝ) ≤ S.length i := hfloor.trans hdense
  have hlen : 2 ≤ S.length i := by exact_mod_cast hlenR
  have hinside (t : Fin (S.length i)) :
      0 ≤ (S.start i : ℤ) + (q : ℤ) * (t.val : ℤ) ∧
      (S.start i : ℤ) + (q : ℤ) * (t.val : ℤ) < N i := by
    constructor
    · positivity
    · exact_mod_cast S.inside i t.val t.isLt
  have hbounds := affineInterval_normalized_bounds hN hlen hq hinside
  have hNR : (0 : ℝ) < N i := by exact_mod_cast hN
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsub : ((S.length i - 1 : ℕ) : ℝ) = (S.length i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hhalf : Real.exp (-cost) * (N i : ℝ) / 2 ≤
      ((S.length i - 1 : ℕ) : ℝ) := by
    rw [hsub]
    linarith
  have hscaled : (q : ℝ) * Real.exp (-cost) / 2 ≤
      (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i := by
    apply (le_div_iff₀ hNR).mpr
    have h := mul_le_mul_of_nonneg_left hhalf hq0
    nlinarith
  have hwidth : Real.exp (-cost) / 2 ≤
      (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i := by
    calc
      Real.exp (-cost) / 2 ≤ (q : ℝ) * Real.exp (-cost) / 2 := by
        nlinarith [Real.exp_pos (-cost)]
      _ ≤ _ := hscaled
  have hprod : (q : ℝ) * Real.exp (-cost) ≤ 2 := by
    linarith [hscaled.trans hbounds.2.2.2]
  have hcancel : Real.exp (-cost) * Real.exp cost = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hstep : (q : ℝ) ≤ 2 * Real.exp cost := by
    calc
      (q : ℝ) = ((q : ℝ) * Real.exp (-cost)) * Real.exp cost := by
        rw [mul_assoc, hcancel, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod (Real.exp_pos cost).le
  exact ⟨hlen, by simpa only [Int.cast_natCast] using hbounds.1, hwidth,
    by simpa only [Int.cast_natCast] using hbounds.2.2.1, hbounds.2.2.2, hstep⟩

theorem fiberParameterStride_le {X : Type*} {keep : X → Prop}
    [DecidablePred keep] {q : ℕ} (i : X) :
    fiberParameterStride (keep := keep) (q := q) i ≤ q := by
  unfold fiberParameterStride
  split <;> omega

theorem fiberParameter_dense_of_keep {X : Type*} {keep : X → Prop}
    [DecidablePred keep] {N : X → ℕ} {q : ℕ}
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    {density : ℝ} (hdense : ∀ k, density * (N k.val : ℝ) ≤ S.length k)
    (hq : 0 < q) (i : X) (hi : keep i) :
    density * (N i : ℝ) ≤ S.fiberParameterLength i ∧
      0 < fiberParameterStride (keep := keep) (q := q) i := by
  constructor
  · rw [fiberParameterLength_of_keep S i hi]
    exact hdense ⟨i, hi⟩
  · simpa only [fiberParameterStride, ite_eq_left hi] using hq

theorem fiberParameter_regular_of_threshold {X Y : Type*} {keep : X → Prop}
    [DecidablePred keep] {N : X → ℕ} {q H : ℕ}
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    {density : ℝ} (hdense : ∀ k, density * (N k.val : ℝ) ≤ S.length k)
    (hq : 0 < q) (hkeep : ∀ i, H ≤ N i → keep i) (index : Y → X) :
    (∃ y, N (index y) < H) ∨
      ((∀ y, density * (N (index y) : ℝ) ≤ S.fiberParameterLength (index y)) ∧
        ∀ y, 0 < fiberParameterStride (keep := keep) (q := q) (index y)) := by
  classical
  by_cases hsmall : ∃ y, N (index y) < H
  · exact Or.inl hsmall
  · right
    have hret (y : Y) : keep (index y) :=
      hkeep (index y) (Nat.le_of_not_gt fun h => hsmall ⟨y, h⟩)
    exact ⟨fun y => (S.fiberParameter_dense_of_keep hdense hq (index y) (hret y)).1,
      fun y => (S.fiberParameter_dense_of_keep hdense hq (index y) (hret y)).2⟩

theorem fiberParameter_dense_geometry {X : Type*} {keep : X → Prop}
    [DecidablePred keep] {N : X → ℕ} {q : ℕ}
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ) (i : X) (hi : keep i) {cost : ℝ}
    (hq : 0 < q) (hN : 0 < N i)
    (hdense : Real.exp (-cost) * (N i : ℝ) ≤ S.length ⟨i, hi⟩)
    (hfloor : 2 ≤ Real.exp (-cost) * (N i : ℝ)) :
    let lower := (S.fiberParameterStart fixed i : ℝ) / N i
    let width := (fiberParameterStride (keep := keep) (q := q) i : ℝ) *
      ((S.fiberParameterLength i - 1 : ℕ) : ℝ) / N i
    2 ≤ S.fiberParameterLength i ∧ 0 ≤ lower ∧
      Real.exp (-cost) / 2 ≤ width ∧ lower + width < 1 ∧
      |lower| + |width| ≤ 1 := by
  dsimp only
  simp only [fiberParameterLength, fiberParameterStart, fiberParameterStride,
    dite_eq_left hi, ite_eq_left hi, Int.cast_natCast]
  have h := S.denseCoordinate_geometry ⟨i, hi⟩ hq hN hdense hfloor
  have hw : 0 ≤ (q : ℝ) * ((S.length ⟨i, hi⟩ - 1 : ℕ) : ℝ) / N i :=
    (by positivity : (0 : ℝ) ≤ Real.exp (-cost) / 2).trans h.2.2.1
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  rw [abs_of_nonneg h.2.1, abs_of_nonneg hw]
  exact h.2.2.2.1.le

end Erdos3.ResidueBoxSlice

end

end OAI

import GowersSzemeredi.Proofs13RowLinearization

/-!
# Selecting the base row in Lemma 13.7

Summing the number of selected upper endpoints over the base height counts
exactly the selected vertical edges. A single averaging step can therefore
preserve both quantitative bounds of Stage 13.6. The selected edge count also
bounds the number of original-domain points on the chosen base row.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

/-- The upper-endpoint count at a fixed base height is the sum of its edge
counts over all available displacements. -/
theorem stage137UpperEndpoints_card {N : Nat} (R I : Finset (ZMod N))
    (Y : ZMod N → Finset (Pair N)) (y : ZMod N) :
    (stage137UpperEndpoints R I Y y).card =
      ∑ h ∈ I, (R.filter fun x ↦ (x, y) ∈ Y h).card := by
  classical
  rw [← translatedRow_total R I (stage137UpperEndpoints R I Y y) y
    (Finset.filter_subset _ _)]
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  ext x
  simp only [translatedRow, Finset.mem_filter]
  rw [mem_stage137UpperEndpoints]
  simp only [hh, true_and, and_self_left]

/-- Summing the upper-endpoint count over base heights counts each selected
vertical edge exactly once. -/
theorem stage137UpperEndpoints_sum {N : Nat} [NeZero N]
    (R I : Finset (ZMod N)) (Y : ZMod N → Finset (Pair N)) :
    ∑ y : ZMod N, (stage137UpperEndpoints R I Y y).card =
      ∑ h ∈ I, ((Y h).filter fun z ↦ z.1 ∈ R).card := by
  classical
  simp_rw [stage137UpperEndpoints_card]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  let E := (Y h).filter fun z ↦ z.1 ∈ R
  have hrow : ∀ y, (R.filter fun x ↦ (x, y) ∈ Y h) = translatedRow R E 0 y := by
    intro y
    ext x
    simp [translatedRow, E]
    tauto
  simp_rw [hrow]
  rw [translatedRow_sum R E 0 Finset.univ
    (fun z hz ↦ (Finset.mem_filter.mp hz).2)]
  simp [E]

/-- The finite averaging step for one arbitrary real lower bound. -/
theorem exists_stage137_base_row {N : Nat} [NeZero N]
    (R I : Finset (ZMod N)) (Y : ZMod N → Finset (Pair N)) {b : Real}
    (hb : b * N ≤ ∑ h ∈ I, (((Y h).filter fun z ↦ z.1 ∈ R).card : Real)) :
    ∃ y : ZMod N, b ≤ (stage137UpperEndpoints R I Y y).card := by
  classical
  have hsum : (∑ y : ZMod N, b) ≤
      ∑ y : ZMod N, ((stage137UpperEndpoints R I Y y).card : Real) := by
    rw [← Nat.cast_sum, stage137UpperEndpoints_sum]
    simpa [mul_comm] using hb
  obtain ⟨y, _, hy⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨y, hy⟩

/-- Both Stage 13.6 lower bounds concern the same mass, so select a row for
 their maximum. Separate averaging choices would not suffice. -/
theorem exists_stage137_base_row_two_bounds {N : Nat} [NeZero N]
    (R I : Finset (ZMod N)) (Y : ZMod N → Finset (Pair N)) {b₁ b₂ : Real}
    (h₁ : b₁ * N ≤ ∑ h ∈ I, (((Y h).filter fun z ↦ z.1 ∈ R).card : Real))
    (h₂ : b₂ * N ≤ ∑ h ∈ I, (((Y h).filter fun z ↦ z.1 ∈ R).card : Real)) :
    ∃ y : ZMod N,
      b₁ ≤ (stage137UpperEndpoints R I Y y).card ∧
      b₂ ≤ (stage137UpperEndpoints R I Y y).card := by
  obtain ⟨y, hy⟩ := exists_stage137_base_row R I Y
    (b := max b₁ b₂) (by
      rcases le_total b₁ b₂ with h | h
      · simpa only [max_eq_right h] using h₂
      · simpa only [max_eq_left h] using h₁)
  exact ⟨y, (le_max_left _ _).trans hy, (le_max_right _ _).trans hy⟩

/-- There are at most `|I|` selected edges above each original-domain point
of the base row. -/
theorem stage137UpperEndpoints_card_le_base {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (R I : Finset (ZMod N))
    (Y : ZMod N → Finset (Pair N)) (y : ZMod N)
    (hY : ∀ h ∈ I, Y h ⊆ verticalEdgeDomain A h) :
    (stage137UpperEndpoints R I Y y).card ≤
      (R.filter fun x ↦ (x, y) ∈ A).card * I.card := by
  rw [stage137UpperEndpoints_card]
  calc
    _ ≤ ∑ _h ∈ I, (R.filter fun x ↦ (x, y) ∈ A).card := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxR, hxY⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hxR, (Finset.mem_filter.mp (hY h hh hxY)).2.1⟩
    _ = _ := by simp [mul_comm]

/-- The row selected with relative edge density `delta` has original-domain
 density at least `delta`, provided the displacement set is nonempty. -/
theorem stage137_base_row_density {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (R I : Finset (ZMod N))
    (Y : ZMod N → Finset (Pair N)) (y : ZMod N) (hI : I.Nonempty)
    (hY : ∀ h ∈ I, Y h ⊆ verticalEdgeDomain A h) {δ : Real}
    (hdense : δ * R.card * I.card ≤ (stage137UpperEndpoints R I Y y).card) :
    δ * R.card ≤ (R.filter fun x ↦ (x, y) ∈ A).card := by
  have hbound := stage137UpperEndpoints_card_le_base A R I Y y hY
  have hboundR : ((stage137UpperEndpoints R I Y y).card : Real) ≤
      (R.filter fun x ↦ (x, y) ∈ A).card * (I.card : Real) := by exact_mod_cast hbound
  have hi : (0 : Real) < I.card := by exact_mod_cast hI.card_pos
  exact le_of_mul_le_mul_right (hdense.trans hboundR) hi

/-- Apply the single-row averaging step to the complete Stage 13.6 data. -/
theorem stage136_exists_base_row {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (hF : IsStage136Data S D E F) :
    ∃ y : ZMod N,
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * F.R.length *
        (criticalHeights S D E).card ≤
        (stage137UpperEndpoints F.R.carrier (criticalHeights S D E) F.Y y).card ∧
      (2 : Real) ^ (-(48 : Int)) * S.alpha ^ 256 * E.Q.length * F.R.length ≤
        (stage137UpperEndpoints F.R.carrier (criticalHeights S D E) F.Y y).card := by
  obtain ⟨_, _, _, _, _, h₁, h₂⟩ := hF
  apply exists_stage137_base_row_two_bounds
  · simpa only [stage136RestrictedEdges, Nat.cast_sum, mul_assoc, mul_left_comm, mul_comm] using h₁
  · simpa only [stage136RestrictedEdges, Nat.cast_sum] using h₂

end LeanProofs.GowersSzemeredi

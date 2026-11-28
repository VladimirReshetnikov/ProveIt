import GRHArticle.ClassGroups.ReducedFormsReadback
import GRHArticle.ClassGroups.SevenReducedCountsSmall
import GRHArticle.ClassGroups.SevenReducedCountsLarge
import Mathlib.Tactic.NormNum.Prime

/-!
# The reduced-form counts for the forty recorded orders

These certificates verify the arithmetic data and count primitive reduced
forms. They do not assert which exponent the groups of order forty-nine
have, or enumerate discriminants outside the displayed list.
-/

namespace GRHArticle.ClassGroups

/-- One row records absolute order and field discriminants, the conductor,
and the number of primitive reduced forms. -/
structure SevenReducedOrderRow where
  orderDisc : ℕ
  fieldDisc : ℕ
  conductor : ℕ
  formCount : ℕ
  deriving DecidableEq, Repr

/-- The forty source rows of the article's exponent-seven table. -/
def sevenReducedOrderRows : List SevenReducedOrderRow :=

  [⟨71, 71, 1, 7⟩, ⟨151, 151, 1, 7⟩, ⟨223, 223, 1, 7⟩,
   ⟨251, 251, 1, 7⟩, ⟨284, 71, 2, 7⟩, ⟨343, 7, 7, 7⟩,
   ⟨463, 463, 1, 7⟩, ⟨467, 467, 1, 7⟩, ⟨487, 487, 1, 7⟩,
   ⟨587, 587, 1, 7⟩, ⟨604, 151, 2, 7⟩, ⟨811, 811, 1, 7⟩,
   ⟨827, 827, 1, 7⟩, ⟨859, 859, 1, 7⟩, ⟨892, 223, 2, 7⟩,
   ⟨1163, 1163, 1, 7⟩, ⟨1171, 1171, 1, 7⟩, ⟨1372, 7, 14, 7⟩,
   ⟨1483, 1483, 1, 7⟩, ⟨1523, 1523, 1, 7⟩, ⟨1627, 1627, 1, 7⟩,
   ⟨1787, 1787, 1, 7⟩, ⟨1852, 463, 2, 7⟩, ⟨1948, 487, 2, 7⟩,
   ⟨1987, 1987, 1, 7⟩, ⟨2011, 2011, 1, 7⟩, ⟨2083, 2083, 1, 7⟩,
   ⟨2179, 2179, 1, 7⟩, ⟨2251, 2251, 1, 7⟩, ⟨2467, 2467, 1, 7⟩,
   ⟨2707, 2707, 1, 7⟩, ⟨3019, 3019, 1, 7⟩, ⟨3067, 3067, 1, 7⟩,
   ⟨3187, 3187, 1, 7⟩, ⟨3907, 3907, 1, 7⟩, ⟨4603, 4603, 1, 7⟩,
   ⟨5107, 5107, 1, 7⟩, ⟨5923, 5923, 1, 7⟩, ⟨63499, 63499, 1, 49⟩,
   ⟨118843, 118843, 1, 49⟩]

private theorem sevenReducedOrderRows_discriminant_cases :
    ∀ r ∈ sevenReducedOrderRows, (r.orderDisc ∈ sevenReducedCountDiscriminants ∧ r.formCount = 7) ∨
      (r.orderDisc = 63499 ∧ r.formCount = 49) ∨ (r.orderDisc = 118843 ∧ r.formCount = 49) := by
  decide +kernel

private theorem sevenReducedOrderRows_fieldDisc_prime (r : SevenReducedOrderRow)
    (hr : r ∈ sevenReducedOrderRows) : r.fieldDisc.Prime := by
  simp only [sevenReducedOrderRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with
    h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h
  all_goals
    subst r
    norm_num [SevenReducedOrderRow.fieldDisc]

private theorem sevenReducedOrderRows_numeric :
    ∀ r ∈ sevenReducedOrderRows, r.fieldDisc % 4 = 3 ∧ 0 < r.conductor ∧
      r.orderDisc = r.fieldDisc*r.conductor^2 := by
  decide +kernel

/-- Each row has a prime field discriminant of the required congruence type
and the exact conductor-square relation. -/
theorem sevenReducedOrderRows_arithmetic :
    ∀ r ∈ sevenReducedOrderRows, r.fieldDisc.Prime ∧ r.fieldDisc % 4 = 3 ∧ 0 < r.conductor ∧
      r.orderDisc = r.fieldDisc*r.conductor^2 :=
  fun r hr ↦ ⟨sevenReducedOrderRows_fieldDisc_prime r hr, sevenReducedOrderRows_numeric r hr⟩

/-- There are forty distinct order discriminants, with seven nontrivial conductors. -/
theorem sevenReducedOrderRows_cardinalities :
    (sevenReducedOrderRows.map SevenReducedOrderRow.orderDisc).Nodup ∧
    sevenReducedOrderRows.length = 40 ∧
    (sevenReducedOrderRows.filter (fun r ↦ r.conductor == 1)).length = 33 ∧
    (sevenReducedOrderRows.filter (fun r ↦ r.conductor > 1)).length = 7 := by
  decide +kernel

/-- The table contains thirty-eight rows with seven forms and two rows
with forty-nine forms. -/
theorem sevenReducedOrderRows_count_distribution :
    (sevenReducedOrderRows.filter (fun r ↦ r.formCount == 7)).length = 38 ∧
    (sevenReducedOrderRows.filter (fun r ↦ r.formCount == 49)).length = 2 := by
  decide +kernel

/-- The computed number of primitive reduced forms agrees with every row. -/
theorem sevenReducedOrderRows_reducedFormCount (r : SevenReducedOrderRow) (hr : r ∈ sevenReducedOrderRows) :
    reducedQuadraticFormCount r.orderDisc = r.formCount := by
  rcases sevenReducedOrderRows_discriminant_cases r hr with ⟨h, hc⟩ | ⟨hd,hc⟩ | ⟨hd,hc⟩
  · rw [hc]
    exact sevenReducedCountDiscriminants_count r.orderDisc h
  · rw [hd,hc]
    exact reducedQuadraticFormCount_63499
  · rw [hd,hc]
    exact reducedQuadraticFormCount_118843

/-- The same count holds in the singular-moduli reduced-form model. -/
theorem sevenReducedOrderRows_singularModuli_count (r : SevenReducedOrderRow)
    (hr : r ∈ sevenReducedOrderRows) (D : ℕ+) (hD : (D:ℕ) = r.orderDisc) :
    (GRHArticle.SingularModuli.reducedForms D).card = r.formCount := by
  rw [← reducedQuadraticFormCount_eq_reducedForms_card D, hD]
  exact sevenReducedOrderRows_reducedFormCount r hr

/-- Across the forty rows there are 364 primitive reduced forms, counted
once per order in which they occur. -/
theorem sevenReducedOrderRows_total_reducedForms :
    (sevenReducedOrderRows.map (fun r ↦ reducedQuadraticFormCount r.orderDisc)).sum = 364 := by
  have h : sevenReducedOrderRows.map (fun r ↦ reducedQuadraticFormCount r.orderDisc) =
      sevenReducedOrderRows.map SevenReducedOrderRow.formCount :=
    List.map_congr_left sevenReducedOrderRows_reducedFormCount
  rw [h]
  decide +kernel

end GRHArticle.ClassGroups

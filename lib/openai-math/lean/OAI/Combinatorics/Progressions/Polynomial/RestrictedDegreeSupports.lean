import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable (I : Type*) [Fintype I] [DecidableEq I]

def lowDegreeCoordinateSets (b : ℕ) : Finset (Finset I) :=
  (Finset.range (b + 1)).biUnion (fun j => Finset.powersetCard j Finset.univ)

theorem mem_lowDegreeCoordinateSets (b : ℕ) (S : Finset I) :
    S ∈ lowDegreeCoordinateSets I b ↔ S.card ≤ b := by
  simp only [lowDegreeCoordinateSets, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨j, hj, hcard⟩
    omega
  · intro h
    exact ⟨S.card, by omega, rfl⟩

theorem lowDegreeCoordinateSets_card (b : ℕ) :
    (lowDegreeCoordinateSets I b).card = ∑ j ∈ Finset.range (b + 1), (Fintype.card I).choose j := by
  rw [lowDegreeCoordinateSets, Finset.card_biUnion]
  · simp only [Finset.card_powersetCard, Finset.card_univ]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro S hSi hSj
    exact hij ((Finset.mem_powersetCard.mp hSi).2.symm.trans (Finset.mem_powersetCard.mp hSj).2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

def restrictedDegreeSupports (J : Finset ι) (b : ℕ) : Finset (Finset ι) :=
  J.powerset.filter (fun S => S.card ≤ b)

def degreeTailSupports (J : Finset ι) (r b : ℕ) : Finset (Finset ι) :=
  J.powerset.filter (fun S => r < S.card ∧ S.card ≤ b)

omit [DecidableEq ι] in
theorem mem_restrictedDegreeSupports (J S : Finset ι) (b : ℕ) :
    S ∈ restrictedDegreeSupports J b ↔ S ⊆ J ∧ S.card ≤ b := by
  simp only [restrictedDegreeSupports, Finset.mem_filter, Finset.mem_powerset]

omit [DecidableEq ι] in
theorem mem_degreeTailSupports (J S : Finset ι) (r b : ℕ) :
    S ∈ degreeTailSupports J r b ↔ S ⊆ J ∧ r < S.card ∧ S.card ≤ b := by
  simp only [degreeTailSupports, Finset.mem_filter, Finset.mem_powerset]

theorem restrictedDegreeSupports_eq_biUnion (J : Finset ι) (b : ℕ) :
    restrictedDegreeSupports J b = (Finset.range (b + 1)).biUnion (fun k => J.powersetCard k) := by
  ext S
  simp only [mem_restrictedDegreeSupports, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
  constructor
  · rintro ⟨hS, hb⟩
    exact ⟨S.card, by omega, hS, rfl⟩
  · rintro ⟨k, hk, hS, he⟩
    exact ⟨hS, by omega⟩

theorem sum_restrictedDegreeSupports (J : Finset ι) (b : ℕ) (F : Finset ι → ℝ) :
    (∑ S ∈ restrictedDegreeSupports J b, F S) =
      ∑ k ∈ Finset.range (b + 1), ∑ S ∈ J.powersetCard k, F S := by
  rw [restrictedDegreeSupports_eq_biUnion, Finset.sum_biUnion]
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro S hSi hSj
  exact hij ((Finset.mem_powersetCard.mp hSi).2.symm.trans (Finset.mem_powersetCard.mp hSj).2)

theorem sum_restrictedDegreeSupports_zero (J : Finset ι) (r : ℕ) (F : Finset ι → ℝ) :
    (∑ S ∈ restrictedDegreeSupports J r, F S) =
      F ∅ + ∑ k ∈ Finset.range r, ∑ S ∈ J.powersetCard (k + 1), F S := by
  rw [sum_restrictedDegreeSupports, Finset.sum_range_succ']
  simp only [Finset.powersetCard_zero, Finset.sum_singleton, add_comm]

theorem sum_restrictedDegreeSupports_split (J : Finset ι) {r b : ℕ} (hrb : r ≤ b)
    (F : Finset ι → ℝ) :
    (∑ S ∈ restrictedDegreeSupports J b, F S) =
      (∑ S ∈ restrictedDegreeSupports J r, F S) + (∑ S ∈ degreeTailSupports J r b, F S) := by
  have he : restrictedDegreeSupports J b = restrictedDegreeSupports J r ∪ degreeTailSupports J r b := by
    ext S
    simp only [Finset.mem_union, mem_restrictedDegreeSupports, mem_degreeTailSupports]
    constructor
    · rintro ⟨hS, hb⟩
      by_cases hr : S.card ≤ r
      · exact Or.inl ⟨hS, hr⟩
      · exact Or.inr ⟨hS, by omega, hb⟩
    · rintro (⟨hS, hr⟩ | ⟨hS, _, hb⟩)
      · exact ⟨hS, hr.trans hrb⟩
      · exact ⟨hS, hb⟩
  rw [he]
  apply Finset.sum_union
  apply Finset.disjoint_left.mpr
  intro S hlow htail
  have hl := (mem_restrictedDegreeSupports J S r).mp hlow
  have ht := (mem_degreeTailSupports J S r b).mp htail
  omega

end Erdos3

end

end OAI

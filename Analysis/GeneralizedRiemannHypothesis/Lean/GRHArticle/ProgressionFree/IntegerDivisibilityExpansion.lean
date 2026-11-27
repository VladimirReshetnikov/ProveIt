import GRHArticle.ProgressionFree.IntegerPrefixTransfer
import GRHArticle.ProgressionFree.Density

/-!
# Finite expansions in divisibility indicators

Boolean operations on divisibility tests yield finite linear combinations
of divisibility indicators. Products of indicators use least common
multiples.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical BigOperators

private noncomputable def divisibilityTerm (t : ℕ × ℝ) (n : ℕ) : ℝ :=
  if t.1 ∣ n then t.2 else 0

/-- A set of positive integers whose membership indicator is a finite linear
combination of divisibility indicators with positive moduli. -/
def IntegerDivisibilityExpansion (A : Set ℕ) : Prop :=
  ∃ terms : List (ℕ × ℝ), (∀ t ∈ terms, 0 < t.1) ∧
    ∀ n : ℕ, 0 < n →
      (if n ∈ A then (1 : ℝ) else 0) = (terms.map (divisibilityTerm · n)).sum

namespace IntegerDivisibilityExpansion

/-- Divisibility by one fixed modulus is itself an expansion term. -/
theorem dvd {d : ℕ} (hd : 0 < d) : IntegerDivisibilityExpansion {n | d ∣ n} :=
  ⟨[(d,1)], by simpa, fun n _ ↦ by simp [divisibilityTerm]⟩

/-- The expansion depends only on the positive members of the set. -/
theorem congr {A B : Set ℕ} (hA : IntegerDivisibilityExpansion A)
    (h : ∀ n : ℕ, 0 < n → (n ∈ A ↔ n ∈ B)) : IntegerDivisibilityExpansion B := by
  obtain ⟨L, hp, he⟩ := hA
  refine ⟨L, hp, fun n hn ↦ ?_⟩
  rw [← he n hn]
  exact if_congr (h n hn).symm rfl rfl

private theorem sum_map_term_neg (L : List (ℕ × ℝ)) (n : ℕ) :
    ((L.map fun a ↦ (a.1,-a.2)).map (divisibilityTerm · n)).sum =
      -(L.map (divisibilityTerm · n)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    by_cases h : a.1 ∣ n <;> simp [divisibilityTerm, h, add_comm]

/-- Complement subtracts the indicator from the constant term. -/
theorem compl {A : Set ℕ} (hA : IntegerDivisibilityExpansion A) :
    IntegerDivisibilityExpansion Aᶜ := by
  obtain ⟨L, hp, he⟩ := hA
  refine ⟨(1,1) :: L.map (fun a ↦ (a.1,-a.2)), ?_, ?_⟩
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · decide
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
      exact hp a ha
  · intro n hn
    rw [List.map_cons, List.sum_cons, sum_map_term_neg,
      show divisibilityTerm (1,1) n = 1 by simp [divisibilityTerm], ← he n hn]
    by_cases h : n ∈ A <;> simp [h]

private def termMul (a b : ℕ × ℝ) : ℕ × ℝ :=
  (a.1.lcm b.1, a.2*b.2)

private theorem divisibilityTerm_mul (a b : ℕ × ℝ) (n : ℕ) :
    divisibilityTerm (termMul a b) n = divisibilityTerm a n * divisibilityTerm b n := by
  by_cases ha : a.1 ∣ n <;> by_cases hb : b.1 ∣ n <;>
    simp [divisibilityTerm, termMul, Nat.lcm_dvd_iff, ha, hb]

private theorem sum_map_term_row (a : ℕ × ℝ) (R : List (ℕ × ℝ)) (n : ℕ) :
    ((R.map (termMul a)).map (divisibilityTerm · n)).sum =
      divisibilityTerm a n * (R.map (divisibilityTerm · n)).sum := by
  induction R with
  | nil => simp
  | cons b R ih =>
    simp only [List.map_cons, List.sum_cons, divisibilityTerm_mul, ih, mul_add]

private theorem sum_map_term_product (L R : List (ℕ × ℝ)) (n : ℕ) :
    ((L.flatMap fun a ↦ R.map (termMul a)).map (divisibilityTerm · n)).sum =
      (L.map (divisibilityTerm · n)).sum * (R.map (divisibilityTerm · n)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_map_term_row, ih, add_mul]

/-- Intersections multiply indicators and combine moduli by least common multiple. -/
theorem inter {A B : Set ℕ} (hA : IntegerDivisibilityExpansion A)
    (hB : IntegerDivisibilityExpansion B) : IntegerDivisibilityExpansion (A ∩ B) := by
  obtain ⟨L, hp, he⟩ := hA
  obtain ⟨R, hq, hf⟩ := hB
  refine ⟨L.flatMap (fun a ↦ R.map (termMul a)), ?_, ?_⟩
  · intro t ht
    obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
    exact Nat.lcm_pos (hp a ha) (hq b hb)
  · intro n hn
    rw [sum_map_term_product, ← he n hn, ← hf n hn]
    by_cases ha : n ∈ A <;> by_cases hb : n ∈ B <;> simp [ha, hb]

theorem union {A B : Set ℕ} (hA : IntegerDivisibilityExpansion A)
    (hB : IntegerDivisibilityExpansion B) : IntegerDivisibilityExpansion (A ∪ B) :=
  ((hA.compl.inter hB.compl).compl).congr (fun n _ ↦ by
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union]; tauto)

theorem empty : IntegerDivisibilityExpansion (∅ : Set ℕ) :=
  ⟨[], by simp, fun n _ ↦ by simp⟩

theorem exists_finset {ι : Type*} (I : Finset ι) (A : ι → Set ℕ)
    (hA : ∀ i ∈ I, IntegerDivisibilityExpansion (A i)) :
    IntegerDivisibilityExpansion {n | ∃ i ∈ I, n ∈ A i} := by
  induction I using Finset.induction_on with
  | empty => exact empty.congr (fun _ _ ↦ by simp)
  | insert i I hi ih =>
    have h := (hA i (mem_insert_self _ _)).union (ih (fun j hj ↦ hA j (mem_insert_of_mem hj)))
    apply h.congr
    intro n _
    simp only [Set.mem_union, Set.mem_setOf_eq, mem_insert]
    constructor
    · rintro (hni | ⟨j,hj,hnj⟩)
      · exact ⟨i, Or.inl rfl, hni⟩
      · exact ⟨j, Or.inr hj, hnj⟩
    · rintro ⟨j, rfl | hj, hnj⟩
      · exact Or.inl hnj
      · exact Or.inr ⟨j, hj, hnj⟩

theorem forall_finset {ι : Type*} (I : Finset ι) (A : ι → Set ℕ)
    (hA : ∀ i ∈ I, IntegerDivisibilityExpansion (A i)) :
    IntegerDivisibilityExpansion {n | ∀ i ∈ I, n ∈ A i} :=
  ((exists_finset I (fun i ↦ (A i)ᶜ) (fun i hi ↦ (hA i hi).compl)).compl).congr
    (fun n _ ↦ by simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_and, not_not])

/-- A joint exact valuation test is a finite Boolean combination of two
divisibility tests for each prime. -/
theorem valuationCylinder (S : Finset ℕ) (e : ℕ → ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    IntegerDivisibilityExpansion (GRHArticle.ProgressionFree.valuationCylinder S e) := by
  refine (forall_finset S (fun p ↦ {n | p^(e p) ∣ n} ∩ {n | p^(e p+1) ∣ n}ᶜ)
    (fun p hp ↦ (dvd (pow_pos (hS p hp).pos _)).inter (dvd (pow_pos (hS p hp).pos _)).compl)).congr ?_
  intro n hn
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff,
    GRHArticle.ProgressionFree.valuationCylinder]
  have hf (p : ℕ) (hp : p ∈ S) :
      (p ^ (e p) ∣ n ∧ ¬ p ^ (e p+1) ∣ n) ↔ n.factorization p = e p := by
    rw [(hS p hp).pow_dvd_iff_le_factorization hn.ne',
      (hS p hp).pow_dvd_iff_le_factorization hn.ne']
    omega
  exact ⟨fun h ↦ ⟨hn.ne', fun p hp ↦ (hf p hp).mp (h p hp)⟩,
    fun h p hp ↦ (hf p hp).mpr (h.2 p hp)⟩

private theorem countUpTo_inter_as_sum (A B : Set ℕ) (N : ℕ) :
    (countUpTo (A ∩ B) N : ℝ) =
      ∑ n ∈ integerPrefixSlice B N, (if n ∈ A then 1 else 0) := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  change ((integerPrefixSlice (A ∩ B) N).card : ℝ) = _
  have h : integerPrefixSlice (A ∩ B) N =
      (integerPrefixSlice B N).filter (· ∈ A) := by
    ext n
    simp only [integerPrefixSlice, mem_filter, Set.mem_inter_iff]
    tauto
  rw [h]

private theorem sum_divisibilityTerm (t : ℕ × ℝ) (B : Set ℕ) (N : ℕ) :
    (∑ n ∈ integerPrefixSlice B N, divisibilityTerm t n) =
      t.2 * (countUpTo ({n | t.1 ∣ n} ∩ B) N : ℝ) := by
  rw [countUpTo_inter_as_sum]
  simp_rw [Set.mem_setOf_eq, divisibilityTerm, mul_sum, mul_ite, mul_one, mul_zero]

private theorem sum_divisibilityTerms (L : List (ℕ × ℝ)) (B : Set ℕ) (N : ℕ) :
    (∑ n ∈ integerPrefixSlice B N, (L.map (divisibilityTerm · n)).sum) =
      (L.map fun t ↦ t.2 * (countUpTo ({n | t.1 ∣ n} ∩ B) N : ℝ)).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons, sum_add_distrib, sum_divisibilityTerm, ih]

/-- The same coefficients expand the density in every additional intersection,
so the identity holds before any cutoff limit. -/
theorem exists_densityUpTo_inter_eq {A : Set ℕ} (hA : IntegerDivisibilityExpansion A) :
    ∃ L : List (ℕ × ℝ), (∀ t ∈ L, 0 < t.1) ∧
      ∀ (B : Set ℕ) (N : ℕ), densityUpTo (A ∩ B) N =
        (L.map fun t ↦ t.2 * densityUpTo ({n | t.1 ∣ n} ∩ B) N).sum := by
  obtain ⟨L, hp, he⟩ := hA
  refine ⟨L, hp, fun B N ↦ ?_⟩
  unfold densityUpTo
  rw [countUpTo_inter_as_sum]
  have h : (∑ n ∈ integerPrefixSlice B N, (if n ∈ A then (1 : ℝ) else 0)) =
      ∑ n ∈ integerPrefixSlice B N, (L.map (divisibilityTerm · n)).sum := by
    apply sum_congr rfl
    intro n hn
    apply he
    simp only [integerPrefixSlice, integerPrefix, mem_filter, mem_Icc] at hn
    exact hn.1.1
  rw [h, sum_divisibilityTerms]
  clear hp he h
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons, add_div, mul_div_assoc, ih]

end IntegerDivisibilityExpansion

end GRHArticle.ProgressionFree

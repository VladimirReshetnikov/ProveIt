import GRHArticle.ProgressionFree.IntervalRothCertificate
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Deficiency of axis-progression-free triangular arrays

The difference between the sum of the one-dimensional Roth upper
bounds and the actual point count is invariant under transposition.
A translated tip preserves a previous deficiency, while a nonmaximal
row outside the tip incurs an additional unit.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical

abbrev NatGrid := Set (ℕ × ℕ)

/-- Every horizontal and vertical section avoids nonconstant three-term progressions. -/
def GridAxisFree (A : NatGrid) : Prop :=
  (∀ i, ThreeAPFree {j : ℕ | (i,j) ∈ A}) ∧ (∀ j, ThreeAPFree {i : ℕ | (i,j) ∈ A})

noncomputable def triangleRow (A : NatGrid) (i length : ℕ) : Finset ℕ :=
  (range length).filter fun j ↦ (i,j) ∈ A

theorem mem_triangleRow {A : NatGrid} {i n j : ℕ} : j ∈ triangleRow A i n ↔ j < n ∧ (i,j) ∈ A := by
  simp [triangleRow]

def triangleRothRowBound (L : ℕ) : ℕ := ∑ i ∈ range L, rothNumberNat (L-i)

noncomputable def triangleRothDeficit (A : NatGrid) (L : ℕ) : ℕ :=
  ∑ i ∈ range L, (rothNumberNat (L-i) - (triangleRow A i (L-i)).card)

private theorem row_card_le {A : NatGrid} (h : GridAxisFree A) (i n : ℕ) :
    (triangleRow A i n).card ≤ rothNumberNat n :=
  ((h.1 i).mono (fun _ hj ↦ (mem_filter.mp hj).2)).le_addRothNumber (filter_subset ..)

private theorem row_free {A : NatGrid} (h : GridAxisFree A) (i n : ℕ) :
    ThreeAPFree (triangleRow A i n : Set ℕ) :=
  (h.1 i).mono (fun _ hj ↦ (mem_filter.mp hj).2)

private theorem deficit_add_count {A : NatGrid} (h : GridAxisFree A) (L : ℕ) :
    triangleRothDeficit A L + ∑ i ∈ range L, (triangleRow A i (L-i)).card = triangleRothRowBound L := by
  unfold triangleRothDeficit triangleRothRowBound
  rw [←sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ Nat.sub_add_cancel (row_card_le h i _)

private def transposeGrid (A : NatGrid) : NatGrid := {p | p.swap ∈ A}

private theorem transpose_free {A : NatGrid} (h : GridAxisFree A) :
    GridAxisFree (transposeGrid A) := ⟨h.2,h.1⟩

private theorem transpose_count (A : NatGrid) (L : ℕ) :
    (∑ i ∈ range L, (triangleRow (transposeGrid A) i (L-i)).card) =
      ∑ j ∈ range L, (triangleRow A j (L-j)).card := by
  have he (B : NatGrid) (i : ℕ) :
      (triangleRow B i (L-i)).card =
        ∑ j ∈ range L, if i+j<L ∧ (i,j) ∈ B then 1 else 0 := by
    rw [sum_boole]
    congr 1
    ext j
    simp only [triangleRow,mem_filter,mem_range]
    constructor
    · rintro ⟨hl,hmem⟩
      exact ⟨by omega,by omega,hmem⟩
    · rintro ⟨_,hl,hmem⟩
      exact ⟨by omega,hmem⟩
  simp_rw [he]
  rw [sum_comm]
  exact sum_congr rfl fun j _ ↦ sum_congr rfl fun i _ ↦ by
    simp only [transposeGrid,Set.mem_setOf_eq,Prod.swap_prod_mk,Nat.add_comm i j]

private theorem transpose_deficit {A : NatGrid} (h : GridAxisFree A) (L : ℕ) :
    triangleRothDeficit (transposeGrid A) L = triangleRothDeficit A L := by
  have h₁ := deficit_add_count (transpose_free h) L
  have h₂ := deficit_add_count h L
  rw [transpose_count] at h₁
  omega

private def shiftRows (A : NatGrid) (a : ℕ) : NatGrid := {p | (a+p.1,p.2) ∈ A}

private theorem shift_free {A : NatGrid} (h : GridAxisFree A) (a : ℕ) :
    GridAxisFree (shiftRows A a) := by
  refine ⟨fun i ↦ h.1 (a+i),?_⟩
  intro j x hx y hy z hz he
  have he' : (a+x)+(a+z)=(a+y)+(a+y) := by omega
  exact Nat.add_left_cancel ((h.2 j) (show (a+x,j) ∈ A from hx) (show (a+y,j) ∈ A from hy) (show (a+z,j) ∈ A from hz) he')

private theorem deficit_split (A : NatGrid) (a K : ℕ) :
    triangleRothDeficit A (a+K) =
      (∑ i ∈ range a, (rothNumberNat (a+K-i) - (triangleRow A i (a+K-i)).card)) +
        triangleRothDeficit (shiftRows A a) K := by
  unfold triangleRothDeficit
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [show a+K-(a+j) = K-j by omega]
  rfl

/-- Every axis-free triangular section of length `L` misses at least
`h` positions relative to its individual row optima. -/
def TriangleRothLoss (L h : ℕ) : Prop := ∀ A : NatGrid, GridAxisFree A → h ≤ triangleRothDeficit A L

theorem TriangleRothLoss.mono_length {K L h : ℕ} (hK : TriangleRothLoss K h) (hKL : K ≤ L) :
    TriangleRothLoss L h := by
  intro A hA
  have h := hK (shiftRows A (L-K)) (shift_free hA _)
  have he := deficit_split A (L-K) K
  rw [Nat.sub_add_cancel hKL] at he
  omega

private theorem row_max_of_small_deficit {K L h i : ℕ} {A : NatGrid} (hA : GridAxisFree A)
    (hK : TriangleRothLoss K h) (hi : i < L-K) (hbad : triangleRothDeficit A L ≤ h) :
    (triangleRow A i (L-i)).card = rothNumberNat (L-i) := by
  have hKL : K ≤ L := by omega
  have he := deficit_split A (L-K) K
  rw [Nat.sub_add_cancel hKL] at he
  have htip := hK _ (shift_free hA (L-K))
  have hi' : rothNumberNat (L-i) - (triangleRow A i (L-i)).card ≤
      ∑ j ∈ range (L-K), (rothNumberNat (L-j) - (triangleRow A j (L-j)).card) :=
    single_le_sum (f := fun j ↦ rothNumberNat (L-j) - (triangleRow A j (L-j)).card)
      (fun _ _ ↦ Nat.zero_le _) (mem_range.mpr hi)
  have hup := row_card_le hA i (L-i)
  omega

/-- A row and column which require opposite choices at a common point
force a new unit of loss beyond the translated length-`K` tip. -/
theorem TriangleRothLoss.succ_of_conflict {K L h i j : ℕ} (hK : TriangleRothLoss K h)
    (hi : i < L-K) (hj : j < L-K) (hij : i+j < L)
    (hRow : ∀ B : Finset ℕ, B ⊆ range (L-i) → ThreeAPFree (B : Set ℕ) →
      B.card = rothNumberNat (L-i) → j ∈ B)
    (hCol : ∀ B : Finset ℕ, B ⊆ range (L-j) → ThreeAPFree (B : Set ℕ) →
      B.card = rothNumberNat (L-j) → i ∉ B) : TriangleRothLoss L (h+1) := by
  intro A hA
  by_contra! hbad
  have hh : triangleRothDeficit A L ≤ h := by omega
  have hr := hRow (triangleRow A i _) (filter_subset ..) (row_free hA _ _)
    (row_max_of_small_deficit hA hK hi hh)
  have ht : triangleRothDeficit (transposeGrid A) L ≤ h := (transpose_deficit hA L).le.trans hh
  have hc := hCol (triangleRow (transposeGrid A) j _) (filter_subset ..) (row_free (transpose_free hA) _ _)
    (row_max_of_small_deficit (transpose_free hA) hK hj ht)
  exact hc (mem_filter.mpr ⟨mem_range.mpr (by omega), (mem_filter.mp hr).2⟩)

/-- Read the row deficiency as a bound on the cardinality of an actual
finite set of exponent pairs. -/
theorem TriangleRothLoss.card_le {L h : ℕ} (hl : TriangleRothLoss L h) (A : Finset (ℕ × ℕ))
    (hL : ∀ x ∈ A, x.1+x.2<L) (hA : GridAxisFree (A : NatGrid)) :
    A.card+h ≤ triangleRothRowBound L := by
  have he : A.card = ∑ i ∈ range L, (triangleRow A i (L-i)).card := by
    rw [card_eq_sum_card_fiberwise (s := A) (f := Prod.fst) (t := range L)
      (fun x hx ↦ mem_range.mpr (by have := hL x hx; omega))]
    apply sum_congr rfl
    intro i _
    apply card_bij (fun x _ ↦ x.2)
    · intro x hx
      obtain ⟨hx,he⟩ := mem_filter.mp hx
      have hn := hL x hx
      exact mem_triangleRow.mpr ⟨by omega,he ▸ hx⟩
    · intro x hx y hy he
      exact Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) he
    · intro j hj
      exact ⟨(i,j),mem_filter.mpr ⟨(mem_triangleRow.mp hj).2,rfl⟩,rfl⟩
  rw [he]
  have hd := deficit_add_count hA L
  have := hl _ hA
  omega

end GRHArticle.ProgressionFree

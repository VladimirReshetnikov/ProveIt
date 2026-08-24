import DavisEntringerGrahamSimmons1977.Proofs
import Mathlib

set_option autoImplicit false

noncomputable section

namespace LeanProofs.DavisEntringerGrahamSimmons1977

private def natEquivPositiveNat : Nat ≃ PositiveNat where
  toFun n := ⟨n + 1, by omega⟩
  invFun n := (n : Nat) - 1
  left_inv n := by simp
  right_inv n := by
    apply Subtype.ext
    change (n.val - 1) + 1 = n.val
    omega

private def intParityEquiv : Int ≃ Int ⊕ Int where
  toFun z := if Even z then Sum.inl (z / 2) else Sum.inr ((z - 1) / 2)
  invFun := Sum.elim (fun z => 2 * z) (fun z => 2 * z + 1)
  left_inv z := by
    rcases Int.even_or_odd' z with ⟨k, hk | hk⟩
    · subst z
      have heven : Even (2 * k) := ⟨k, by omega⟩
      simp [heven]
    · subst z
      have hnot : ¬Even (2 * k + 1) := by
        rintro ⟨l, hl⟩
        omega
      simp [hnot]
  right_inv z := by
    rcases z with z | z
    · have heven : Even (2 * z) := ⟨z, by omega⟩
      simp [heven]
    · have hnot : ¬Even (2 * z + 1) := by
        rintro ⟨l, hl⟩
        omega
      simp [hnot]

private def signEquiv : PositiveNat ⊕ PositiveNat ≃ Int :=
  (Equiv.sumCongr natEquivPositiveNat natEquivPositiveNat).symm.trans
    Equiv.intEquivNatSumNat.symm

private def integerPermutationOfDouble (p : DoublyInfinitePermutation) : IntegerPermutation :=
  intParityEquiv.trans ((Equiv.sumCongr p p).trans signEquiv)

private theorem integerPermutationOfDouble_even (p : DoublyInfinitePermutation) (i : Int) :
    integerPermutationOfDouble p (2 * i) = (p i : Nat) - 1 := by
  simp [integerPermutationOfDouble, intParityEquiv, signEquiv, natEquivPositiveNat,
    Int.even_iff]
  change Int.ofNat ((p i : Nat) - 1) = ((p i : Nat) : Int) - 1
  rw [Int.ofNat_eq_natCast]
  have hp : 0 < (p i : Nat) := (p i).property
  omega

private theorem integerPermutationOfDouble_odd (p : DoublyInfinitePermutation) (i : Int) :
    integerPermutationOfDouble p (2 * i + 1) = -((p i : Nat) : Int) := by
  simp [integerPermutationOfDouble, intParityEquiv, signEquiv, natEquivPositiveNat,
    Int.even_iff]
  change Int.negSucc ((p i : Nat) - 1) = -((p i : Nat) : Int)
  rw [Int.negSucc_eq]
  have hp : 0 < (p i : Nat) := (p i).property
  omega

private theorem integerPermutationOfDouble_nonneg_position (p : DoublyInfinitePermutation)
    (i : Int) (hi : 0 ≤ integerPermutationOfDouble p i) :
    ∃ j : Int, i = 2 * j ∧
      integerPermutationOfDouble p i = ((p j : Nat) : Int) - 1 := by
  rcases Int.even_or_odd' i with ⟨j, rfl | rfl⟩
  · exact ⟨j, rfl, integerPermutationOfDouble_even p j⟩
  · rw [integerPermutationOfDouble_odd] at hi
    have hp : 0 < ((p j : PositiveNat) : Nat) := (p j).property
    omega

private theorem integerPermutationOfDouble_neg_position (p : DoublyInfinitePermutation)
    (i : Int) (hi : integerPermutationOfDouble p i < 0) :
    ∃ j : Int, i = 2 * j + 1 ∧
      integerPermutationOfDouble p i = -((p j : Nat) : Int) := by
  rcases Int.even_or_odd' i with ⟨j, rfl | rfl⟩
  · rw [integerPermutationOfDouble_even] at hi
    have hp : 0 < ((p j : PositiveNat) : Nat) := (p j).property
    omega
  · exact ⟨j, rfl, integerPermutationOfDouble_odd p j⟩

private def firstFour (i : Fin 4) : Fin 7 := ⟨i, by omega⟩

private theorem firstFour_strictMono : StrictMono firstFour := by
  intro i j hij
  exact hij

private def lastFour (i : Fin 4) : Fin 7 := ⟨(i : Nat) + 3, by omega⟩

private theorem lastFour_strictMono : StrictMono lastFour := by
  intro i j hij
  apply Fin.mk_lt_mk.mpr
  exact Nat.add_lt_add_right (Fin.mk_lt_mk.mp hij) 3

private theorem nonnegative_four_impossible (p : DoublyInfinitePermutation) (hp : p ∈ D 4)
    (pos : Fin 4 → Int) (hpos : StrictMono pos)
    (hnonneg : ∀ i, 0 ≤ integerPermutationOfDouble p (pos i))
    (hprogression : IsArithmeticProgression (fun i => integerPermutationOfDouble p (pos i))) :
    False := by
  have hexists : ∀ i, ∃ j : Int, pos i = 2 * j ∧
      integerPermutationOfDouble p (pos i) = ((p j : Nat) : Int) - 1 :=
    fun i => integerPermutationOfDouble_nonneg_position p (pos i) (hnonneg i)
  choose j hjpos hjval using hexists
  have hjmono : StrictMono j := by
    intro i k hik
    have hik' := hpos hik
    rw [hjpos i, hjpos k] at hik'
    omega
  obtain ⟨a, d, hd, hformula⟩ := hprogression
  apply hp
  refine ⟨j, hjmono, a + 1, d, hd, ?_⟩
  intro i
  have hformula_i := hformula i
  have hjval_i := hjval i
  dsimp at hformula_i
  simp only [doublyPermutationSequence]
  calc
    ((p (j i) : Nat) : Int) = integerPermutationOfDouble p (pos i) + 1 := by omega
    _ = (a + (i : Nat) * d) + 1 := by rw [hformula_i]
    _ = a + 1 + (i : Nat) * d := by ring

private theorem negative_four_impossible (p : DoublyInfinitePermutation) (hp : p ∈ D 4)
    (pos : Fin 4 → Int) (hpos : StrictMono pos)
    (hneg : ∀ i, integerPermutationOfDouble p (pos i) < 0)
    (hprogression : IsArithmeticProgression (fun i => integerPermutationOfDouble p (pos i))) :
    False := by
  have hexists : ∀ i, ∃ j : Int, pos i = 2 * j + 1 ∧
      integerPermutationOfDouble p (pos i) = -((p j : Nat) : Int) :=
    fun i => integerPermutationOfDouble_neg_position p (pos i) (hneg i)
  choose j hjpos hjval using hexists
  have hjmono : StrictMono j := by
    intro i k hik
    have hik' := hpos hik
    rw [hjpos i, hjpos k] at hik'
    omega
  obtain ⟨a, d, hd, hformula⟩ := hprogression
  apply hp
  have hdne : d ≠ 0 := by simpa [bne_iff_ne] using hd
  have hnegd : (-d != 0) = true := by
    simpa [bne_iff_ne] using neg_ne_zero.mpr hdne
  refine ⟨j, hjmono, -a, -d, hnegd, ?_⟩
  intro i
  have hformula_i := hformula i
  have hjval_i := hjval i
  dsimp at hformula_i
  simp only [doublyPermutationSequence]
  calc
    ((p (j i) : Nat) : Int) = -integerPermutationOfDouble p (pos i) := by omega
    _ = -(a + (i : Nat) * d) := by rw [hformula_i]
    _ = -a + (i : Nat) * -d := by ring

private theorem firstFour_progression (p : DoublyInfinitePermutation)
    (pos : Fin 7 → Int) (a d : Int)
    (hformula : ∀ i, integerPermutationOfDouble p (pos i) = a + (i : Nat) * d)
    (hd : (d != 0) = true) :
    IsArithmeticProgression
      (fun i => integerPermutationOfDouble p (pos (firstFour i))) := by
  refine ⟨a, d, hd, ?_⟩
  intro i
  simpa [firstFour] using hformula (firstFour i)

private theorem lastFour_progression (p : DoublyInfinitePermutation)
    (pos : Fin 7 → Int) (a d : Int)
    (hformula : ∀ i, integerPermutationOfDouble p (pos i) = a + (i : Nat) * d)
    (hd : (d != 0) = true) :
    IsArithmeticProgression
      (fun i => integerPermutationOfDouble p (pos (lastFour i))) := by
  refine ⟨a + 3 * d, d, hd, ?_⟩
  intro i
  change integerPermutationOfDouble p (pos (lastFour i)) = _
  rw [hformula (lastFour i)]
  simp only [lastFour]
  push_cast
  ring

theorem integer_seven_term_construction_holds : integer_seven_term_construction := by
  rw [integer_seven_term_construction]
  have hfact : D 4 ≠ ∅ := by simpa [fact_6] using fact_6_holds
  obtain ⟨p, hp⟩ : Set.Nonempty (D 4) := Set.nonempty_iff_ne_empty.mpr hfact
  refine ⟨integerPermutationOfDouble p, ?_⟩
  intro hap
  obtain ⟨pos, hpos, a, d, hd, hprogression⟩ := hap
  change ∀ i, integerPermutationOfDouble p (pos i) = a + (i : Nat) * d at hprogression
  have hmiddle := hprogression (3 : Fin 7)
  have hdne : d ≠ 0 := by simpa [bne_iff_ne] using hd
  by_cases hnonneg : 0 ≤ integerPermutationOfDouble p (pos (3 : Fin 7))
  · by_cases hdpos : 0 < d
    · apply nonnegative_four_impossible p hp (fun i => pos (lastFour i))
        (hpos.comp lastFour_strictMono)
      · intro i
        rw [hprogression (lastFour i)]
        rw [hmiddle] at hnonneg
        simp only [lastFour] at hnonneg ⊢
        push_cast
        have hi0 : 0 ≤ (i : Int) := by positivity
        have hprod : 0 ≤ (i : Int) * d := mul_nonneg hi0 hdpos.le
        rw [show a + ((i : Int) + 3) * d = (a + 3 * d) + (i : Int) * d by ring]
        exact add_nonneg hnonneg hprod
      · exact lastFour_progression p pos a d hprogression hd
    · have hdneg : d < 0 := by omega
      apply nonnegative_four_impossible p hp (fun i => pos (firstFour i))
        (hpos.comp firstFour_strictMono)
      · intro i
        rw [hprogression (firstFour i)]
        rw [hmiddle] at hnonneg
        simp only [firstFour] at hnonneg ⊢
        have hi3 : (i : Int) ≤ 3 := by omega
        have hprod : 0 ≤ (3 - (i : Int)) * (-d) :=
          mul_nonneg (sub_nonneg.mpr hi3) (neg_nonneg.mpr hdneg.le)
        rw [show a + (i : Int) * d = (a + 3 * d) + (3 - (i : Int)) * (-d) by ring]
        exact add_nonneg hnonneg hprod
      · exact firstFour_progression p pos a d hprogression hd
  · have hmiddleNeg : integerPermutationOfDouble p (pos (3 : Fin 7)) < 0 :=
      lt_of_not_ge hnonneg
    by_cases hdpos : 0 < d
    · apply negative_four_impossible p hp (fun i => pos (firstFour i))
        (hpos.comp firstFour_strictMono)
      · intro i
        rw [hprogression (firstFour i)]
        rw [hmiddle] at hmiddleNeg
        simp only [firstFour] at hmiddleNeg ⊢
        have hi3 : (i : Int) ≤ 3 := by omega
        have hprod : 0 ≤ (3 - (i : Int)) * d :=
          mul_nonneg (sub_nonneg.mpr hi3) hdpos.le
        have hle : a + (i : Int) * d ≤ a + 3 * d := by
          rw [show a + 3 * d = (a + (i : Int) * d) + (3 - (i : Int)) * d by ring]
          exact le_add_of_nonneg_right hprod
        exact lt_of_le_of_lt hle hmiddleNeg
      · exact firstFour_progression p pos a d hprogression hd
    · have hdneg : d < 0 := by omega
      apply negative_four_impossible p hp (fun i => pos (lastFour i))
        (hpos.comp lastFour_strictMono)
      · intro i
        rw [hprogression (lastFour i)]
        rw [hmiddle] at hmiddleNeg
        simp only [lastFour] at hmiddleNeg ⊢
        push_cast
        have hi0 : 0 ≤ (i : Int) := by positivity
        have hprod : 0 ≤ (i : Int) * (-d) :=
          mul_nonneg hi0 (neg_nonneg.mpr hdneg.le)
        have hle : a + ((i : Int) + 3) * d ≤ a + 3 * d := by
          rw [show a + ((i : Int) + 3) * d = (a + 3 * d) - (i : Int) * (-d) by ring]
          exact sub_le_self _ hprod
        exact lt_of_le_of_lt hle hmiddleNeg
      · exact lastFour_progression p pos a d hprogression hd

end LeanProofs.DavisEntringerGrahamSimmons1977


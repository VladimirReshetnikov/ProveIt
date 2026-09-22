import Surreal.HahnSeries.Neumann
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Finite ancestry relative to an input support

The last assertion of `dyn:lem:neumann` in
`docs/surcomplex/dynamics-and-normal-forms/article.tex` allows an arbitrary
well-ordered input support, including negative exponents. It gives a finite
bound on the length of words reaching each output exponent, with that bound
depending on the input support.

The bound `ℓ_S(γ)` asserted in `dyn:cor:ancestry` does not have that generality:
even multiplication by a positive monomial gives counterexamples. The final
section records this obstruction as an identity of actual Hahn series.
-/

namespace Surreal.HahnSeries

open scoped Pointwise

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- The shifted support in the last assertion of `dyn:lem:neumann` is well
ordered, without a sign restriction on the input support. -/
theorem isPWO_add_positive_closure {A S : Set Γ} (hA : A.IsPWO) (hS : S.IsPWO)
    (hpos : ∀ s ∈ S, 0 < s) : (A + (AddSubmonoid.closure S : Set Γ)).IsPWO :=
  hA.add (neumann_positive hS hpos).1

/-- At a fixed output exponent there are only finitely many pairs of an
input exponent and a positive word producing that exponent. This is the last
finiteness assertion of `dyn:lem:neumann`. -/
theorem finite_shifted_words_of_sum_eq {A S : Set Γ} (hA : A.IsPWO) (hS : S.IsPWO)
    (hpos : ∀ s ∈ S, 0 < s) (g : Γ) :
    {p : Γ × List Γ | p.1 ∈ A ∧ (∀ s ∈ p.2, s ∈ S) ∧ p.1 + p.2.sum = g}.Finite := by
  have hanti := Set.AddAntidiagonal.finite_of_isPWO hA (neumann_positive hS hpos).1 g
  have hfinite := hanti.biUnion fun p _ =>
    (finite_words_of_sum_eq hS hpos p.2).image (fun l => (p.1, l))
  apply hfinite.subset
  rintro ⟨a, l⟩ ⟨ha, hl, hsum⟩
  apply Set.mem_iUnion.mpr
  refine ⟨(a, l.sum), Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact ⟨ha, (AddSubmonoid.closure S).list_sum_mem
      (fun s hs => AddSubmonoid.subset_closure (hl s hs)), hsum⟩
  · exact ⟨l, ⟨hl, rfl⟩, rfl⟩

/-- Corrected combinatorial depth bound for `dyn:cor:ancestry`. The bound
depends on the input support as well as the positive alphabet and output
exponent; no nonnegativity assumption on the input is needed. -/
theorem exists_shifted_word_length_bound {A S : Set Γ} (hA : A.IsPWO) (hS : S.IsPWO)
    (hpos : ∀ s ∈ S, 0 < s) (g : Γ) :
    ∃ N : ℕ, ∀ a ∈ A, ∀ l : List Γ, (∀ s ∈ l, s ∈ S) →
      a + l.sum = g → l.length ≤ N := by
  classical
  let F := (finite_shifted_words_of_sum_eq hA hS hpos g).toFinset
  refine ⟨F.sup (fun p => p.2.length), ?_⟩
  intro a ha l hl hsum
  apply Finset.le_sup (b := (a, l)) (f := fun p : Γ × List Γ => p.2.length)
  simpa only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using
    And.intro ha (And.intro hl hsum)

/-- If each step contributes a nonempty positive word, the number of steps
is bounded at a fixed output exponent. This is the depth implication of
finite ancestry with the input support retained. -/
theorem exists_shifted_nonempty_word_depth_bound {A S : Set Γ}
    (hA : A.IsPWO) (hS : S.IsPWO) (hpos : ∀ s ∈ S, 0 < s) (g : Γ) :
    ∃ N : ℕ, ∀ a ∈ A, ∀ L : List (List Γ),
      (∀ l ∈ L, l ≠ [] ∧ ∀ s ∈ l, s ∈ S) → a + L.flatten.sum = g → L.length ≤ N := by
  obtain ⟨N, hN⟩ := exists_shifted_word_length_bound hA hS hpos g
  refine ⟨N, ?_⟩
  intro a ha L hL hsum
  have hletters : ∀ s ∈ L.flatten, s ∈ S := by
    intro s hs
    obtain ⟨l, hl, hs⟩ := List.mem_flatten.mp hs
    exact (hL l hl).2 s hs
  have hlength : L.length ≤ L.flatten.length := by
    clear hletters hsum
    induction L with
    | nil => simp
    | cons l L ih =>
      have htail : ∀ m ∈ L, m ≠ [] ∧ ∀ s ∈ m, s ∈ S :=
        fun m hm => hL m (List.mem_cons_of_mem l hm)
      have hl : 0 < l.length := List.length_pos_iff.mpr (hL l List.mem_cons_self).1
      simpa only [List.length_cons, List.flatten_cons, List.length_append, Nat.add_comm]
        using Nat.add_le_add (ih htail) hl
  exact hlength.trans (hN a ha L.flatten hletters hsum)

/-- The input exponents contributing at a fixed output exponent form a
finite set. -/
theorem finite_input_exponents_of_shifted_words {A S : Set Γ}
    (hA : A.IsPWO) (hS : S.IsPWO) (hpos : ∀ s ∈ S, 0 < s) (g : Γ) :
    {a ∈ A | ∃ l : List Γ, (∀ s ∈ l, s ∈ S) ∧ a + l.sum = g}.Finite := by
  apply ((finite_shifted_words_of_sum_eq hA hS hpos g).image Prod.fst).subset
  rintro a ⟨ha, l, hl, hsum⟩
  exact ⟨(a, l), ⟨ha, hl, hsum⟩, rfl⟩

/-- All letters occurring in all ancestries at a fixed output exponent
form a finite set, with the input support included in the definition. -/
theorem finite_letters_of_shifted_words {A S : Set Γ}
    (hA : A.IsPWO) (hS : S.IsPWO) (hpos : ∀ s ∈ S, 0 < s) (g : Γ) :
    {s | ∃ a ∈ A, ∃ l : List Γ,
      (∀ t ∈ l, t ∈ S) ∧ a + l.sum = g ∧ s ∈ l}.Finite := by
  have hfinite := (finite_shifted_words_of_sum_eq hA hS hpos g).biUnion
    (fun p _ => p.2.finite_toSet)
  apply hfinite.subset
  rintro s ⟨a, ha, l, hl, hsum, hs⟩
  exact Set.mem_iUnion.mpr ⟨(a, l), Set.mem_iUnion.mpr ⟨⟨ha, hl, hsum⟩, hs⟩⟩

/-- A positive word of total weight zero is empty. In particular the
unshifted depth at zero in `dyn:eq:depth` is zero. -/
theorem eq_nil_of_positive_word_sum_eq_zero {S : Set Γ} (hpos : ∀ s ∈ S, 0 < s)
    {l : List Γ} (hl : ∀ s ∈ l, s ∈ S) (hsum : l.sum = 0) : l = [] := by
  exact (eq_of_sublistForall₂_of_sum_eq List.SublistForall₂.nil
    (fun s hs => hpos s (hl s hs)) hsum.symm).symm

section Counterexample

open _root_.HahnSeries

/-- A complex-linear operator whose every term adds exactly the one-letter
positive word `[1]` to an input exponent. -/
noncomputable def positiveMonomialShift : ℂ⟦ℤ⟧ →ₗ[ℂ] ℂ⟦ℤ⟧ :=
  { toFun := fun A => single 1 1 * A
    map_add' := fun A B => mul_add _ A B
    map_smul' := fun c A => by
      ext g
      simp only [coeff_single_mul, coeff_smul, one_mul, RingHom.id_apply] }

/-- The shift has exactly one coefficient operation at each exponent. -/
theorem coeff_positiveMonomialShift (A : ℂ⟦ℤ⟧) (g : ℤ) :
    (positiveMonomialShift A).coeff g = A.coeff (g - 1) := by
  change (single 1 (1 : ℂ) * A).coeff g = A.coeff (g - 1)
  rw [coeff_single_mul, one_mul]

/-- Iterating the positive shift translates by the number of iterations. -/
theorem iterate_positiveMonomialShift (n : ℕ) (A : ℂ⟦ℤ⟧) :
    ((positiveMonomialShift : ℂ⟦ℤ⟧ → ℂ⟦ℤ⟧)^[n]) A = single (n : ℤ) 1 * A := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change single 1 1 * (single (n : ℤ) 1 * A) = single ((n + 1 : ℕ) : ℤ) 1 * A
    rw [← mul_assoc, single_mul_single, one_mul]
    simp [add_comm]

/-- Arbitrarily many positive shifts can contribute at exponent zero when
the input has a sufficiently negative exponent. For `n = 100` this is the
counterexample recorded for `dyn:cor:ancestry` in the formalization ledger. -/
theorem iterate_positiveMonomialShift_negative_monomial (n : ℕ) :
    ((positiveMonomialShift : ℂ⟦ℤ⟧ → ℂ⟦ℤ⟧)^[n])
      (single (-(n : ℤ)) 1) = 1 := by
  rw [iterate_positiveMonomialShift, single_mul_single]
  simp

/-- The unshifted positive alphabet `{1}` has only the empty word at output
weight zero, so the source's unshifted bound `ℓ_{ {1} }(0)` is zero. -/
theorem singleton_one_word_sum_zero_length {l : List ℤ}
    (hl : ∀ s ∈ l, s ∈ ({1} : Set ℤ)) (hsum : l.sum = 0) : l.length = 0 := by
  have hnil := eq_nil_of_positive_word_sum_eq_zero (S := ({1} : Set ℤ))
    (by simp) hl hsum
  simp [hnil]

/-- No bound independent of the input support can limit contributions at
exponent zero, even for the complex-linear one-letter positive shift. -/
theorem no_input_independent_ancestry_depth :
    ¬ ∃ N : ℕ, ∀ A : ℂ⟦ℤ⟧, ∀ n : ℕ, N < n →
      (((positiveMonomialShift : ℂ⟦ℤ⟧ → ℂ⟦ℤ⟧)^[n]) A).coeff 0 = 0 := by
  rintro ⟨N, hN⟩
  have h := hN (single (-((N + 1 : ℕ) : ℤ)) 1) (N + 1) (Nat.lt_succ_self N)
  rw [iterate_positiveMonomialShift_negative_monomial] at h
  simp at h

end Counterexample

end Surreal.HahnSeries

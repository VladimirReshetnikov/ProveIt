import PA194ModelClosedSepClassifier
import PA194SourceSeparation

set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

theorem syntactic_shift_fixed_noFree (n : ℕ) (p : Semiproposition SourceL n)
    (h : Rewriting.shift p = p) : p.freeVariables = ∅ := by
  have prev (x : ℕ) (hx : p.FVar? x) : ∃ y, p.FVar? y ∧ x = y+1 := by
    have hx' : (Rew.shift ▹ p).FVar? x := by
      change (Rewriting.shift p).FVar? x
      rw [h]
      exact hx
    rcases Semiformula.fvar?_rew hx' with ⟨i,hi⟩ | ⟨y,hy,hi⟩
    · simp at hi
    · refine ⟨y,hy,?_⟩
      have hh : y+1 = x := by simpa using hi
      exact hh.symm
  have hn : ∀ x, ¬p.FVar? x := by
    intro x
    induction x using Nat.strong_induction_on with
    | h x ih =>
      intro hx
      obtain ⟨y,hy,hxy⟩ := prev x hx
      exact ih y (by omega) hy
  ext x
  simp only [Finset.notMem_empty, iff_false]
  exact hn x

theorem syntactic_noFree_shift_fixed (n : ℕ) (p : Semiproposition SourceL n)
    (hp : p.freeVariables = ∅) : Rewriting.shift p = p := by
  have h := Rewriting.shifts_emb (L := SourceL) [p.toEmpty hp]
  simpa only [Rewriting.shifts, List.map_cons, List.map_nil, Semiformula.emb_toEmpty,
    List.cons.injEq, and_true] using h

theorem standard_quote_shift_fixed_iff (n : ℕ) (p : Semiproposition SourceL n) :
    shift SourceL (⌜p⌝ : ℕ) = ⌜p⌝ ↔ p.freeVariables = ∅ := by
  have hquote : (⌜Rewriting.shift p⌝ : ℕ) = shift SourceL (⌜p⌝ : ℕ) := Semiformula.quote_shift p
  constructor
  · intro h
    have hcode : (⌜Rewriting.shift p⌝ : ℕ) = ⌜p⌝ := hquote.trans h
    have hsyn : Rewriting.shift p = p := by
      apply Encodable.encode_injective
      simpa [Semiformula.quote_eq_encode] using hcode
    exact syntactic_shift_fixed_noFree n p hsyn
  · intro h
    rw [← hquote,syntactic_noFree_shift_fixed n p h]

/-- Standard shift-invariant codes are exactly embedded semisentences. -/
theorem standard_quote_shift_fixed_semisentence_iff
    (n : ℕ) (p : Semiproposition SourceL n) :
    shift SourceL (⌜p⌝ : ℕ) = ⌜p⌝ ↔
      ∃ σ : Semisentence SourceL n, Rewriting.emb σ = p := by
  rw [standard_quote_shift_fixed_iff]
  constructor
  · intro h
    exact ⟨p.toEmpty h, Semiformula.emb_toEmpty p h⟩
  · rintro ⟨σ,rfl⟩
    exact Semiformula.freeVariables_emb σ

#print axioms standard_quote_shift_fixed_semisentence_iff
#print axioms standard_quote_shift_fixed_iff
#print axioms syntactic_noFree_shift_fixed
#print axioms syntactic_shift_fixed_noFree
end PA194ModelLogic

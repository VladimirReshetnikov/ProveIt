import PA194TermShiftPR
set_option autoImplicit false
namespace PA194TermShiftModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping M6.PA.RelationalSource
open PA194SourceSearchCoding
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem no_function_symbols (k f : V) : ¬ language.IsFunc k f := by
  change ¬ (⊥ : ArithmeticSemisentence 2).Evalb ![k,f]
  simp

theorem term_cases {t : V} (ht : IsUTerm language t) :
    (∃ z : V, t = ^#z) ∨ (∃ x : V, t = ^&x) := by
  rcases IsUTerm.case ht with h | h | ⟨k,f,v,hf,_,_⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (no_function_symbols k f hf)

theorem termShift_cases {t : V} (ht : IsUTerm language t) :
    (∃ z : V, t = ^#z ∧ termShift language t = ^#z) ∨
    (∃ x : V, t = ^&x ∧ termShift language t = ^&(x+1)) := by
  rcases term_cases ht with ⟨z, rfl⟩ | ⟨x, rfl⟩
  · exact Or.inl ⟨z, rfl, termShift_bvar z⟩
  · exact Or.inr ⟨x, rfl, termShift_fvar x⟩

noncomputable def termShiftAlgorithm (t : V) : V :=
  if t = 0 then 0 else
  if pi₁ (t-1) = 1 then pair 1 (pi₂ (t-1) + 1) + 1 else t

theorem termShiftAlgorithm_correct {t : V} (ht : IsUTerm language t) :
    termShiftAlgorithm t = termShift language t := by
  rcases term_cases ht with ⟨z, rfl⟩ | ⟨x, rfl⟩
  · rw [termShift_bvar]
    simp [termShiftAlgorithm, qqBvar]
  · rw [termShift_fvar]
    simp [termShiftAlgorithm, qqFvar]

def validTermShiftGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y t. (∃ z, !qqBvarDef t z ∧ !qqBvarDef y z) ∨
    (∃ x, !qqFvarDef t x ∧ !qqFvarDef y (x+1))”

theorem validTermShiftGraph_iff {t y : V} (ht : IsUTerm language t) :
    validTermShiftGraph.val.Eval ![y,t] Empty.elim ↔ y = termShift language t := by
  simp [validTermShiftGraph]
  constructor
  · rintro (⟨z, rfl, rfl⟩ | ⟨x, rfl, rfl⟩)
    · exact (termShift_bvar z).symm
    · exact (termShift_fvar x).symm
  · intro hy
    rcases term_cases ht with ⟨z, rfl⟩ | ⟨x, rfl⟩
    · left
      exact ⟨z, rfl, hy.trans (termShift_bvar z)⟩
    · right
      exact ⟨x, rfl, hy.trans (termShift_fvar x)⟩


theorem pi₁_nat (n : Nat) : pi₁ n = n.unpair.1 := by
  have h := pi₁_pair (V := Nat) n.unpair.1 n.unpair.2
  rw [nat_pair_eq, Nat.pair_unpair] at h
  exact h

theorem pi₂_nat (n : Nat) : pi₂ n = n.unpair.2 := by
  have h := pi₂_pair (V := Nat) n.unpair.1 n.unpair.2
  rw [nat_pair_eq, Nat.pair_unpair] at h
  exact h

theorem termShiftAlgorithm_nat (n : Nat) :
    termShiftAlgorithm (V := Nat) n = PA194TermShiftPR.termShiftCode n := by
  cases n with
  | zero => simp [termShiftAlgorithm, PA194TermShiftPR.termShiftCode]
  | succ n => simp [termShiftAlgorithm, PA194TermShiftPR.termShiftCode, pi₁_nat, pi₂_nat, nat_pair_eq]

#print axioms termShiftAlgorithm_nat
#print axioms validTermShiftGraph_iff
#print axioms termShiftAlgorithm_correct
#print axioms no_function_symbols
#print axioms term_cases
#print axioms termShift_cases
end PA194TermShiftModel

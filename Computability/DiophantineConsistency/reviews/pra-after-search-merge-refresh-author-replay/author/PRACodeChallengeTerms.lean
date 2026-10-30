import DiophantineConsistency.PRAFiniteFunctionCodes
import DiophantineConsistency.PRALanguage
/-! PR codes as terms supported on the finite parameter prefix. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRACodeChallengeTerms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage

def challengeTerm {n : ℕ} (c : Code n) : SyntacticTerm language :=
  .func c (fun i => &i.val)

theorem challengeTerm_support {n : ℕ} (c : Code n) (k : ℕ) (h : (challengeTerm c).FVar? k) : k < n := by
  simp only [challengeTerm, Semiterm.FVar?, Semiterm.freeVariables_func, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Semiterm.freeVariables_fvar, Finset.mem_singleton] at h
  obtain ⟨i,hi⟩ := h
  subst k
  exact i.isLt

theorem challengeTerm_eval {M : Type} [Structure language M] {n : ℕ} (c : Code n) (e : ℕ → M) :
    Semiterm.val ![] e (challengeTerm c) = Structure.func (L := language) c (fun i => e i.val) := by
  simp [challengeTerm, Semiterm.val_func, Function.comp_def]
end DiophantineConsistency.PRACodeChallengeTerms

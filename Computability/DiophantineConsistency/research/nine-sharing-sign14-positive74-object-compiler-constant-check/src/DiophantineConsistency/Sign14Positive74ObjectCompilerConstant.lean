import DiophantineConsistency.Sign14Positive74ObjectShiftNegativeLeaf

/-! SOURCE ONLY: assignment independence for actual compiled constants. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectCompilerConstant
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory FoundationHANoZero
open Sign14Positive74ObjectCompilerOps

def reflectedOpen {n : ℕ} (t : SetTheory.PA.Term) (v : Fin n → Term language ℕ) : Term language ℕ :=
  Rew.embSubsts v (Semiterm.lMap embedding (sourceTerm n t))

theorem reflected_closed {n : ℕ} (t : SetTheory.PA.Term)
    (h : ∀ i, ¬ SetTheory.PA.Term.Free i t) (v w : Fin n → Term language ℕ) :
    reflectedOpen t v = reflectedOpen t w := by
  induction t generalizing h with
  | var i => exact False.elim (h i rfl)
  | zero =>
      simp [reflectedOpen, sourceTerm, reflectTerm, Semiterm.lMap_func, Rew.func,
        Function.comp_def, funext_iff]
  | succ t ih =>
      have ht : ∀ i, ¬ SetTheory.PA.Term.Free i t := by simpa only [SetTheory.PA.Term.Free] using h
      have hh := ih ht
      simp only [reflectedOpen, sourceTerm] at hh
      simp [reflectedOpen, sourceTerm, reflectTerm, Semiterm.lMap_func, Rew.func,
        Function.comp_def, funext_iff, Fin.forall_fin_two, hh]
  | add p q hp hq =>
      have h₁ : ∀ i, ¬ SetTheory.PA.Term.Free i p := fun i hi => h i (Or.inl hi)
      have h₂ : ∀ i, ¬ SetTheory.PA.Term.Free i q := fun i hi => h i (Or.inr hi)
      have hp' := hp h₁
      have hq' := hq h₂
      simp only [reflectedOpen, sourceTerm] at hp' hq'
      simp [reflectedOpen, sourceTerm, reflectTerm, Semiterm.lMap_func, Rew.func,
        Function.comp_def, funext_iff, Fin.forall_fin_two, hp', hq']
  | mul p q hp hq =>
      have h₁ : ∀ i, ¬ SetTheory.PA.Term.Free i p := fun i hi => h i (Or.inl hi)
      have h₂ : ∀ i, ¬ SetTheory.PA.Term.Free i q := fun i hi => h i (Or.inr hi)
      have hp' := hp h₁
      have hq' := hq h₂
      simp only [reflectedOpen, sourceTerm] at hp' hq'
      simp [reflectedOpen, sourceTerm, reflectTerm, Semiterm.lMap_func, Rew.func,
        Function.comp_def, funext_iff, Fin.forall_fin_two, hp', hq']

theorem compiled_constant {n : ℕ} (k : ℕ) (v w : Fin n → Term language ℕ) :
    compiledOpen (.constant k) v = compiledOpen (.constant k) w := by
  exact reflected_closed (ArithmeticExpression.binaryNumeral k)
    (fun i => ArithmeticExpression.binaryNumeral_closed k i) v w
end DiophantineConsistency.Sign14Positive74ObjectCompilerConstant
#print axioms DiophantineConsistency.Sign14Positive74ObjectCompilerConstant.reflected_closed
#print axioms DiophantineConsistency.Sign14Positive74ObjectCompilerConstant.compiled_constant

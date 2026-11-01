import DiophantineConsistency.IPRANativeEquationSpecialize
/-! Intuitionistic term-vector instances of native composition, projection,
primitive recursion base and step equations. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRADefiningInstances
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRANativeEquationSpecialize
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem composition_instance {m n : ℕ} (f : Code m) (g : Codes n m)
    (v : Fin n → SyntacticTerm language) (Γ : List (Propositionᵢ language))
    (h : Γ ⊢[(𝗜𝗻𝘁¹ : Hilbertᵢ language)] Rewriting.emb (compositionEquationI f g)) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (Semiterm.func (.comp f g) v)
      (Semiterm.func f (fun i => Semiterm.func (getCode g i) v)) := by
  have hs := specialize_equalClosureI (applyCode (.comp f g) (vars n))
    (applyCode f (fun i => applyCode (getCode g i) (vars n))) v Γ (by simpa [compositionEquationI] using h)
  convert hs using 1
  simp [equal, applyCode, vars, Rew.func, Function.comp_def]
theorem projection_instance {n : ℕ} (i : Fin n)
    (v : Fin n → SyntacticTerm language) (Γ : List (Propositionᵢ language))
    (h : Γ ⊢[(𝗜𝗻𝘁¹ : Hilbertᵢ language)] Rewriting.emb (projectionEquationI i)) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (Semiterm.func (.proj i) v) (v i) := by
  have hs := specialize_equalClosureI (applyCode (.proj i) (vars n)) (#i) v Γ
    (by simpa [projectionEquationI] using h)
  convert hs using 1
  simp [equal, applyCode, vars, Rew.func, Function.comp_def]

theorem recursion_base_instance {n : ℕ} (f : Code n) (g : Code (n+2))
    (v : Fin n → SyntacticTerm language) (Γ : List (Propositionᵢ language))
    (h : Γ ⊢[(𝗜𝗻𝘁¹ : Hilbertᵢ language)] Rewriting.emb (recursionBaseEquationI f g)) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (Semiterm.func (.prec f g)
      (Fin.cases (.func (.zero 0) Fin.elim0) v)) (Semiterm.func f v) := by
  have hs := specialize_equalClosureI
    (applyCode (.prec f g) (Fin.cases (applyCode (.zero 0) Fin.elim0) (vars n)))
    (applyCode f (vars n)) v Γ (by simpa [recursionBaseEquationI] using h)
  convert hs using 1
  simp [equal, applyCode, vars, Rew.func, Function.comp_def]
  funext i
  cases i using Fin.cases with
  | zero => simp [Rew.func, Function.comp_def]; funext j; exact Fin.elim0 j
  | succ i => rfl
theorem recursion_step_instance {n : ℕ} (f : Code n) (g : Code (n+2))
    (v : Fin (n+1) → SyntacticTerm language) (Γ : List (Propositionᵢ language))
    (h : Γ ⊢[(𝗜𝗻𝘁¹ : Hilbertᵢ language)] Rewriting.emb (recursionStepEquationI f g)) :
    Γ ⊢[𝗜𝗻𝘁¹] equal
      (Semiterm.func (.prec f g) (Fin.cases (Semiterm.func .succ (fun _ => v 0)) (fun i => v i.succ)))
      (Semiterm.func g (Fin.cases (v 0) (Fin.cases (Semiterm.func (.prec f g) v) (fun i => v i.succ)))) := by
  let params : Fin n → TermN (n+1) := fun i => .bvar i.succ
  let counter : TermN (n+1) := .bvar 0
  let previous := applyCode (.prec f g) (Fin.cases counter params)
  have hs := specialize_equalClosureI
    (applyCode (.prec f g) (Fin.cases (applyCode .succ (fun _ => counter)) params))
    (applyCode g (Fin.cases counter (Fin.cases previous params))) v Γ
    (by simpa [recursionStepEquationI, params, counter, previous] using h)
  convert hs using 1
  simp [equal, applyCode, params, counter, previous, Rew.func, Function.comp_def]
  constructor
  · funext i
    cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]
    | succ i => rfl
  · funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases with
      | zero =>
        change Semiterm.func (L := language) (Code.prec f g) v =
          Rew.subst v (Rew.emb (Semiterm.func (L := language) (Code.prec f g) (Fin.cases #0 (fun i => #i.succ))))
        simp [Rew.func, Function.comp_def]
        funext j
        cases j using Fin.cases <;> rfl
      | succ i => rfl
end DiophantineConsistency.IPRADefiningInstances

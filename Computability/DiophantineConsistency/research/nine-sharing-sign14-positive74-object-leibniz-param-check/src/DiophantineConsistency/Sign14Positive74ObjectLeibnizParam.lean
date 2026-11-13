import DiophantineConsistency.Sign14Positive74ObjectLeibnizNative

/-! SOURCE-ONLY: parameterized one-coordinate syntactic substitution. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectLeibnizParam
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory

theorem left_rewrite {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (x y : Term language ℕ) (v : Fin n → Term language ℕ) :
    Rew.embSubsts (Fin.cons x (Fin.cons y v)) ▹ eqLeft φ =
      Rew.embSubsts (Fin.cons x v) ▹ φ := by
  have hrew : (Rew.embSubsts (Fin.cons x (Fin.cons y v))).comp
      (Rew.subst (Fin.cases #0 (fun i : Fin n => #i.succ.succ))) =
      Rew.embSubsts (Fin.cons x v) := by
    ext i
    · cases i using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => simp [Rew.comp_app]
    · exact Empty.elim i
  simpa only [eqLeft, ← TransitiveRewriting.comp_app, hrew]

theorem right_rewrite {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (x y : Term language ℕ) (v : Fin n → Term language ℕ) :
    Rew.embSubsts (Fin.cons x (Fin.cons y v)) ▹ eqRight φ =
      Rew.embSubsts (Fin.cons y v) ▹ φ := by
  have hrew : (Rew.embSubsts (Fin.cons x (Fin.cons y v))).comp
      (Rew.subst (Fin.cases #1 (fun i : Fin n => #i.succ.succ))) =
      Rew.embSubsts (Fin.cons y v) := by
    ext i
    · cases i using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => simp [Rew.comp_app]
    · exact Empty.elim i
  simpa only [eqRight, ← TransitiveRewriting.comp_app, hrew]
end DiophantineConsistency.Sign14Positive74ObjectLeibnizParam
#print axioms DiophantineConsistency.Sign14Positive74ObjectLeibnizParam.left_rewrite
#print axioms DiophantineConsistency.Sign14Positive74ObjectLeibnizParam.right_rewrite

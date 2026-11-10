import DiophantineConsistency.Sign14Positive74ObjectCoordinateElim

/-! SOURCE-ONLY: one-coordinate substitution rewrite identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectLeibnizRewrite
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory

theorem left_rewrite (φ : Semisentenceᵢ language 1) (x y : Term language ℕ) :
    Rew.embSubsts ![x,y] ▹ eqLeft φ = Rew.embSubsts ![x] ▹ φ := by
  have hrew : (Rew.embSubsts ![x,y]).comp
      (Rew.subst (Fin.cases #0 (fun i : Fin 0 => #i.succ.succ))) = Rew.embSubsts ![x] := by
    ext i
    · cases i using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => exact Fin.elim0 i
    · exact Empty.elim i
  simpa only [eqLeft, ← TransitiveRewriting.comp_app, hrew]

theorem right_rewrite (φ : Semisentenceᵢ language 1) (x y : Term language ℕ) :
    Rew.embSubsts ![x,y] ▹ eqRight φ = Rew.embSubsts ![y] ▹ φ := by
  have hrew : (Rew.embSubsts ![x,y]).comp
      (Rew.subst (Fin.cases #1 (fun i : Fin 0 => #i.succ.succ))) = Rew.embSubsts ![y] := by
    ext i
    · cases i using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => exact Fin.elim0 i
    · exact Empty.elim i
  simpa only [eqRight, ← TransitiveRewriting.comp_app, hrew]
end DiophantineConsistency.Sign14Positive74ObjectLeibnizRewrite
#print axioms DiophantineConsistency.Sign14Positive74ObjectLeibnizRewrite.left_rewrite
#print axioms DiophantineConsistency.Sign14Positive74ObjectLeibnizRewrite.right_rewrite

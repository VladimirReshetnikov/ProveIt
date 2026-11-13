module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedInductionRules
@[expose] public section

/-! The translated zero instance supplies the genuine ordinal-induction base,
with the whole proof context and every occurring free parameter shifted. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] formula value Ordinal.domain Ordinal.zero
set_option maxHeartbeats 800000

def inductionTranslatedShift {Γ : List Form} (p : SourceFormula 0)
    (f : Nat → Term 0) (h : ND.Proof Γ (formula p Fin.elim0 f)) :
    ND.Proof (shifted Γ) (formula p Fin.elim0 (freeShiftEnv f)) := by
  convert shiftProof h using 1
  simp only [Semiformula.shift,Rewriting.shift,app_eq_rewAux,formula_rew]
  apply formula_env_ext
  · intro i; exact Fin.elim0 i
  · intro i; rfl

theorem inductionPredicate_free (p : SourceFormula 1) (f : Nat → Term 0) :
    (inductionPredicate p f).free = formula p (fun _ => .fvar 0) (freeShiftEnv f) := by
  simp only [inductionPredicate,Semiformula.free,Rewriting.free,app_eq_rewAux,formula_rew]
  apply formula_env_ext
  · intro i; rfl
  · intro i
    cases hf : f i with
    | bvar j => nomatch j
    | func fn _ => nomatch fn
    | fvar k => simp only [shiftEnv,freeShiftEnv,hf]; rfl

def interpretedInductionBase {Γ : List Form} (A : SubstitutionPremises Γ)
    (p : SourceFormula 1) (f : Nat → Term 0)
    (H : InductionParameterCoverage Γ p f)
    (hb : ND.Proof Γ (formula (Semiformula.rewAux (Rew.subst ![Presentation.zero]) p)
      Fin.elim0 f)) : ND.Proof Γ (Ordinal.inductionBase (inductionPredicate p f)) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have out : ND.Proof (shifted Γ) (d 🡒 formula p (fun _ => .fvar 0) (freeShiftEnv f)) := by
    apply impIntro
    have hd : ND.Proof (d::shifted Γ) d := assumption (by simp)
    exact interpretedInductionZero (A.shift.up d) p (freeShiftEnv f) (.fvar 0)
      (H.shift.up d) (andLeft hd) (andRight hd)
      (up (inductionTranslatedShift _ f hb) d)
  convert out using 1
  simp only [Ordinal.inductionBase,Semiformula.free,Rewriting.free,app_eq_rewAux,
    Semiformula.imp_eq,Semiformula.neg_eq,Semiformula.rewAux,rew_neg,
    Ordinal.domain_rew,Ordinal.zero_rew]
  rw [show Semiformula.rewAux Rew.free (inductionPredicate p f) =
    formula p (fun _ => .fvar 0) (freeShiftEnv f) from inductionPredicate_free p f]
  rfl

#print axioms inductionTranslatedShift
#print axioms inductionPredicate_free
#print axioms interpretedInductionBase
end M6.PA.ForwardRelational

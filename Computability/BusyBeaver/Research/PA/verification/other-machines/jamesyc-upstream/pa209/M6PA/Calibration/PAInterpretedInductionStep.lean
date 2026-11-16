module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedInductionBase
@[expose] public section

/-! The literal translated source step supplies the full ordinal successor
step, using an actual raw successor value rather than syntactic substitution. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] formula value Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000

def sourceInductionStep (p : SourceFormula 1) : SourceFormula 0 :=
  .all (Presentation.implies p
    (Semiformula.rewAux (Rew.subst ![Presentation.succ (.bvar (0 : Fin 1))]) p))

def interpretedInductionStepAt {Γ : List Form} (A : SubstitutionPremises Γ)
    (p : SourceFormula 1) (f : Nat → Term 0) (a c : Term 0)
    (H : InductionParameterCoverage Γ p f)
    (ha : ND.Proof Γ (Ordinal.domain a)) (hc : ND.Proof Γ (Ordinal.domain c))
    (hs : ND.Proof Γ (Ordinal.successor a c))
    (hstep : ND.Proof Γ (formula (sourceInductionStep p) Fin.elim0 f))
    (hp : ND.Proof Γ (formula p (fun _ => a) f)) :
    ND.Proof Γ (formula p (fun _ => c) f) := by
  have hi := inductionAllElim _ f a hstep ha
  rw [inductionFormula_implies] at hi
  exact interpretedInductionSuccessor A p f a c H ha hc hs (mp hp hi)

def interpretedInductionStep {Γ : List Form} (A : SubstitutionPremises Γ)
    (p : SourceFormula 1) (f : Nat → Term 0)
    (H : InductionParameterCoverage Γ p f)
    (hstep : ND.Proof Γ (formula (sourceInductionStep p) Fin.elim0 f)) :
    ND.Proof Γ (Ordinal.inductionStep (inductionPredicate p f)) := by
  apply allIntro
  apply allIntro
  let fs := freeShiftEnv (freeShiftEnv f)
  let d : Form := Ordinal.domain (.fvar 1) ⋏ (Ordinal.domain (.fvar 0) ⋏
    (Ordinal.successor (.fvar 1) (.fvar 0) ⋏ formula p (fun _ => .fvar 1) fs))
  have out : ND.Proof (shifted (shifted Γ)) (d 🡒 formula p (fun _ => .fvar 0) fs) := by
    apply impIntro
    have hd : ND.Proof (d::shifted (shifted Γ)) d := assumption (by simp)
    exact interpretedInductionStepAt (A.shift.shift.up d) p fs (.fvar 1) (.fvar 0)
      (H.shift.shift.up d) (andLeft hd) (andLeft (andRight hd))
      (andLeft (andRight (andRight hd)))
      (up (inductionTranslatedShift _ (freeShiftEnv f) (inductionTranslatedShift _ f hstep)) d)
      (andRight (andRight (andRight hd)))
  convert out using 1
  simp only [Ordinal.inductionStep,Ordinal.traceProperty,inductionPredicate,
    Semiformula.free,Rewriting.free,app_eq_rewAux,Semiformula.imp_eq,
    Semiformula.neg_eq,Semiformula.rewAux,rew_neg,Ordinal.domain_rew,
    Ordinal.successor_rew,formula_rew]
  simp only [d,fs,freeShiftEnv,shiftEnv,Rew.comp_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  finishSourceSyntax
  all_goals
    first | apply congrArg (fun q : Form => q.neg) | skip
    apply formula_env_ext
    · intro i; rfl
    · intro i
      cases hf : f i with
      | bvar j => nomatch j
      | func fn _ => nomatch fn
      | fvar k => simp only [freeShiftEnv,hf]; rfl

#print axioms interpretedInductionStepAt
#print axioms interpretedInductionStep
end M6.PA.ForwardRelational

module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedInductionBase
@[expose] public section

/-! The source existential rule uses a real value of the substituted arithmetic
term. Totality and finite domain guards are retained, not replaced by raw
source-to-target term substitution. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] formula value Ordinal.domain
set_option maxHeartbeats 800000

def interpretedExistsAt {Γ : List Form} (p : SourceFormula 1) (f : Nat → Term 0)
    (a : Term 0) (ha : ND.Proof Γ (Ordinal.domain a))
    (hp : ND.Proof Γ (formula p (fun _ => a) f)) :
    ND.Proof Γ (formula (.exs p) Fin.elim0 f) := by
  rw [formula]
  apply exsIntro _ a
  convert andIntro ha hp using 1
  simp only [app_eq_rewAux,Semiformula.rewAux,Ordinal.domain_rew,formula_rew]
  congr 2
  · funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  · funext i
    cases hf : f i with
    | bvar j => nomatch j
    | func fn _ => nomatch fn
    | fvar k => simp only [shiftEnv,hf]; rfl

def interpretedExistsValue {Γ : List Form} (A : SubstitutionPremises Γ)
    (p : SourceFormula 1) (t : SourceTerm 0) (f : Nat → Term 0) (a : Term 0)
    (H : InductionParameterCoverage Γ p f)
    (Ht : EnvironmentCoverage Γ Fin.elim0 f t)
    (ha : ND.Proof Γ (value t Fin.elim0 f a))
    (hp : ND.Proof Γ (formula (Semiformula.rewAux (Rew.subst ![t]) p) Fin.elim0 f)) :
    ND.Proof Γ (formula (.exs p) Fin.elim0 f) :=
  interpretedExistsAt p f a (valueDomain t Fin.elim0 f a ha)
    (mp hp (andLeft (inductionSubstitution A p t Fin.elim0 f a H Ht ha)))

def interpretedExistsRule {Γ : List Form} (A : SubstitutionPremises Γ)
    (p : SourceFormula 1) (t : SourceTerm 0) (f : Nat → Term 0)
    (H : InductionParameterCoverage Γ p f)
    (Ht : EnvironmentCoverage Γ Fin.elim0 f t)
    (hp : ND.Proof Γ (formula (Semiformula.rewAux (Rew.subst ![t]) p) Fin.elim0 f)) :
    ND.Proof Γ (formula (.exs p) Fin.elim0 f) := by
  apply valueElim t Fin.elim0 f _ (termTotality A.totality t Fin.elim0 f Ht)
  have he : freeShiftEnv (Fin.elim0 : Fin 0 → Term 0) = Fin.elim0 := by
    funext i; exact Fin.elim0 i
  let d := value t Fin.elim0 (freeShiftEnv f) (.fvar 0)
  have hv : ND.Proof (d::shifted Γ) d := assumption (by simp)
  have ht' : EnvironmentCoverage (d::shifted Γ) Fin.elim0 (freeShiftEnv f) t := by
    simpa only [he] using (EnvironmentCoverage.shift t Ht).up t d
  have out := interpretedExistsValue (A.shift.up d) p t (freeShiftEnv f) (.fvar 0)
    (H.shift.up d) ht' hv (up (inductionTranslatedShift _ f hp) d)
  simp only [he]
  convert out using 1
  simp only [Semiformula.shift,Rewriting.shift,app_eq_rewAux,formula_rew]
  apply formula_env_ext
  · intro i; exact Fin.elim0 i
  · intro i; rfl

#print axioms interpretedExistsAt
#print axioms interpretedExistsValue
#print axioms interpretedExistsRule
end M6.PA.ForwardRelational

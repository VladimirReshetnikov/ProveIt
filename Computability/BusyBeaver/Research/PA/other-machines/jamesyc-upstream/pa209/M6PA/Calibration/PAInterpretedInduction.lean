module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedInductionStep
public import M6PA.Calibration.RelationalOrdinalInductionUniform
@[expose] public section

/-! Uniform typed interpretation of the actual PAeq induction schema.
All occurring free parameters have explicit finite domain coverage; exact
Separation for the negated interpreted predicate remains an actual premise.
This is not an internal numerical proof-code transformer. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] formula value Ordinal.domain
set_option maxHeartbeats 800000

def interpretedInductionConclusion {Γ : List Form} (A : SubstitutionPremises Γ)
    (p : SourceFormula 1) (f : Nat → Term 0)
    (H : InductionParameterCoverage Γ p f)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hadj : ND.Proof Γ adjunctionFormula)
    (hsep : ND.Proof Γ (separationFormula (∼inductionPredicate p f)))
    (hb : ND.Proof Γ (formula (Semiformula.rewAux (Rew.subst ![Presentation.zero]) p)
      Fin.elim0 f))
    (hs : ND.Proof Γ (formula (sourceInductionStep p) Fin.elim0 f)) :
    ND.Proof Γ (formula (.all p) Fin.elim0 f) := by
  rw [inductionPredicate_conclusion]
  exact Ordinal.uniformInduction A.coherence.equality.core (inductionPredicate p f)
    A.coherence.equality.transitive hi hadj hsep
    (interpretedInductionBase A p f H hb) (interpretedInductionStep A p f H hs)

def interpretedInduction {Γ : List Form} (A : SubstitutionPremises Γ)
    (p : SourceFormula 1) (f : Nat → Term 0)
    (H : InductionParameterCoverage Γ p f)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hadj : ND.Proof Γ adjunctionFormula)
    (hsep : ND.Proof Γ (separationFormula (∼inductionPredicate p f))) :
    ND.Proof Γ (formula (Presentation.inductionFormula p) Fin.elim0 f) := by
  rw [Presentation.inductionFormula,inductionFormula_implies,inductionFormula_implies]
  apply impIntro
  apply impIntro
  let b : Form := formula (Semiformula.rewAux (Rew.subst ![Presentation.zero]) p) Fin.elim0 f
  let s : Form := formula (sourceInductionStep p) Fin.elim0 f
  exact interpretedInductionConclusion ((A.up b).up s) p f ((H.up b).up s)
    (up (up hi b) s) (up (up hadj b) s) (up (up hsep b) s)
    (assumption (by simp [b,s])) (assumption (by simp [b,s]))

#print axioms interpretedInductionConclusion
#print axioms interpretedInduction
end M6.PA.ForwardRelational

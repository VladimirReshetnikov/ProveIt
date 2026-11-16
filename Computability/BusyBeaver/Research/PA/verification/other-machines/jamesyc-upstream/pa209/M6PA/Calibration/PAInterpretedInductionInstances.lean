module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedInductionSubstitution
public import M6PA.Calibration.PAPresentationAxioms
@[expose] public section

/-! The genuine zero and raw-successor instances used by interpreted induction.
All arithmetic value witnesses and finite free-parameter guards remain explicit. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] formula value Ordinal.domain Ordinal.zero Ordinal.successor
set_option maxHeartbeats 800000

def interpretedInductionZero {Γ : List Form} (A : SubstitutionPremises Γ)
    (p : SourceFormula 1) (f : Nat → Term 0) (a : Term 0)
    (H : InductionParameterCoverage Γ p f)
    (hd : ND.Proof Γ (Ordinal.domain a)) (hz : ND.Proof Γ (Ordinal.zero a))
    (hb : ND.Proof Γ (formula (Semiformula.rewAux (Rew.subst ![Presentation.zero]) p)
      Fin.elim0 f)) : ND.Proof Γ (formula p (fun _ => a) f) := by
  have hv : ND.Proof Γ (value Presentation.zero Fin.elim0 f a) := by
    rw [value_zero]; exact andIntro hd hz
  exact mp hb (andLeft (inductionSubstitution A p Presentation.zero Fin.elim0 f a H
    (fun i => Fin.elim0 i) hv))

def interpretedInductionSuccessor {Γ : List Form} (A : SubstitutionPremises Γ)
    (p : SourceFormula 1) (f : Nat → Term 0) (a c : Term 0)
    (H : InductionParameterCoverage Γ p f)
    (ha : ND.Proof Γ (Ordinal.domain a)) (hc : ND.Proof Γ (Ordinal.domain c))
    (hs : ND.Proof Γ (Ordinal.successor a c))
    (hb : ND.Proof Γ (formula (Semiformula.rewAux
      (Rew.subst ![Presentation.succ (.bvar (0 : Fin 1))]) p) (fun _ => a) f)) :
    ND.Proof Γ (formula p (fun _ => c) f) := by
  have hv : ND.Proof Γ (value (.bvar 0) (fun _ : Fin 1 => a) f a) := by
    rw [value_bvar]; exact andIntro ha (A.coherence.equality.reflexive a)
  have hvs := successorValueIntro (.bvar 0) (fun _ : Fin 1 => a) f a c hv hc hs
  exact mp hb (andLeft (inductionSubstitution A p (Presentation.succ (.bvar 0))
    (fun _ => a) f c H (Fin.cases ha (fun j => Fin.elim0 j)) hvs))

#print axioms interpretedInductionZero
#print axioms interpretedInductionSuccessor
end M6.PA.ForwardRelational

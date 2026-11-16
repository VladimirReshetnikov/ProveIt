module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedLK
@[expose] public section

/-! Finite-context transport of actual arithmetic ND/LK derivations. Every
translated source premise is a supplied target proof; no theory membership
witness is extracted and no axiom image is silently assumed. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def interpretedPremiseSupply (ps : List (SourceFormula 0)) (f : Nat → Term 0)
    {C : List Form} (h : ∀ p,p∈ps→ND.Proof C (formula p Fin.elim0 f))
    (q : SourceFormula 0) (hq : q∈ps.map Semiformula.neg) :
    ND.Proof C (∼formula q Fin.elim0 f) := by
  cases ps with
  | nil => exact False.elim (List.not_mem_nil hq)
  | cons p ps =>
    by_cases he : q=p.neg
    · subst q
      simpa only [Semiformula.neg_eq,formula_neg,Semiformula.neg_neg] using h p (by simp)
    · exact interpretedPremiseSupply ps f (fun p hp => h p (List.mem_cons_of_mem _ hp)) q
        ((List.mem_cons.mp hq).resolve_left he)

def interpretedND {C : List Form} (ps : List (SourceFormula 0)) (p : SourceFormula 0)
    (d : Presentation.ND.Proof ps p) (f : Nat → Term 0)
    (A : SubstitutionPremises C) (H : DomainEnvironment C f)
    (h : ∀ q,q∈ps→ND.Proof C (formula q Fin.elim0 f)) :
    ND.Proof C (formula p Fin.elim0 f) := by
  apply (interpretedLK d).positive f A H
  intro q hq
  exact interpretedPremiseSupply ps f h q (by simpa only [Presentation.ND.negatives,Multiset.mem_coe] using hq)

#print axioms interpretedPremiseSupply
#print axioms interpretedND
end M6.PA.ForwardRelational


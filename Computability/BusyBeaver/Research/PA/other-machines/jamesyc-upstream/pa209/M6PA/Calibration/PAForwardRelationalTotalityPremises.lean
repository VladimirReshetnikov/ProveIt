module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalArithmeticClosure
public import M6PA.Calibration.PAForwardRelationalTotalityRewriting
public import M6PA.Calibration.RelationalMultiplicationClosedResult
@[expose] public section

/-! Explicit closed ND hypotheses for structural value totality. Their actual
suppliers are separate, with budgets preserved. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] Ordinal.domain Ordinal.zero Ordinal.successor
  PairGraph.addResult PairGraph.mulResult

macro "totalitySyntax" : tactic => `(tactic|
  (simp only [Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,
    Rewriting.subst,app_eq_rewAux,Semiformula.rewAux,Semiformula.imp_eq,
    Semiformula.neg_eq,rew_neg,
    Ordinal.domain_rew,Ordinal.zero_rew,Ordinal.successor_rew,
    PairGraph.addResult_rew,PairGraph.mulResult_rew,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ];
   try simp;
   finishSourceSyntax))

structure TotalityPremises (Γ : List Form) where
  reflexive : ND.Proof Γ reflexivityFormula
  zero : ND.Proof Γ zeroInhabited
  successor : ND.Proof Γ successorClosed
  addition : ND.Proof Γ PairGraph.addClosedResult
  multiplication : ND.Proof Γ PairGraph.mulClosedResult

def TotalityPremises.up {Γ : List Form} (h : TotalityPremises Γ) (p : Form) :
    TotalityPremises (p :: Γ) where
  reflexive := ND.up h.reflexive p
  zero := ND.up h.zero p
  successor := ND.up h.successor p
  addition := ND.up h.addition p
  multiplication := ND.up h.multiplication p

def TotalityPremises.shift {Γ : List Form} (h : TotalityPremises Γ) :
    TotalityPremises (shifted Γ) where
  reflexive := by convert shiftProof h.reflexive using 1; equalitySyntax
  zero := by
    convert shiftProof h.zero using 1
    simp only [zeroInhabited]
    totalitySyntax
  successor := by
    convert shiftProof h.successor using 1
    simp only [successorClosed,closeParameter,Ordinal.domainSuccessorStatement,
      Ordinal.domainSuccessorExists]
    totalitySyntax
  addition := by
    convert shiftProof h.addition using 1
    simp only [PairGraph.addClosedResult,closeParameter,PairGraph.addTotalStatement,
      PairGraph.addOutputConclusion,PairGraph.addOutput]
    totalitySyntax
  multiplication := PairGraph.mulClosedResultShift h.multiplication

def TotalityPremises.eqRefl {Γ : List Form} (h : TotalityPremises Γ) (x : Term 0) :
    ND.Proof Γ (ND.eq x x) := by
  convert allElim _ x h.reflexive using 1
  simp only [reflexivityFormula,eqAtom,ND.eq]
  totalitySyntax

def TotalityPremises.successorAt {Γ : List Form} (h : TotalityPremises Γ)
    (x : Term 0) (hx : ND.Proof Γ (Ordinal.domain x)) :
    ND.Proof Γ (Ordinal.domainSuccessorExists x) := by
  have hh := specializeParameter (Ordinal.domainSuccessorStatement (.fvar 0)) x h.successor
  apply mp hx
  convert hh using 1
  simp only [Ordinal.domainSuccessorStatement,Ordinal.domainSuccessorExists]
  totalitySyntax

def TotalityPremises.addAt {Γ : List Form} (h : TotalityPremises Γ)
    (x y : Term 0) (hx : ND.Proof Γ (Ordinal.domain x))
    (hy : ND.Proof Γ (Ordinal.domain y)) : ND.Proof Γ (PairGraph.addOutput x y) := by
  have hh := specializeParameter (PairGraph.addTotalStatement 0) y h.addition
  have hp : ND.Proof Γ (Ordinal.domain y 🡒
      ∀¹ (Ordinal.domain (.bvar 0) 🡒 PairGraph.addOutput (.bvar 0) (Rew.bShift y))) := by
    convert hh using 1
    simp only [PairGraph.addTotalStatement,PairGraph.addOutputConclusion,PairGraph.addOutput]
    totalitySyntax
  apply mp hx
  convert allElim _ x (mp hy hp) using 1
  simp only [PairGraph.addOutput]
  totalitySyntax

def TotalityPremises.mulAt {Γ : List Form} (h : TotalityPremises Γ)
    (x y : Term 0) (hx : ND.Proof Γ (Ordinal.domain x))
    (hy : ND.Proof Γ (Ordinal.domain y)) : ND.Proof Γ (PairGraph.mulOutput x y) := by
  cases x with
  | bvar i => exact Fin.elim0 i
  | func fn _ => nomatch fn
  | fvar i =>
    cases y with
    | bvar j => exact Fin.elim0 j
    | func fn _ => nomatch fn
    | fvar j => exact PairGraph.mulClosedResultAt i j h.multiplication hx hy

#print axioms TotalityPremises.shift
#print axioms TotalityPremises.eqRefl
#print axioms TotalityPremises.successorAt
#print axioms TotalityPremises.addAt
#print axioms TotalityPremises.mulAt
end M6.PA.ForwardRelational

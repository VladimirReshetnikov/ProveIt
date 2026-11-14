import PA194FoundationOrdinalEmpty
import PA194FoundationAdjunction
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND

def successorExists (a : Term n) : Formula n :=
  ∃⁰ successor (Rew.bShift a) (.bvar 0)

/-- Specialize the two adjunction inputs to the same object. -/
def rawSuccessor {Γ : List Form} (a : Term 0)
    (d : ND.Proof Γ adjunctionFormula) : ND.Proof Γ (successorExists a) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar i =>
    have first := allElim _ (.fvar i) d
    have second := allElim _ (.fvar i) first
    convert second using 1 ;
      simp only [successorExists,successor,memAtom,eqAtom,
        mem,eq,sourceIff,sourceImply,Rewriting.subst,app_eq_rewAux,
        Semiformula.rewAux,Semiformula.neg] ;
      finishSourceSyntax

def rawSuccessorDerivation (a : Term 0) :
    ND.Proof [adjunctionFormula] (successorExists a) :=
  rawSuccessor a (assumption (by simp))


#print axioms rawSuccessorDerivation
end M6.PA.RelationalSource.Ordinal

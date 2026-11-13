module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedFixedSupplier
@[expose] public section

/-! The exact twelve fixed source axioms have no free parameters. Their
ordinary source sentence closure therefore embeds back to the identical
formula; induction instances are deliberately excluded from this shortcut. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

theorem fixedAxiom_freeVariables (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) :
    p.freeVariables = ∅ := by
  simp only [Presentation.fixedAxioms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [Presentation.reflexivity,Presentation.symmetry,Presentation.transitivity,
      Presentation.succCongruence,Presentation.addCongruence,Presentation.mulCongruence,
      Presentation.addZero,Presentation.addSucc,Presentation.mulZero,Presentation.mulSucc,
      Presentation.zeroNotSucc,Presentation.succInjective,Presentation.eq,Presentation.implies,
      Presentation.zero,Presentation.succ,Presentation.add,Presentation.mul,
      Semiformula.freeVariables,←Semiformula.neg_eq,Semiterm.freeVariables_func,Fin.univ_succ]

theorem fixedAxiom_univCl (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) :
    (Rewriting.emb p.univCl : SourceFormula 0) = p := by
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of p (fixedAxiom_freeVariables p hp)

def interpretedFixedSentence {Γ : List Form} (I : FixedImagePremises Γ)
    (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) (f : Nat → Term 0) :
    ND.Proof Γ (formula (Rewriting.emb p.univCl : SourceFormula 0) Fin.elim0 f) := by
  rw [fixedAxiom_univCl p hp]
  exact interpretedFixedAxiom I p hp f

#print axioms fixedAxiom_freeVariables
#print axioms fixedAxiom_univCl
#print axioms interpretedFixedSentence
end M6.PA.ForwardRelational


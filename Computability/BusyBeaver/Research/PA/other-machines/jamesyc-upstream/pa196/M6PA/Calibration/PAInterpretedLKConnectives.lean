module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedLKPropositional
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def interpretedRefutesAnd {Γ : LK.Sequent Presentation.language} {p q : SourceFormula 0}
    (d : InterpretedRefutes (Γ+⦃p⦄)) (e : InterpretedRefutes (Γ+⦃q⦄)) :
    InterpretedRefutes (Γ+⦃Semiformula.and p q⦄) := by
  intro f C A H h
  have hp := d.positive f A H (fun r hr => h r (Multiset.mem_add.mpr (Or.inl hr)))
  have hq := e.positive f A H (fun r hr => h r (Multiset.mem_add.mpr (Or.inl hr)))
  exact contradiction (andIntro hp hq) (h (Semiformula.and p q) (by simp))

def interpretedRefutesOr {Γ : LK.Sequent Presentation.language} {p q : SourceFormula 0}
    (d : InterpretedRefutes (Γ+⦃p,q⦄)) : InterpretedRefutes (Γ+⦃Semiformula.or p q⦄) := by
  intro f C A H h
  have hn : ND.Proof C ((∼formula p Fin.elim0 f) ⋏ (∼formula q Fin.elim0 f)) := h (Semiformula.or p q) (by simp)
  apply d f A H
  intro r hr
  by_cases hp : r=p
  · subst r; exact andLeft hn
  by_cases hq : r=q
  · subst r; exact andRight hn
  exact h r (Multiset.mem_add.mpr (Or.inl (by simpa [hp,hq] using hr)))

/-- Domain-covered environments supply every finite occurrence guard needed
by the existential rule. This stronger host family is explicit, not encoded. -/
def interpretedRefutesExists {Γ : LK.Sequent Presentation.language}
    (p : SourceFormula 1) (t : SourceTerm 0)
    (d : InterpretedRefutes (Γ+⦃p/[t]⦄)) : InterpretedRefutes (Γ+⦃Semiformula.exs p⦄) := by
  intro f C A H h
  have hp := d.positive f A H (fun r hr => h r (Multiset.mem_add.mpr (Or.inl hr)))
  have ht : EnvironmentCoverage C Fin.elim0 f t :=
    coverageFromFamilies t Fin.elim0 f (fun i => Fin.elim0 i) H
  have hex := interpretedExistsRule A p t f (fun i _ => H i) ht hp
  exact contradiction hex (h (Semiformula.exs p) (by simp))

#print axioms interpretedRefutesAnd
#print axioms interpretedRefutesOr
#print axioms interpretedRefutesExists
end M6.PA.ForwardRelational

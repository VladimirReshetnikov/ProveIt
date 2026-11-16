module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLiftOrdinal
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder ND

theorem lift_closed_shift (p : RelationalSource.ND.Form) (hp : p.freeVariables=∅) :
    (liftFormula p).shift=liftFormula p := by
  change Rewriting.shift (liftFormula p)=liftFormula p
  apply Semiformula.rew_eq_self_of
  · intro i; exact Fin.elim0 i
  · intro i hi
    simp [Semiformula.FVar?,liftFormula,hp] at hi

def EqualityProofs.shift {Γ : List ND.Form} (e : EqualityProofs Γ) : EqualityProofs (shifted Γ) where
  reflexive := by
    simpa only [lift_closed_shift RelationalSource.reflexivityFormula (by simp [Finset.ext_iff,Fin.exists_fin_two,Semiformula.freeVariables,Semiterm.freeVariables,RelationalSource.reflexivityFormula,RelationalSource.eqAtom])] using ND.shiftProof e.reflexive
  symmetric := by
    simpa only [lift_closed_shift RelationalSource.symmetryFormula (by simp [Finset.ext_iff,Fin.exists_fin_two,Semiformula.freeVariables,Semiterm.freeVariables,RelationalSource.symmetryFormula,RelationalSource.eqAtom,RelationalSource.notEqAtom])] using ND.shiftProof e.symmetric
  congruent := by
    simpa only [lift_closed_shift RelationalSource.congruenceFormula (by simp [Finset.ext_iff,Fin.exists_fin_two,Semiformula.freeVariables,Semiterm.freeVariables,RelationalSource.congruenceFormula,RelationalSource.eqAtom,RelationalSource.notEqAtom,RelationalSource.memAtom,RelationalSource.notMemAtom])] using ND.shiftProof e.congruent

def eqRefl {Γ : List ND.Form} (e : EqualityProofs Γ) (i : Nat)
    : ND.Proof Γ (eq (.fvar i) (.fvar i)) := by
  have d : RelationalSource.ND.Proof [(RelationalSource.reflexivityFormula),(RelationalSource.symmetryFormula),(RelationalSource.congruenceFormula)] (RelationalSource.ND.eq (.fvar i) (.fvar i)) :=
    RelationalSource.Ordinal.eqRefl ⟨RelationalSource.ND.assumption (by simp),RelationalSource.ND.assumption (by simp),RelationalSource.ND.assumption (by simp)⟩ i 
  have out := liftInto (Δ:=Γ) d (by
    intro q hq
    by_cases h0 : q=(RelationalSource.reflexivityFormula)
    · subst q
      simpa [liftTerm,Semiterm.lMap] using e.reflexive
    by_cases h1 : q=(RelationalSource.symmetryFormula)
    · subst q
      simpa [liftTerm,Semiterm.lMap] using e.symmetric
    by_cases h2 : q=(RelationalSource.congruenceFormula)
    · subst q
      simpa [liftTerm,Semiterm.lMap] using e.congruent
    · simp_all)
  simpa [liftTerm,Semiterm.lMap] using out

def eqSymm {Γ : List ND.Form} (e : EqualityProofs Γ) (i j : Nat)
    (h : ND.Proof Γ (eq (.fvar i) (.fvar j)))
    : ND.Proof Γ (eq (.fvar j) (.fvar i)) := by
  have d : RelationalSource.ND.Proof [(RelationalSource.reflexivityFormula),(RelationalSource.symmetryFormula),(RelationalSource.congruenceFormula),(RelationalSource.ND.eq (.fvar i) (.fvar j))] (RelationalSource.ND.eq (.fvar j) (.fvar i)) :=
    RelationalSource.Ordinal.eqSymm ⟨RelationalSource.ND.assumption (by simp),RelationalSource.ND.assumption (by simp),RelationalSource.ND.assumption (by simp)⟩ i j (RelationalSource.ND.assumption (by simp))
  have out := liftInto (Δ:=Γ) d (by
    intro q hq
    by_cases h0 : q=(RelationalSource.reflexivityFormula)
    · subst q
      simpa [liftTerm,Semiterm.lMap] using e.reflexive
    by_cases h1 : q=(RelationalSource.symmetryFormula)
    · subst q
      simpa [liftTerm,Semiterm.lMap] using e.symmetric
    by_cases h2 : q=(RelationalSource.congruenceFormula)
    · subst q
      simpa [liftTerm,Semiterm.lMap] using e.congruent
    by_cases h3 : q=(RelationalSource.ND.eq (.fvar i) (.fvar j))
    · subst q
      simpa [liftTerm,Semiterm.lMap] using h
    · simp_all)
  simpa [liftTerm,Semiterm.lMap] using out


#print axioms EqualityProofs.shift
#print axioms eqRefl
#print axioms eqSymm
end M6.PA.RelationalPredicateTemplate.Ordinal

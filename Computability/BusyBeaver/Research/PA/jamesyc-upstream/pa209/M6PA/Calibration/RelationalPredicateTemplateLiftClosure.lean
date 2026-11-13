module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLiftOrdinal
public import M6PA.Calibration.RelationalOrdinalSuccessorBase
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder ND

def leastExists (s : Term n) : Formula n := ∃¹ least (Rew.bShift s) (.bvar 0)
def greatestExists (s : Term n) : Formula n := ∃¹ greatest (Rew.bShift s) (.bvar 0)
def successorExists (s : Term n) : Formula n := ∃¹ successor (Rew.bShift s) (.bvar 0)

@[simp] theorem lift_leastExists {n : Nat} (a : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.leastExists a)=leastExists (liftTerm a) := by
  simp [RelationalSource.Ordinal.leastExists,leastExists]

@[simp] theorem lift_greatestExists {n : Nat} (a : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.greatestExists a)=greatestExists (liftTerm a) := by
  simp [RelationalSource.Ordinal.greatestExists,greatestExists]

@[simp] theorem lift_successorExists {n : Nat} (a : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.successorExists a)=successorExists (liftTerm a) := by
  simp [RelationalSource.Ordinal.successorExists,successorExists]
def domainGreatest {Γ : List ND.Form} (b : Nat)
    (hb : ND.Proof Γ (domain (.fvar b)))
    (hn : ND.Proof Γ (nonempty (.fvar b)))
    : ND.Proof Γ (greatestExists (.fvar b)) := by
  have d : RelationalSource.ND.Proof [(RelationalSource.Ordinal.domain (.fvar b)),(RelationalSource.Ordinal.nonempty (.fvar b))] (RelationalSource.Ordinal.greatestExists (.fvar b)) :=
    RelationalSource.Ordinal.domainGreatest b (RelationalSource.ND.assumption (by simp)) (RelationalSource.ND.assumption (by simp))
  have out := liftInto (Δ:=Γ) d (by
    intro q hq
    by_cases h0 : q=(RelationalSource.Ordinal.domain (.fvar b))
    · subst q
      simpa [liftTerm,Semiterm.lMap] using hb
    by_cases h1 : q=(RelationalSource.Ordinal.nonempty (.fvar b))
    · subst q
      simpa [liftTerm,Semiterm.lMap] using hn
    · simp_all)
  simpa [liftTerm,Semiterm.lMap] using out

def rawSuccessor {Γ : List ND.Form} (a : Term 0)
    (ha : ND.Proof Γ (liftFormula RelationalSource.adjunctionFormula))
    : ND.Proof Γ (successorExists a) := by
  have d : RelationalSource.ND.Proof [(RelationalSource.adjunctionFormula)] (RelationalSource.Ordinal.successorExists (lowerTerm a)) :=
    RelationalSource.Ordinal.rawSuccessor (lowerTerm a) (RelationalSource.ND.assumption (by simp))
  have out := liftInto (Δ:=Γ) d (by
    intro q hq
    by_cases h0 : q=(RelationalSource.adjunctionFormula)
    · subst q
      simpa [liftTerm,Semiterm.lMap] using ha
    · simp_all)
  simpa [liftTerm,Semiterm.lMap] using out

def successorDomain {Γ : List ND.Form} (e : EqualityProofs Γ) (a b : Term 0)
    (et : ND.Proof Γ (liftFormula RelationalSource.transitivityFormula))
    (hi : ND.Proof Γ (liftFormula RelationalSource.Ordinal.intersectionFormula))
    (ha : ND.Proof Γ (domain a))
    (hs : ND.Proof Γ (successor a b))
    : ND.Proof Γ (domain b) := by
  have d : RelationalSource.ND.Proof [(RelationalSource.reflexivityFormula),(RelationalSource.symmetryFormula),(RelationalSource.congruenceFormula),(RelationalSource.transitivityFormula),(RelationalSource.Ordinal.intersectionFormula),(RelationalSource.Ordinal.domain (lowerTerm a)),(RelationalSource.Ordinal.successor (lowerTerm a) (lowerTerm b))] (RelationalSource.Ordinal.domain (lowerTerm b)) :=
    RelationalSource.Ordinal.successorDomain ⟨RelationalSource.ND.assumption (by simp),RelationalSource.ND.assumption (by simp),RelationalSource.ND.assumption (by simp)⟩ (RelationalSource.ND.assumption (by simp)) (RelationalSource.ND.assumption (by simp)) (lowerTerm a) (lowerTerm b) (RelationalSource.ND.assumption (by simp)) (RelationalSource.ND.assumption (by simp))
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
    by_cases h3 : q=(RelationalSource.transitivityFormula)
    · subst q
      simpa [liftTerm,Semiterm.lMap] using et
    by_cases h4 : q=(RelationalSource.Ordinal.intersectionFormula)
    · subst q
      simpa [liftTerm,Semiterm.lMap] using hi
    by_cases h5 : q=(RelationalSource.Ordinal.domain (lowerTerm a))
    · subst q
      simpa [liftTerm,Semiterm.lMap] using ha
    by_cases h6 : q=(RelationalSource.Ordinal.successor (lowerTerm a) (lowerTerm b))
    · subst q
      simpa [liftTerm,Semiterm.lMap] using hs
    · simp_all)
  simpa [liftTerm,Semiterm.lMap] using out


#print axioms domainGreatest
#print axioms rawSuccessor
#print axioms successorDomain
end M6.PA.RelationalPredicateTemplate.Ordinal

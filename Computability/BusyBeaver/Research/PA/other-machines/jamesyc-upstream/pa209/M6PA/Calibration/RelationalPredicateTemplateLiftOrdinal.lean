module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLiftSyntax
public import M6PA.Calibration.RelationalPredicateTemplateLiftLogic
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder ND

structure EqualityProofs (Γ : List ND.Form) where
  reflexive : ND.Proof Γ (liftFormula RelationalSource.reflexivityFormula)
  symmetric : ND.Proof Γ (liftFormula RelationalSource.symmetryFormula)
  congruent : ND.Proof Γ (liftFormula RelationalSource.congruenceFormula)

def EqualityProofs.up {Γ : List ND.Form} (e : EqualityProofs Γ) (p : ND.Form) : EqualityProofs (p::Γ) where
  reflexive := ND.up e.reflexive p
  symmetric := ND.up e.symmetric p
  congruent := ND.up e.congruent p

def memberDomain {Γ : List ND.Form} (a b : Nat)
    (ha : ND.Proof Γ (domain (.fvar a)))
    (hm : ND.Proof Γ (mem (.fvar a) (.fvar b)))
    : ND.Proof Γ (domain (.fvar b)) := by
  have d : RelationalSource.ND.Proof [(RelationalSource.Ordinal.domain (.fvar a)),(RelationalSource.ND.mem (.fvar a) (.fvar b))] (RelationalSource.Ordinal.domain (.fvar b)) :=
    RelationalSource.Ordinal.memberDomain a b (RelationalSource.ND.assumption (by simp)) (RelationalSource.ND.assumption (by simp))
  have out := liftInto (Δ:=Γ) d (by
    intro q hq
    by_cases h0 : q=(RelationalSource.Ordinal.domain (.fvar a))
    · subst q
      simpa [liftTerm,Semiterm.lMap] using ha
    by_cases h1 : q=(RelationalSource.ND.mem (.fvar a) (.fvar b))
    · subst q
      simpa [liftTerm,Semiterm.lMap] using hm
    · simp_all)
  simpa [liftTerm,Semiterm.lMap] using out

def greatestSuccessor {Γ : List ND.Form} (e : EqualityProofs Γ) (b m : Nat)
    (ht : ND.Proof Γ (transitive (.fvar b)))
    (hg : ND.Proof Γ (greatest (.fvar b) (.fvar m)))
    : ND.Proof Γ (successor (.fvar m) (.fvar b)) := by
  have d : RelationalSource.ND.Proof [(RelationalSource.reflexivityFormula),(RelationalSource.symmetryFormula),(RelationalSource.congruenceFormula),(RelationalSource.Ordinal.transitive (.fvar b)),(RelationalSource.Ordinal.greatest (.fvar b) (.fvar m))] (RelationalSource.Ordinal.successor (.fvar m) (.fvar b)) :=
    RelationalSource.Ordinal.greatestSuccessor ⟨RelationalSource.ND.assumption (by simp),RelationalSource.ND.assumption (by simp),RelationalSource.ND.assumption (by simp)⟩ b m (RelationalSource.ND.assumption (by simp)) (RelationalSource.ND.assumption (by simp))
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
    by_cases h3 : q=(RelationalSource.Ordinal.transitive (.fvar b))
    · subst q
      simpa [liftTerm,Semiterm.lMap] using ht
    by_cases h4 : q=(RelationalSource.Ordinal.greatest (.fvar b) (.fvar m))
    · subst q
      simpa [liftTerm,Semiterm.lMap] using hg
    · simp_all)
  simpa [liftTerm,Semiterm.lMap] using out

def leastExcludesMember {Γ : List ND.Form} (e : EqualityProofs Γ) (c b m : Nat)
    (hb : ND.Proof Γ (domain (.fvar b)))
    (hl : ND.Proof Γ (least (.fvar c) (.fvar b)))
    (hm : ND.Proof Γ (mem (.fvar b) (.fvar m)))
    : ND.Proof Γ (∼mem (.fvar c) (.fvar m)) := by
  have d : RelationalSource.ND.Proof [(RelationalSource.reflexivityFormula),(RelationalSource.symmetryFormula),(RelationalSource.congruenceFormula),(RelationalSource.Ordinal.domain (.fvar b)),(RelationalSource.Ordinal.least (.fvar c) (.fvar b)),(RelationalSource.ND.mem (.fvar b) (.fvar m))] (∼RelationalSource.ND.mem (.fvar c) (.fvar m)) :=
    RelationalSource.Ordinal.leastExcludesMember ⟨RelationalSource.ND.assumption (by simp),RelationalSource.ND.assumption (by simp),RelationalSource.ND.assumption (by simp)⟩ c b m (RelationalSource.ND.assumption (by simp)) (RelationalSource.ND.assumption (by simp)) (RelationalSource.ND.assumption (by simp))
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
    by_cases h3 : q=(RelationalSource.Ordinal.domain (.fvar b))
    · subst q
      simpa [liftTerm,Semiterm.lMap] using hb
    by_cases h4 : q=(RelationalSource.Ordinal.least (.fvar c) (.fvar b))
    · subst q
      simpa [liftTerm,Semiterm.lMap] using hl
    by_cases h5 : q=(RelationalSource.ND.mem (.fvar b) (.fvar m))
    · subst q
      simpa [liftTerm,Semiterm.lMap] using hm
    · simp_all)
  simpa [liftTerm,Semiterm.lMap] using out

def notZeroNonempty {Γ : List ND.Form} (b : Nat)
    (h : ND.Proof Γ (∼zero (.fvar b)))
    : ND.Proof Γ (nonempty (.fvar b)) := by
  have d : RelationalSource.ND.Proof [(∼RelationalSource.Ordinal.zero (.fvar b))] (RelationalSource.Ordinal.nonempty (.fvar b)) :=
    RelationalSource.Ordinal.notZeroNonempty b (RelationalSource.ND.assumption (by simp))
  have out := liftInto (Δ:=Γ) d (by
    intro q hq
    by_cases h0 : q=(∼RelationalSource.Ordinal.zero (.fvar b))
    · subst q
      simpa [liftTerm,Semiterm.lMap] using h
    · simp_all)
  simpa [liftTerm,Semiterm.lMap] using out


#print axioms memberDomain
#print axioms greatestSuccessor
#print axioms leastExcludesMember
#print axioms notZeroNonempty
end M6.PA.RelationalPredicateTemplate.Ordinal

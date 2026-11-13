module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLiftLanguage
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalSyntax
public import M6PA.Calibration.RelationalOrdinalInductionMinimal
public import M6PA.Calibration.RelationalOrdinalSuccessorClosure
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder

@[simp] theorem lift_and {n : Nat} (p q : Semiformula RelationalSource.language Nat n) : liftFormula (p ⋏ q)=liftFormula p ⋏ liftFormula q := by simp [liftFormula]
@[simp] theorem lift_or {n : Nat} (p q : Semiformula RelationalSource.language Nat n) : liftFormula (p ⋎ q)=liftFormula p ⋎ liftFormula q := by simp [liftFormula]
@[simp] theorem lift_imp {n : Nat} (p q : Semiformula RelationalSource.language Nat n) : liftFormula (p 🡒 q)=liftFormula p 🡒 liftFormula q := by simp [liftFormula]
@[simp] theorem lift_neg {n : Nat} (p : Semiformula RelationalSource.language Nat n) : liftFormula (∼p)=∼liftFormula p := by simp [liftFormula]
@[simp] theorem lift_all {n : Nat} (p : Semiformula RelationalSource.language Nat (n+1)) : liftFormula (∀¹ p)=∀¹ liftFormula p := rfl
@[simp] theorem lift_exs {n : Nat} (p : Semiformula RelationalSource.language Nat (n+1)) : liftFormula (∃¹ p)=∃¹ liftFormula p := rfl

@[simp] theorem liftTerm_bShift {n : Nat} (t : Semiterm RelationalSource.language Nat n) :
    liftTerm (Rew.bShift t)=Rew.bShift (liftTerm t) := by
  cases t with
  | bvar i => rfl
  | fvar i => rfl
  | func f _ => nomatch f

@[simp] theorem lift_mem {n : Nat} (a b : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.ND.mem a b)=Ordinal.mem (liftTerm a) (liftTerm b) := by
  change Semiformula.rel Relation.mem (fun i => liftTerm (![b,a] i)) = Semiformula.rel Relation.mem ![liftTerm b,liftTerm a]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem lift_eq {n : Nat} (a b : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.ND.eq a b)=Ordinal.eq (liftTerm a) (liftTerm b) := by
  change Semiformula.rel Relation.eq (fun i => liftTerm (![a,b] i)) = Semiformula.rel Relation.eq ![liftTerm a,liftTerm b]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem lift_zero {n : Nat} (a : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.zero a)=Ordinal.zero (liftTerm a) := by
  simp [RelationalSource.Ordinal.zero,Ordinal.zero,RelationalSource.sourceIff,Ordinal.sourceIff,←Semiformula.neg_eq]

@[simp] theorem lift_successor {n : Nat} (a b : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.successor a b)=Ordinal.successor (liftTerm a) (liftTerm b) := by
  change (∀¹ liftFormula ((RelationalSource.ND.mem (Rew.bShift b) (.bvar 0) 🡒 (RelationalSource.ND.mem (Rew.bShift a) (.bvar 0) ⋎ RelationalSource.ND.eq (.bvar 0) (Rew.bShift a))) ⋏ ((RelationalSource.ND.mem (Rew.bShift a) (.bvar 0) ⋎ RelationalSource.ND.eq (.bvar 0) (Rew.bShift a)) 🡒 RelationalSource.ND.mem (Rew.bShift b) (.bvar 0)))) = _
  simp [Ordinal.successor,Ordinal.sourceIff]

@[simp] theorem lift_subset {n : Nat} (a b : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.subset a b)=Ordinal.subset (liftTerm a) (liftTerm b) := by
  simp [RelationalSource.Ordinal.subset,Ordinal.subset,RelationalSource.sourceIff,Ordinal.sourceIff,←Semiformula.neg_eq]

@[simp] theorem lift_transitive {n : Nat} (a : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.transitive a)=Ordinal.transitive (liftTerm a) := by
  simp [RelationalSource.Ordinal.transitive,Ordinal.transitive,RelationalSource.sourceIff,Ordinal.sourceIff,←Semiformula.neg_eq]

@[simp] theorem lift_memberTransitive {n : Nat} (a : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.memberTransitive a)=Ordinal.memberTransitive (liftTerm a) := by
  simp [RelationalSource.Ordinal.memberTransitive,Ordinal.memberTransitive,RelationalSource.sourceIff,Ordinal.sourceIff,←Semiformula.neg_eq]

@[simp] theorem lift_memberLinear {n : Nat} (a : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.memberLinear a)=Ordinal.memberLinear (liftTerm a) := by
  simp [RelationalSource.Ordinal.memberLinear,Ordinal.memberLinear,RelationalSource.sourceIff,Ordinal.sourceIff,←Semiformula.neg_eq]

@[simp] theorem lift_nonempty {n : Nat} (a : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.nonempty a)=Ordinal.nonempty (liftTerm a) := by
  simp [RelationalSource.Ordinal.nonempty,Ordinal.nonempty,RelationalSource.sourceIff,Ordinal.sourceIff,←Semiformula.neg_eq]

@[simp] theorem lift_least {n : Nat} (a b : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.least a b)=Ordinal.least (liftTerm a) (liftTerm b) := by
  simp [RelationalSource.Ordinal.least,Ordinal.least,RelationalSource.sourceIff,Ordinal.sourceIff,←Semiformula.neg_eq]

@[simp] theorem lift_greatest {n : Nat} (a b : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.greatest a b)=Ordinal.greatest (liftTerm a) (liftTerm b) := by
  simp [RelationalSource.Ordinal.greatest,Ordinal.greatest,RelationalSource.sourceIff,Ordinal.sourceIff,←Semiformula.neg_eq]

@[simp] theorem lift_internalExtrema {n : Nat} (a : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.internalExtrema a)=Ordinal.internalExtrema (liftTerm a) := by
  simp [RelationalSource.Ordinal.internalExtrema,Ordinal.internalExtrema,RelationalSource.sourceIff,Ordinal.sourceIff,←Semiformula.neg_eq]

@[simp] theorem lift_representative {n : Nat} (a : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.representative a)=Ordinal.representative (liftTerm a) := by
  simp [RelationalSource.Ordinal.representative,Ordinal.representative,RelationalSource.sourceIff,Ordinal.sourceIff,←Semiformula.neg_eq]

@[simp] theorem lift_memberIr {n : Nat} (a : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.memberIr a)=Ordinal.memberIr (liftTerm a) := by
  simp [RelationalSource.Ordinal.memberIr,Ordinal.memberIr,RelationalSource.sourceIff,Ordinal.sourceIff,←Semiformula.neg_eq]

@[simp] theorem lift_domain {n : Nat} (a : Semiterm RelationalSource.language Nat n) :
    liftFormula (RelationalSource.Ordinal.domain a)=Ordinal.domain (liftTerm a) := by
  simp [RelationalSource.Ordinal.domain,Ordinal.domain,RelationalSource.sourceIff,Ordinal.sourceIff,←Semiformula.neg_eq]

#print axioms lift_domain
#print axioms lift_successor
end M6.PA.RelationalPredicateTemplate

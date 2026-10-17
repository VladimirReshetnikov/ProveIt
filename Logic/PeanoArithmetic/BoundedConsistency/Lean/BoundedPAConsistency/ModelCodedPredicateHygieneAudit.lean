import BoundedPAConsistency.ModelCodedPredicateHygiene
open LO FirstOrder
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateHygiene

#print axioms LeanProofs.BoundedPAConsistency.ModelCodedPredicateHygiene.translateFormula_shift_heterogeneous
#print axioms LeanProofs.BoundedPAConsistency.ModelCodedPredicateHygiene.translateFormula_free_heterogeneous

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {arity n : ℕ}
example (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (p : Semiproposition (templateLanguage arity) n) :
    translateFormula S.shift (Rewriting.shift p) = (translateFormula S p).shift :=
  translateFormula_shift_heterogeneous S p
example (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (p : Semiproposition (templateLanguage arity) 1) :
    translateFormula S.shift (Rewriting.free p) = (translateFormula S p).free :=
  translateFormula_free_heterogeneous S p
example (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (p : Semiproposition (templateLanguage arity) n) :
    translateFormula S.shift.shift (Rewriting.shift p) = (translateFormula S.shift p).shift :=
  translateFormula_shift_heterogeneous S.shift p
example (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (p : Semiproposition (templateLanguage arity) 1) :
    translateFormula S.shift.shift (Rewriting.free p) = (translateFormula S.shift p).free :=
  translateFormula_free_heterogeneous S.shift p
example (p : Semiproposition (templateLanguage 1) n) :
    translateFormula ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ .fvar 17).shift (Rewriting.shift p) =
      (translateFormula ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ .fvar 17) p).shift :=
  translateFormula_shift_heterogeneous _ p
example (p : Semiproposition (templateLanguage 1) 1) :
    translateFormula ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ .fvar 17).shift (Rewriting.free p) =
      (translateFormula ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ .fvar 17) p).free :=
  translateFormula_free_heterogeneous _ p
end

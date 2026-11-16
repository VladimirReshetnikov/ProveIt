module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTargetShiftParameters
public import Foundation.FirstOrder.LK.Basic
@[expose] public section

/-! A template-only unary predicate extension. Proofs, when added, use
Foundation's existing LK datatype; the target relational language is unchanged.
The unary hole denotes a model-valued formula with one bound argument and may
have free parameters. Eigenvariable shift must shift those parameters too. -/
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
inductive Relation : Nat → Type
  | eq : Relation 2
  | mem : Relation 2
  | predicate : Relation 1
abbrev sourceLanguage : Language where
  Func := fun _ => Empty
  Rel := Relation
abbrev Term (n : Nat) := Semiterm sourceLanguage Nat n
abbrev Formula (n : Nat) := Semiformula sourceLanguage Nat n
end M6.PA.RelationalPredicateTemplate


(**
  Public facade for the foundational first-order development.

  This mirrors [Foundation/FirstOrder/Basic.lean].  [Require Export] retains
  the source module's public-import behavior, so clients can depend on one
  stable entry point while all declarations remain owned and audited by their
  focused implementation modules.
*)

From Foundation.FirstOrder.Basic.Syntax Require Export Formula.
From Foundation.Syntax.Predicate Require Export Rew.
From Foundation.FirstOrder.Basic.Semantics Require Export
  Semantics RewriteClosure OperatorSemantics ModelTheory Elementary.
From Foundation.FirstOrder.Basic Require Export
  Operator BinderNotation Model Calculus CutFree Calculus2 Coding Eq
  Soundness Padding Definability.

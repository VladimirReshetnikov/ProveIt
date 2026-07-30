/-
ANOMALY (no False): `Expr.proj` + eta-for-structures can eliminate a one-constructor
inductive into a universe in which that type's own recursor cannot eliminate.

The kernel accepts   I2 (a : Sort u) : Sort u  |  mk : a -> I2 a
(the *elaborator frontend* rejects it: "resulting universe ... may be `Prop` for some
parameter values").  Because the type may be a Prop at u := 0 while carrying a field,
`elim_only_at_universe_zero` (kernel/inductive.cpp:479) restricts I2.rec to Prop motives.
But `is_non_rec_structure` (kernel/inductive.cpp:27) only asks for 1 ctor / 0 indices /
non-recursive, and `infer_proj` (kernel/type_checker.cpp:221) only guards the field
universe when the *struct* type is syntactically `Sort 0`.  So proj/eta-struct apply and
project into `Sort v` for a parametric v.

This is NOT unsound -- see the reasoning -- but it refutes the desugaring
"proj is equivalent to an application of the recursor" that Lean4Lean's specification
of Expr.proj relies on (arXiv:2403.14064 sec 3.1 / 5.1): here no such recursor exists.
-/
import Lean
open Lean Meta

private def u : Level := .param `u
private def srt : Expr := .sort u

run_cmd do
  let iT : Expr := .forallE `a srt srt .default
  let mT : Expr := .forallE `a srt
    (.forallE `x (.bvar 0) (.app (.const `I2 [u]) (.bvar 1)) .default) .default
  Elab.Command.liftCoreM <| addDecl <| .inductDecl [`u] 1
    [{ name := `I2, type := iT, ctors := [{ name := `I2.mk, type := mT }] }] false

-- The recursor is Prop-only:
#check @I2.rec
-- @I2.rec : ∀ {a : Sort u_1} {motive : I2 a → Prop}, (∀ x, motive (I2.mk a x)) → ∀ t, motive t

run_cmd Elab.Command.liftTermElabM do
  let v := Level.param `v
  withLocalDeclD `a (Expr.sort v) fun a => do
  withLocalDeclD `x (mkApp (.const `I2 [v]) a) fun x => do
    let p := Expr.proj `I2 0 x                 -- x.1
    logInfo m!"proj eliminates into: {← inferType p}   (I2.rec cannot: motive : _ → Prop)"
    let rhs := mkApp2 (.const `I2.mk [v]) a p
    logInfo m!"eta-struct isDefEq (x) (I2.mk a x.1) = {← isDefEq x rhs}"
    -- have the KERNEL certify both facts
    addDecl (.defnDecl { name := `I2.out, levelParams := [`v], hints := .abbrev, safety := .safe
                       , type  := ← mkForallFVars #[a, x] a
                       , value := ← mkLambdaFVars #[a, x] p })
    addDecl (.thmDecl { name := `I2.eta, levelParams := [`v]
                      , type  := ← mkForallFVars #[a, x] (← mkEq x rhs)
                      , value := ← mkLambdaFVars #[a, x] (← mkEqRefl x) })

#check @I2.out
#print axioms I2.out
#print axioms I2.eta

-- Round trip is definitional in both directions, kernel-checked:
theorem I2.out_mk (a : Sort v) (y : a) : I2.out a (I2.mk a y) = y := rfl
#print axioms I2.out_mk

/- Why there is no contradiction: the kernel's constructor check
   (inductive.cpp:439) accepts a field of level m in an inductive of level l only if
   `is_geq l m` holds *universally* or l is syntactically 0.  Hence for every level
   substitution s with l[s] = 0 we also get m[s] = 0: the field is a Prop exactly
   where the structure is a Prop, so `proj` never carries data out of a Prop. -/
example (p : Prop) (h : I2.{0} p) : p := I2.out.{0} p h    -- lands in Prop, harmless

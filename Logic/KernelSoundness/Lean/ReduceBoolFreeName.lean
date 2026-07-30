/-
A THIRD, DIFFERENT mechanism: the kernel's *native* reduction hook.

`src/kernel/type_checker.cpp`:

    g_lean_reduce_bool = new_persistent_expr_const({"Lean", "reduceBool"});

    optional<expr> reduce_native(environment const & env, expr const & e) {
      if (!is_app(e)) return none_expr();
      expr const & arg = app_arg(e);
      if (!is_constant(arg)) return none_expr();
      if (app_fn(e) == *g_lean_reduce_bool) {
        object * r = ir::run_boxed_kernel(env, options(), const_name(arg), 0, nullptr);
        ...
      }
    }

and in `type_checker::whnf`, `reduce_native` is tried FIRST, ahead of both
`reduce_nat` and `unfold_definition`.

`Init.Prelude` does not define `Lean.reduceBool` (core declares it much later, in
`Init.Core`), so at this point the name is free. Defining it gives the kernel two
disagreeing rules once more — but note what is *absent* here: no
`Lean.ofReduceBool`, no `native_decide`, no `@[implemented_by]`, no `@[extern]`.
The kernel runs compiled code and believes the result, purely because a constant
is called `Lean.reduceBool`.

`#print axioms boom` therefore reports nothing at all — in contrast to the honest
`native_decide` route, which is tracked by an axiom.
-/
prelude
import Init.Prelude

/-- An ordinary definition of a name `Init.Prelude` leaves free. -/
def Lean.reduceBool (_b : Bool) : Bool := Bool.true

/-- A nullary constant for the kernel's native hook to evaluate. -/
def probe : Bool := Bool.false

/-- (1) A free variable is not a constant, so `reduce_native` declines and the
    kernel delta-reduces, agreeing with the declaration. -/
theorem rb_decl (b : Bool) : Eq (Lean.reduceBool b) Bool.true := rfl

/-- (2) A nullary constant makes the kernel *run the compiled code* for `probe`
    and believe the answer. -/
theorem rb_native : Eq (Lean.reduceBool probe) Bool.false := rfl

/-- (3) Hence `true = false`. -/
theorem true_eq_false : Eq Bool.true Bool.false :=
  @Eq.rec Bool (Lean.reduceBool probe) (fun x _ => Eq x Bool.false)
    rb_native Bool.true (rb_decl probe)

def IsTrue (b : Bool) : Prop :=
  @Bool.rec (fun _ => Prop) False True b

/-- (4) `False`. -/
theorem boom : False :=
  @Eq.rec Bool Bool.true (fun x _ => IsTrue x) True.intro Bool.false true_eq_false

#print axioms boom

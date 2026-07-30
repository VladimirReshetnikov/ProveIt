/-
Loophole #2 (kernel, no axioms at all).

The Lean kernel has a hard-wired normalizer extension for `Nat` that is keyed on
*names only*.  From `src/kernel/type_checker.cpp`:

    g_nat_add  = new_persistent_expr_const({"Nat", "add"});
    g_nat_succ = new_persistent_expr_const({"Nat", "succ"});
    g_nat_zero = new_persistent_expr_const({"Nat", "zero"});
    ...
    if (f == *g_nat_add) return reduce_bin_nat_op(nat_add, e);

and in `type_checker::whnf` the accelerator is tried *before* delta-reduction:

    } else if (auto v = reduce_nat(t1)) { ...return...
    } else if (auto next_t = unfold_definition(t1)) { ...

The kernel never checks that the constant named `Nat.add` denotes addition.
A `prelude` module - a completely standard, supported Lean feature; it is how
`Init` itself is written - may declare its own `Nat`, `Nat.zero`, `Nat.succ` and
`Nat.add`.  The kernel then has two *disagreeing* reduction rules for the same
term:

  * delta-reduction, which uses the declared body (available when arguments are
    free variables, so the accelerator does not fire), and
  * the GMP accelerator, which fires whenever both arguments reduce to literals.

Chaining them through `Eq.rec` yields `False`.
No `sorry`, no `native_decide`, no `unsafe`, no axioms.
-/
prelude

universe u v

set_option genCtorIdx false in
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a

inductive False : Prop

inductive True : Prop where
  | intro : True

/-- A perfectly ordinary definition.  It simply is not addition. -/
def Nat.add (a : Nat) (_b : Nat) : Nat := a

/-- (1) With free variables the accelerator cannot fire, so the kernel
    delta-reduces and agrees with the *declaration*. -/
theorem add_left (a b : Nat) : Eq (Nat.add a b) a := Eq.refl

/-- (2) With closed arguments the kernel's built-in GMP `Nat.add` fires first,
    computing `0 + 1 = 1`. -/
theorem add_lit : Eq (Nat.add Nat.zero (Nat.succ Nat.zero)) (Nat.succ Nat.zero) :=
  Eq.refl

/-- (3) Therefore `0 = 1`. -/
theorem zero_eq_one : Eq Nat.zero (Nat.succ Nat.zero) :=
  @Eq.rec Nat (Nat.add Nat.zero (Nat.succ Nat.zero))
    (fun x _ => Eq x (Nat.succ Nat.zero))
    add_lit
    Nat.zero
    (add_left Nat.zero (Nat.succ Nat.zero))

/-- `NZ Nat.zero` reduces to `True`; `NZ (Nat.succ Nat.zero)` reduces to `False`. -/
def NZ (n : Nat) : Prop :=
  @Nat.rec (fun _ => Prop) True (fun _ _ => False) n

/-- (4) `False`. -/
theorem boom : False :=
  @Eq.rec Nat Nat.zero (fun x _ => NZ x) True.intro (Nat.succ Nat.zero) zero_eq_one

#print axioms boom

theorem anything (P : Prop) : P := @False.rec (fun _ => P) boom

#print axioms anything

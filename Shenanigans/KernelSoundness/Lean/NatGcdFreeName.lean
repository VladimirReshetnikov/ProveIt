/-
STRONGER FORM OF THE HOLE: nothing is redefined.

The usual objection to the `prelude` construction is "you replaced part of the system".
This module replaces nothing. It imports `Init.Prelude`, so `Nat`, `Eq`, `rfl`,
`False`, `True`, `Nat.rec`, `OfNat` and the numeric literals are all the genuine
core ones. It then merely *defines* `Nat.gcd` — a name that `Init.Prelude` does
not claim (`#check @Nat.gcd` there is `unknown constant`; core defines it much
later, in `Init/Data/Nat/Gcd.lean`).

The kernel nevertheless applies its hard-wired GMP `gcd` to it, because
`src/kernel/type_checker.cpp` matches on the name alone:

    g_nat_gcd = new_persistent_expr_const({"Nat", "gcd"});
    ...
    if (f == *g_nat_gcd) return reduce_bin_nat_op(nat_gcd, e);

So the kernel has two disagreeing reduction rules for `Nat.gcd` on the *real*
`Nat`: delta-reduction (reachable with free variables, where the accelerator
declines) and GMP (fires once both arguments are literals).
-/
prelude
import Init.Prelude

/-- An ordinary definition of a name `Init.Prelude` leaves free. -/
def Nat.gcd (a : Nat) (_b : Nat) : Nat := a

/-- (1) Free variables ⇒ accelerator declines ⇒ kernel delta-reduces. -/
theorem gcd_left (a b : Nat) : Eq (Nat.gcd a b) a := rfl

/-- (2) Literal arguments ⇒ the kernel's built-in GMP `gcd` fires: `gcd 0 1 = 1`. -/
theorem gcd_lit : Eq (Nat.gcd 0 1) 1 := rfl

/-- (3) Hence `0 = 1`, for the genuine core `Nat`. -/
theorem zero_eq_one : Eq 0 1 :=
  @Eq.rec Nat (Nat.gcd 0 1) (fun x _ => Eq x 1) gcd_lit 0 (gcd_left 0 1)

/-- `NZ 0` reduces to `True`; `NZ 1` reduces to `False`. -/
def NZ (n : Nat) : Prop :=
  @Nat.rec (fun _ => Prop) True (fun _ _ => False) n

/-- (4) `False`. -/
theorem boom : False :=
  @Eq.rec Nat 0 (fun x _ => NZ x) True.intro 1 zero_eq_one

#print axioms boom

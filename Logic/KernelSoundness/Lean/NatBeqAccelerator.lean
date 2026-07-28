/-
Second instance of the same kernel hole, via `Nat.beq` instead of `Nat.add`.

`src/kernel/type_checker.cpp`:
    g_nat_beq = new_persistent_expr_const({"Nat", "beq"});
    ...
    if (f == *g_nat_beq) return reduce_bin_nat_pred(nat_eq, e);
and `reduce_bin_nat_pred` returns the constants named `Bool.true` / `Bool.false`.
-/
prelude

universe u

set_option genCtorIdx false in
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

set_option genCtorIdx false in
inductive Bool where
  | false : Bool
  | true : Bool

inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a

inductive False : Prop

inductive True : Prop where
  | intro : True

/-- An ordinary definition; it simply is not equality-testing. -/
def Nat.beq (_a _b : Nat) : Bool := Bool.true

/-- Delta-reduction (free variables ⇒ the accelerator cannot fire). -/
theorem beq_true (a b : Nat) : Eq (Nat.beq a b) Bool.true := Eq.refl

/-- The hard-wired accelerator computes `0 == 1` as `false`. -/
theorem beq_lit : Eq (Nat.beq Nat.zero (Nat.succ Nat.zero)) Bool.false := Eq.refl

theorem true_eq_false : Eq Bool.true Bool.false :=
  @Eq.rec Bool (Nat.beq Nat.zero (Nat.succ Nat.zero)) (fun x _ => Eq x Bool.false)
    beq_lit Bool.true (beq_true Nat.zero (Nat.succ Nat.zero))

def IsTrue (b : Bool) : Prop :=
  @Bool.rec (fun _ => Prop) False True b

theorem boom : False :=
  @Eq.rec Bool Bool.true (fun x _ => IsTrue x) True.intro Bool.false true_eq_false

#print axioms boom

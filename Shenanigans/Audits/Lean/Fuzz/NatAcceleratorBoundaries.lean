import Lean
/-!
# Kernel `Nat` accelerators vs. the compiled implementation, at boundaries

The kernel replaces fourteen `Nat` operations with GMP calls keyed on the
constant's *name* (`type_checker::reduce_nat`). Each is a place where a C++ bug
becomes an axiom-free `False`, and the class has bitten twice —
[lean4#1433](https://github.com/leanprover/lean4/issues/1433) (`lean_nat_mod`
truncating `size_t` to `unsigned`, a proof of `False` by plain `rfl`) and
[lean4#8060](https://github.com/leanprover/lean4/pull/8060) (`reduce_pow`
interpreting a `.const` as an `mpz`).

This harness asks the **kernel** to evaluate each accelerated operation at
powers-of-two boundaries and compares against Lean's **compiled**
implementation, which reaches the same GMP through a different code path. Any
disagreement is an axiom-free `False` by `rfl`.

Result on Lean `4.32.0`: **39,510 applications, 0 divergences.**

One deliberate gap, and the reason it is called out here: the `shiftLeft`
exponent is capped, because an uncapped shift allocates gigabytes. The first
version of this file capped it at 4096, which is why it missed
[`Reports/2026-07-31-kernel-shiftleft-panic.md`](../../../Reports/2026-07-31-kernel-shiftleft-panic.md)
— the kernel aborts outright for shifts above `UINT_MAX`. That case is now a
separate documented probe (§2) rather than something the sweep hits by accident.

Run with plain `lean` on this file; it is not part of any Lake build.
-/
open Lean Elab Command

/-- Powers of two and their neighbours: where a `size_t`/`unsigned` narrowing shows up. -/
def boundaries : List Nat :=
  let ks := [0,1,2,6,7,8,15,16,17,30,31,32,33,62,63,64,65,126,127,128,129]
  let base := ks.flatMap fun k => let p := 2 ^ k; [p - 1, p, p + 1]
  (0 :: 1 :: 2 :: 3 :: 255 :: 256 :: 65535 :: 65536 :: base).eraseDups

structure Op where
  name : Name
  ref  : Nat → Nat → Nat
  /-- Cap on the second argument, to bound the size of the result. -/
  capB : Nat := 0

def ops : List Op :=
  [ { name := ``Nat.add,        ref := (· + ·) },
    { name := ``Nat.sub,        ref := (· - ·) },
    { name := ``Nat.mul,        ref := (· * ·) },
    { name := ``Nat.div,        ref := (· / ·) },
    { name := ``Nat.mod,        ref := (· % ·) },
    { name := ``Nat.gcd,        ref := Nat.gcd },
    { name := ``Nat.land,       ref := Nat.land },
    { name := ``Nat.lor,        ref := Nat.lor },
    { name := ``Nat.xor,        ref := Nat.xor },
    { name := ``Nat.shiftLeft,  ref := Nat.shiftLeft,  capB := 4096 },
    { name := ``Nat.shiftRight, ref := Nat.shiftRight },
    { name := ``Nat.pow,        ref := Nat.pow,        capB := 64 } ]

/-! ## 1. The sweep -/

run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut bad : Array MessageData := #[]
  for op in ops do
    for a in boundaries do
      for b0 in boundaries do
        let b := if op.capB > 0 && b0 > op.capB then op.capB else b0
        if op.name == ``Nat.pow && a > 4 && b > 16 then continue
        if op.name == ``Nat.shiftLeft && a > 2^70 then continue
        let lhs := mkApp2 (mkConst op.name) (mkNatLit a) (mkNatLit b)
        let rhs := mkNatLit (op.ref a b)
        checked := checked + 1
        match Kernel.isDefEq env {} lhs rhs with
        | .ok true  => pure ()
        | .ok false => bad := bad.push m!"KERNEL DISAGREES: {op.name} {a} {b} ≠ {op.ref a b}"
        | .error e  => bad := bad.push m!"KERNEL ERROR: {op.name} {a} {b}: {e.toMessageData {}}"
  logInfo m!"checked {checked} accelerated applications"
  if bad.isEmpty then
    logInfo "no divergence between the kernel accelerators and compiled Nat"
  else
    for m in bad[:40] do logError m

/-! ## 2. The oversized-shift probe — DO NOT UNCOMMENT

`reduce_pow` bounds its exponent by `ReducePowMaxExp` and returns `none_expr()`
above it, declining to use the accelerator. `reduce_bin_nat_op(lean_nat_shiftl, …)`
has no such bound, and `lean_nat_shiftl` calls `lean_internal_panic` for shifts
above `UINT_MAX` — a hard abort, not a `kernel_exception`. Uncommenting the line
below terminates the `lean` process:

```lean
example : (1 : Nat) <<< 4294967296 = 0 := rfl
-- INTERNAL PANIC: Nat.shiftl exponent is too big     (exit 1)
```

Controls, all on `v4.32.2` with `--trust=0`:

* `(2 : Nat) ^ 4294967296 = 0 := rfl` — clean error, the exponent threshold fires.
* `Nat.shiftRight 12345 4294967296 = 0 := rfl` — **accepted**, correct.
* `(1 : Nat) <<< 16777216 = 0 := rfl` — clean type-mismatch error; the 2 MB value
  is computed correctly.

Write-up: [`Reports/2026-07-31-kernel-shiftleft-panic.md`](../../../Reports/2026-07-31-kernel-shiftleft-panic.md).
This is a robustness defect, **not** unsoundness: the process aborts rather than
continuing with a wrong value, and bignum shift amounts also panic cleanly
rather than being truncated.
-/

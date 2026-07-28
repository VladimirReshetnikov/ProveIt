# Checking the exhibits against `leanprover/comparator`

[Comparator](https://github.com/leanprover/comparator) is the Lean FRO's
trustworthy judge for Lean proofs, built for the AIMO competitions. Given a
`Challenge` module containing `theorem boom : False := sorry` and a `Solution`
module claiming to prove it, comparator guarantees the solution's theorem

1. proves the same statement as the challenge,
2. uses no more axioms than permitted, and
3. is accepted by the Lean kernel.

**Every exhibit in `../Lean/` is rejected by comparator.** That is the correct
outcome, and it is the honest bottom line for this whole line of work.

## Results

Run on comparator `master` (2026-07-28) with Lean `v4.33.0-rc1`.

| Project | Verdict | Message |
| --- | --- | --- |
| `control` | **accepted**, exit 0 | `Your solution is okay!` |
| `natgcd` | rejected, exit 1 | `Const does not match between challenge and target 'Nat.shiftRight'` |
| `reducebool` | rejected, exit 1 | `Const does not match between challenge and target 'Nat.shiftRight'` |
| `natadd` | rejected, exit 1 | `Const does not match between challenge and target 'String.ofList'` |
| `stringfab` | rejected, exit 1 | `Const does not match between challenge and target 'String.ofList'` |

`control` is an honest solution (`theorem easy : 1 + 1 = 2 := by rfl`). It is
included because without a *passing* control the four rejections would prove
nothing — they could just be the harness failing on Windows.

## This attack class was already known to the Lean FRO

Comparator's own regression suite contains
[`tests/projects/primitive_issue`](https://github.com/leanprover/comparator/tree/master/tests/projects/primitive_issue),
whose `Solution.lean` is *essentially identical* to `../Lean/NatGcdFreeName.lean`:

```lean
prelude
import Init.Prelude
import Init.Core

def Nat.gcd (_ _ : Nat) : Nat := 0

theorem thm1 a b : Nat.gcd a b = 0 := by unfold Nat.gcd; rfl
theorem thm2 : Nat.gcd 1 1 = 1 := rfl

theorem boom : False := Nat.noConfusion <| Eq.trans (thm1 1 1).symm thm2

-- The following are just to make the export "primitive-complete"
def Nat.land (_ _ : Nat) : Nat := 0
...
```

with `test.json` asserting `"exit_code": 1`. So the "define a kernel-primitive
name the prelude has not claimed" attack is a known one with a deployed
countermeasure and a regression test.

## How the defence works

`Main.lean:primitiveTargets` pins a list of kernel-special-cased constants
("List from `git grep new_persistent_expr_const src/kernel/`"), and
`Comparator/Compare.lean:compareAt` seeds a worklist with those *plus* every
constant used in the challenge statement, then transitively demands full
`ConstantInfo` equality (type **and** value) between the two exported
environments. A solution that supplies its own `Nat.gcd` — or its own `False`,
or its own `String.ofList` — differs on one of those constants and is rejected.

## A gap in the list (not exploitable as far as I could get)

`primitiveTargets` omits several names the kernel really does hard-code:

* `Lean.reduceBool` and `Lean.reduceNat` — both created with
  `new_persistent_expr_const` in `src/kernel/type_checker.cpp`, so they *are*
  matched by the comment's own stated `git grep`, yet are absent from the list.
* `Char.ofNat`, `List.cons`, `List.nil`, `String.mk`, `Char`, `List`, `Nat`,
  `String` — used by `string_lit_to_constructor`/`nat_lit_to_constructor`. These
  appear only in `builtinTargets`, which is returned **only when
  `enable_nanoda` is true**; with the default `false` they are never compared.
  (`String`, `Char` and `List` are still reached transitively from
  `String.ofList`'s type; `Char.ofNat`, `List.cons` and `List.nil` are not.)
* `eagerReduce` — kernel-special-cased, though created with `new name` rather
  than `new_persistent_expr_const`, so arguably outside the comment's scope.

I could not turn any of these into an accepted solution. The reason is a
structural one worth recording: to make the export "primitive-complete" *and*
supply the permitted axioms, the solution must import enough of `Init` — and by
the time `Init.Core` is imported, `Lean.reduceBool`, `Lean.reduceNat` and
`eagerReduce` are all defined by core, so they can no longer be claimed. The
`reducebool` project above was caught only incidentally, by the `Nat.shiftRight`
stub it had to declare to satisfy the export.

Separately, Lean `v4.33.0-rc1` reports `Lean.reduceBool` as **deprecated**
("in-kernel native reduction is deprecated; assert native evaluations with
axioms instead"), so that hook is on its way out regardless.

## Reproducing

Comparator needs Lean `v4.33.0-rc1`, `lean4export`, and `landrun`. `landrun` is
Linux-only; `fake-landrun.c` here is a Windows stand-in for the repository's
`scripts/fake-landrun.sh` (it does **no** sandboxing — it is only for testing
comparator's *verification* logic, never for judging untrusted input).

```bash
git clone https://github.com/leanprover/comparator
cd comparator && lake build lean4export comparator
gcc -O2 -o fake-landrun.exe path/to/fake-landrun.c

cd <one of the project directories here>
COMPARATOR_LANDRUN=/path/to/fake-landrun.exe \
COMPARATOR_LEAN4EXPORT=/path/to/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
  lake env /path/to/comparator/.lake/build/bin/comparator config.json
```

The `Solution.lean` files here carry extra stub definitions of the kernel
primitives (`Nat.land`, `String.ofList`, …). Those are not part of the exploit;
they exist only so `lean4export` can emit a primitive-complete export, exactly as
in comparator's own `primitive_issue` test.

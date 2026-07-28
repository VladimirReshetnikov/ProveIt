# Lean kernel soundness — adversarial artifacts

> **Warning.** Every Lean module in `Lean/` in this directory is *deliberately
> unsound*. `NatAddAccelerator.lean` and `NatBeqAccelerator.lean` each contain a
> machine-checked proof of `False` that the Lean kernel accepts. They exist to
> document a soundness hole, not to be used. They are **not** registered in the
> root `lakefile.toml`, are **not** imported by `ProveIt.lean`, and must never be.
>
> They cannot contaminate the rest of the repository: they are `prelude` modules
> that declare their own `Nat`, `Eq`, `False`, …, so importing one into a module
> that also imports `Init` is impossible.

Full write-up:
[`docs/reports/2026-07-28-lean-kernel-nat-accelerator-unsoundness.md`](../../docs/reports/2026-07-28-lean-kernel-nat-accelerator-unsoundness.md).

## The hole in one paragraph

The Lean kernel has a hard-wired normalizer extension that computes `Nat`
operations with GMP instead of unfolding their definitions. The extension is
keyed on **names only** — `src/kernel/type_checker.cpp` builds
`g_nat_add = mkConst {"Nat","add"}` at startup and fires whenever it meets a
constant with that name applied to two literals — and the kernel never checks
that the constant so named actually *is* addition. It is also tried **before**
delta-reduction in `type_checker::whnf`. A `prelude` module — a completely
standard, supported Lean feature; it is how `Init` itself is written — may
declare its own `Nat` and its own `Nat.add`. The kernel then holds two
disagreeing reduction rules for one term: delta-reduction (reachable when the
arguments are free variables, so the accelerator cannot fire) and the GMP
accelerator (fires as soon as both arguments reduce to literals). Chaining the
two through `Eq.rec` gives `False`.

## Contents

| File | What it is |
| --- | --- |
| `Lean/NatAddAccelerator.lean` | `theorem boom : False`, via a non-standard `Nat.add`. `#print axioms boom` reports **no axioms**. |
| `Lean/NatBeqAccelerator.lean` | The same hole via `Nat.beq` (whose accelerator returns the constants named `Bool.true`/`Bool.false`). |
| `Lean/NegativeControl.lean` | Control experiment. Uses `set_option debug.skipKernelTC true` to smuggle a blatantly ill-typed `bogus : False` into an `.olean`. `leanchecker` **rejects** this module — which is what makes acceptance of the other two meaningful. |
| `Lean/NativeDecideContrast.lean` | For contrast: the *already documented* `native_decide` / `@[implemented_by]` trust boundary. Unlike the two above, it does show up in `#print axioms`. |

`Fuzz/` holds the audit harnesses used to search for a hole that does *not*
require `prelude`. All three came up empty, which is the useful part of their
output; they are kept because they are reusable. Run any of them with plain
`lean <file>` (they `import Lean`; they are not part of the Lake build).

| File | What it checks |
| --- | --- |
| `Fuzz/LevelFuzzer.lean` | Kernel `Sort a ≡ Sort b` against denotational equality of the level expressions. 880 random levels, 774,400 pairs — 0 unsound, 162 incompleteness cases. |
| `Fuzz/DefEqFuzzer.lean` | That `Kernel.isDefEq a b` never holds when the kernel's own `whnf` gives `a` and `b` different `Bool` constants. 3,354 differing pairs — 0 unsound. |
| `Fuzz/CompilerKernelDiff.lean` | `Lean.Kernel.whnf` against the compiler (`Meta.evalExpr`) on closed terms over `String`/`Char`/`Nat`/`Int`/`UInt`/`BitVec`/`List`/`Array`. 72 terms — 0 divergences. |

## Reproducing

The modules are `prelude`, so they need no Lake package and no mathlib. From a
scratch directory (do not run this inside the repository's Lake workspace):

```bash
lean -o NatAddAccelerator.olean Logic/KernelSoundness/Lean/NatAddAccelerator.lean
```

Expected: exit code `0`, and `'boom' does not depend on any axioms`.

Then re-check the produced `.olean` with the independent replay checker that
ships with the toolchain (`LEAN_PATH` must contain the directory holding the
`.olean`):

```bash
leanchecker --fresh NatAddAccelerator
```

Expected: exit code `0` and no output — `leanchecker` replayed every constant
into a fresh environment through the kernel and found nothing wrong.

To confirm the checker is not simply no-opping, do the same with the control:

```bash
leanchecker NegativeControl
```

Expected: `leanchecker found a problem in NegativeControl`, exit code `1`.

## Verified on

* Lean `4.32.0` (`x86_64-w64-windows-gnu`, commit `8c9756b28d64`)
* Lean `4.31.0` — the toolchain this repository pins

## Status and prior art

**This is a rediscovery, not a new finding.** The same technique — using
`prelude` to redefine `Nat.add` and play the kernel's GMP accelerator off
against delta-reduction — was demonstrated publicly by Joachim Breitner
(a Lean core developer) in the comment thread of the Manifold market
["Is the Lean kernel unsound?"](https://manifold.markets/tfae/is-the-lean-kernel-unsound).
It was ruled out there as a "shenanigan", on the grounds that redefining core
types and operations amounts to *replacing part of the system* rather than
finding an inherent hole in it. That is a reasonable position, and it is the
right way to read these artifacts.

What the artifacts here add is a self-contained, minimal, end-to-end verified
reproduction: exit code `0`, `#print axioms` reporting nothing, `leanchecker
--fresh` accepting, and a negative control proving the checker is not
no-opping. No matching issue exists on the `leanprover/lean4` tracker, so the
behaviour is not fixed — only deemed out of scope.

The behaviour is present in both toolchains listed above.

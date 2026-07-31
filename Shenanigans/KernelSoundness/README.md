# Lean kernel soundness — adversarial artifacts

> **Warning.** Every Lean module in `Lean/` in this directory is *deliberately
> unsound*. Four of them contain a machine-checked proof of `False`. They exist
> to document soundness holes, not to be used. They are **not** registered in the
> root `lakefile.toml`, are **not** imported by `ProveIt.lean`, and must never be.
>
> They cannot contaminate the rest of the repository: they are `prelude` modules,
> so importing one into a module that also imports `Init` is impossible.

Full write-up:
[`docs/reports/2026-07-28-lean-kernel-nat-accelerator-unsoundness.md`](../../docs/reports/2026-07-28-lean-kernel-nat-accelerator-unsoundness.md).

> ## Bottom line: Lean's official judge rejects all of these
>
> Every exhibit here was run through
> [`leanprover/comparator`](https://github.com/leanprover/comparator), the Lean
> FRO's trustworthy proof judge, against a `theorem boom : False := sorry`
> challenge. **All four are rejected**; an honest control solution is accepted.
>
> However, `Comparator/evade/` **is accepted** (exit 0, `Your solution is okay!`,
> `#print axioms boom` reporting nothing). It exploits the fact that comparator
> checks only that the challenge and solution *agree* on the kernel primitives,
> never that those primitives are the real ones — so a challenge that does not
> import `Init` gets no protection from that mechanism, a precondition comparator
> documents but does not enforce. A normally-written challenge is unaffected.
> See [`Comparator/README.md`](Comparator/README.md) for the runs and messages.
>
> Comparator's own regression suite already contains this attack:
> `tests/projects/primitive_issue` is essentially identical to
> `Lean/NatGcdFreeName.lean`, with `"exit_code": 1` asserted. So this is a known
> attack class with a deployed countermeasure — which is also the reason
> comparator exists, since `#print axioms` plus `leanchecker` demonstrably are
> **not** sufficient on their own.

## The hole in one paragraph

The Lean kernel has hard-wired normalizer extensions that compute `Nat`
operations with GMP, and that run compiled code for `Lean.reduceBool`, instead of
unfolding definitions. Every one of these extensions is keyed on **names only** —
`src/kernel/type_checker.cpp` builds `g_nat_add = mkConst {"Nat","add"}` at
startup and fires whenever it meets a constant with that name — and the kernel
never checks that the constant so named actually *is* what it assumes. The
extensions are also tried **before** delta-reduction in `type_checker::whnf`.
Give the kernel a differently-behaving declaration under one of those names and
it holds two disagreeing reduction rules for one term: delta-reduction
(reachable when an argument is a free variable, so the extension declines) and
the extension (fires once the arguments are literals, or a nullary constant).
Chaining the two through `Eq.rec` gives `False`.

## The worst case: the kernel fabricates an inhabitant of an empty type

`StringLitFabrication.lean` is qualitatively different from the arithmetic
exhibits. There, two reduction rules disagreed about a definition I wrote. Here
the kernel simply **builds a term that is not well typed, and never checks it**.

`string_lit_to_constructor` assembles `String.ofList (List.cons (Char.ofNat 97)
List.nil)` out of names, and `inductive_reduce_rec` hands the result straight to
`String.rec`'s computation rule. Nothing type-checks the assembled term. So if
`String.ofList`'s field type happens to be `Empty` — a type with **no
constructors** — the kernel produces an inhabitant of it, and `False` follows in
three lines. A bare string literal `"a"` is the whole trigger: no `Nat`, no
numerals, no `OfNat`, and no `List` or `Char` declarations at all (those names
are never resolved, precisely because the term is never inferred).

For real Lean this is harmless, because core's `String.ofList` genuinely is that
constructor. But that is an *unchecked assumption about the ambient environment*,
which is the same root cause as the arithmetic accelerators — with a much worse
failure mode.

## The interesting part: you do not have to redefine anything

The obvious objection to this — and the reason it was dismissed when it was first
raised (see *Prior art*) — is "you replaced part of the system". `NatGcdFreeName`
answers that. It imports `Init.Prelude`, so `Nat`, `Nat.add`, `Eq`, `rfl`,
`True`, `False`, `Nat.rec` and the numeric literals are all the genuine core
ones, used unmodified. It then merely **defines** `Nat.gcd` — a name
`Init.Prelude` does not claim, because core defines it much later in
`Init.Data.Nat.Gcd`.

`Lean/FreeNameSurvey.lean` enumerates the surface. Under `Init.Prelude`, nine
kernel-special-cased names are free:

```
Nat.gcd   Nat.land   Nat.lor   Nat.xor   Nat.shiftLeft   Nat.shiftRight
Lean.reduceBool   Lean.reduceNat   eagerReduce
```

The kernel has already armed hard-wired rules for all of them. So the hazard is
not "a module that redefines `Nat`" but "a module that defines a name the kernel
has claimed but the prelude has not yet". `dontcare` — the kernel's placeholder
constant in `is_def_eq_binding` — is free even with all of `Init` imported, but
it appears to be genuinely vacuous.

## Contents

| File | What it is | `leanchecker` |
| --- | --- | --- |
| `Lean/NatGcdFreeName.lean` | **Strongest.** Redefines nothing; imports `Init.Prelude` and defines the free name `Nat.gcd`. `theorem boom : False` about the *genuine* core `Nat`. `#print axioms` reports nothing. | accepts |
| `Lean/StringLitFabrication.lean` | **Worst failure mode.** Nothing "disagrees" with anything: expanding a *string literal* makes the kernel assemble a term by name and feed it to a recursor rule **without type-checking it**, fabricating an inhabitant of `Empty` — a type with no constructors. Trigger is a bare `"a"`; no `Nat`, numerals, `OfNat`, `List` or `Char` needed. | accepts |
| `Lean/NatAddAccelerator.lean` | `theorem boom : False` via a module-local `Nat` and a non-standard `Nat.add`. | accepts |
| `Lean/NatBeqAccelerator.lean` | The same, via `Nat.beq` (whose accelerator returns the constants named `Bool.true`/`Bool.false`). | accepts |
| `Lean/ReduceBoolFreeName.lean` | Different mechanism: the kernel's *native* hook. Defining the free name `Lean.reduceBool` makes the kernel run compiled code and believe it — with **no** `Lean.ofReduceBool`, no `native_decide`, no `@[implemented_by]`. `lean` exits 0 and `#print axioms` reports nothing, so this is an axiom-*tracking* hole. | **rejects** (the interpreter cannot replay `probe`) |
| `Lean/ProjIndexTruncation.lean` | **Not `prelude`; a live upstream defect.** `Expr.proj` indices are narrowed `size_t`→`unsigned` behind an `is_small()` guard, so index `2^32+k` becomes `k` and the kernel accepts projections out of range for the structure ([lean4#12746](https://github.com/leanprover/lean4/issues/12746), OPEN). Not a `False` on its own — truncation is consistent, and a collision needs 2^32 fields. Ships its own control and a `v4.32.0`/`v4.32.2`/`v4.33.0-rc1` matrix. | n/a (no `False`) |
| `Lean/NegativeControl.lean` | Control. `set_option debug.skipKernelTC true` smuggles a blatantly ill-typed `bogus : False` into an `.olean`. It too builds with exit 0 and reports no axioms. | **rejects** — which is what makes acceptance of the others meaningful |
| `Lean/FreeNameSurvey.lean` | `#check`s every kernel-special-cased name under `Init.Prelude` to show which are free. | n/a |
| `Lean/NativeDecideContrast.lean` | For contrast: the *documented* `native_decide` / `@[implemented_by]` boundary. Unlike the above, it does show up in `#print axioms`. | n/a |

`Fuzz/` holds the audit harnesses used to search for a hole that does *not*
require `prelude`. All three came up empty, which is the useful part of their
output; they are kept because they are reusable. Run any with plain `lean <file>`
(they `import Lean`; they are not part of the Lake build).

| File | What it checks |
| --- | --- |
| `Fuzz/LevelFuzzer.lean` | Kernel `Sort a ≡ Sort b` against denotational equality of the level expressions. 880 random levels, 774,400 pairs — 0 unsound, 162 incompleteness cases. |
| `Fuzz/DefEqFuzzer.lean` | That `Kernel.isDefEq a b` never holds when the kernel's own `whnf` gives `a` and `b` different `Bool` constants. 3,354 differing pairs — 0 unsound. |
| `Fuzz/CompilerKernelDiff.lean` | `Lean.Kernel.whnf` against the compiler (`Meta.evalExpr`) on closed terms over `String`/`Char`/`Nat`/`Int`/`UInt`/`BitVec`/`List`/`Array`. 72 terms — 0 divergences. |

## Reproducing

```bash
pwsh Shenanigans/KernelSoundness/verify.ps1
```

It builds each module in a scratch directory outside the Lake workspace, runs
`leanchecker --fresh` on each, and **asserts the verdict in the table above**,
including that the negative control is rejected. Expected final line:
`All 5 modules behaved as documented.`

## Verified on

* Lean `4.32.0` (`x86_64-w64-windows-gnu`, commit `8c9756b28d64`)
* Lean `4.31.0` — the toolchain this repository pins

## Status and prior art

**The core technique is a rediscovery.** Using `prelude` to redefine `Nat.add`
and play the kernel's GMP accelerator off against delta-reduction was
demonstrated publicly by Joachim Breitner (a Lean core developer) in the comment
thread of the Manifold market
["Is the Lean kernel unsound?"](https://manifold.markets/tfae/is-the-lean-kernel-unsound).
It was ruled out there as a "shenanigan", on the grounds that redefining core
types and operations amounts to *replacing part of the system* rather than
finding an inherent hole in it.

What is added here: (a) a self-contained, end-to-end verified reproduction with a
negative control; (b) the `NatGcdFreeName` variant, which replaces nothing at all
and so is not obviously covered by that objection; (c) the survey showing this is
a family of nine free names rather than a one-off; and (d) the `Lean.reduceBool`
variant, which is a distinct mechanism and an axiom-tracking hole.

**Upstream has now ruled on this family (corrected 2026-07-30).** An earlier
version of this section said no matching issue existed on the `leanprover/lean4`
tracker. That is wrong: [lean4#13626](https://github.com/leanprover/lean4/issues/13626)
("does the kernel assume built-in Bool order?", filed 2026-05-03) is exactly the
`Lean.reduceBool` free-name mechanism of `ReduceBoolFreeName.lean`, reported
independently. It was closed 2026-05-04 as working-as-intended, with the
maintainers' position stated explicitly:

> The kernel assumes that the official prelude is used. If you use `prelude` you
> are responsible for making sure it matches the kernel's expectations, i.e. It
> is not supported to write arbitrary code after `prelude`.

This covers **every exhibit in this directory**, including `NatGcdFreeName.lean`:
that module redefines nothing, but it is still a `prelude` module (`prelude` plus
`import Init.Prelude`), which is precisely the configuration declared
unsupported. So the correct status is not "unreported and therefore unfixed" but
**"reported, and deliberately out of scope"** — a documented policy boundary
rather than an open hole. The exhibits remain useful as a precise description of
where that boundary lies and what is on the far side of it.

See [`../CATALOG.md`](../CATALOG.md) for this family's place among all known Lean
and Rocq defects.

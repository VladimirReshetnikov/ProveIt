# Escape hatches: the sanctioned routes to `False`

Every proof assistant ships with ways to assert things the kernel has not
verified. They exist because the alternative — a system in which nothing can be
stubbed, no compiled code can be trusted, and no experimental extension can be
tried — would not be usable. This directory catalogs them, in both systems, with
the audit output for each machine-checked.

Category (see [`../README.md`](../README.md)): a route belongs here when the
`False` is **closed** (no hypothesis in the statement) but *something* discloses
the cost — an entry in `#print axioms` / `Print Assumptions`, or a non-default
compiler flag, or, in the last two files, only a careful reading of the
statement.

Contrast with [`../KernelDefects/`](../KernelDefects/), where the `False` is
closed and the audit reports **nothing**. That is the whole distinction this
directory exists to draw.

## Contents

### Lean

| File | Route | What `#print axioms` reports |
| --- | --- | --- |
| [`Lean/Sorry.lean`](Lean/Sorry.lean) | `sorry` — and the `sorry` you did not write: a failed tactic or a type error patches the declaration and it still enters the environment | `sorryAx` |
| [`Lean/Axioms.lean`](Lean/Axioms.lean) | `axiom`, including the innocuous-looking kind; plus the realistic failure — an over-general statement under `autoImplicit` | the axiom, by name |
| [`Lean/Unsafe.lean`](Lean/Unsafe.lean) | **Negative result.** `unsafe` and `partial` do *not* get you there: the kernel refuses to let a safe declaration depend on an unsafe one, and `partial` needs `Inhabited` | n/a |
| [`Lean/NativeDecide.lean`](Lean/NativeDecide.lean) | `@[implemented_by]` + `native_decide`. The one route that yields a closed, `sorry`-free, `unsafe`-free `theorem Paradox : False` from two core attributes | a fresh per-use axiom, `<thm>._native.native_decide.ax_N_M` |
| [`Lean/Metaprogramming.lean`](Lean/Metaprogramming.lean) | `set_option debug.skipKernelTC true` + hand-built `addDecl`. The only Lean route the audit cannot see | **nothing** — but `leanchecker` rejects it |
| [`Lean/Spoofing.lean`](Lean/Spoofing.lean) | Shadowed names, claimed glyphs, homoglyph identifiers: the statement is not what it reads as | nothing, correctly |
| [`Lean/Spoofing.BareCyrillic.lean`](Lean/Spoofing.BareCyrillic.lean) | Companion control: a bare Cyrillic homoglyph is a **parse error** in Lean, unlike in Rocq | n/a — must be rejected |

### Rocq

| File | Route | Flag needed | What `Print Assumptions` reports |
| --- | --- | --- | --- |
| [`Coq/Assumptions.v`](Coq/Assumptions.v) | `Admitted`, `Axiom`, `Program` obligations | — | the assumption, by name |
| [`Coq/TypingFlags.v`](Coq/TypingFlags.v) | `Unset Guard Checking` (non-terminating fixpoint), `Unset Positivity Checking` (Curry), `Unset Universe Checking` (Hurkens), `#[bypass_check(...)]` | — | `loop is assumed to be guarded.` / `Curry is assumed to be positive.` / `… relies on an unsafe hierarchy.` |
| [`Coq/RewriteRules.v`](Coq/RewriteRules.v) | `Symbol` + `Rewrite Rule` — unchecked definitional equalities injected straight into kernel conversion | `-allow-rewrite-rules` | the symbols, plus `Theory: Rewrite rules are allowed` |
| [`Coq/ImpredicativeSet.v`](Coq/ImpredicativeSet.v) | Chicli–Pottier–Simpson: impredicative `Set` is safe alone, fatal with decidability in `Set` | `-impredicative-set` | `Theory: Set is impredicative` |
| [`Coq/Spoofing.v`](Coq/Spoofing.v) | Redefined names, redefined notations, redefined `=`, homoglyphs | — | `Closed under the global context`, correctly |

## Reproducing

```bash
pwsh Shenanigans/EscapeHatches/verify.ps1
```

Expected final line: `All 14 escape-hatch exhibits behaved as documented.`

Every Lean file carries its own `#guard_msgs` assertions — including the exact
`#print axioms` output and every expected error message — so `lean` exiting 0
already means all of that matched. The script adds the Rocq substring assertions
and, for the two flag-gated Rocq files, the **controls**: each must be *rejected*
without its flag, with the exact refusal recorded
(`requires passing the flag "-allow-rewrite-rules"`, and
`universe inconsistency: Cannot enforce Set+1 <= Set`).

Verified on Lean `4.32.0` and The Rocq Prover `9.2`.

## Three things this collection settles

**1. The two systems draw the line in different places, and neither is
uniformly safer.**

Rocq lets you switch off each kernel check individually and then *tells you* —
`Print Assumptions` names the disabled flag, and the report is per-declaration.
Lean has no such flag, and no such report: its only comparable route,
`debug.skipKernelTC`, bypasses the kernel wholesale and is invisible to
`#print axioms`. Against that, Lean's `unsafe`/`partial` quarantine is enforced
*by the kernel* — `(kernel) invalid declaration, it uses unsafe declaration` —
where Rocq's `Unset Guard Checking` is a real, documented route to `False`.

**2. `native_decide` no longer means what most write-ups say it means.**

`Lean.reduceBool`, `Lean.reduceNat`, `Lean.ofReduceBool` and `Lean.ofReduceNat`
are all deprecated since 2026-02-01, with the message *"in-kernel native
reduction is deprecated; assert native evaluations with axioms instead"*. Under
[RFC #12216](https://github.com/leanprover/lean4/issues/12216), shipped in
`v4.29.0`, `native_decide` runs the computation in the tactic and emits **one
fresh axiom per use**, named after the theorem that used it. `Lean/NativeDecide.lean`
asserts the current name. This is strictly better for auditing, and it is why
the `Lean.reduceBool` exhibit in
[`../KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean`](../KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean)
documents a mechanism on its way out.

**3. The audit is not the last line of defence — reading the statement is.**

`Spoofing.lean` and `Spoofing.v` produce theorems that are entirely honest, fully
closed, and accepted by every checker, whose displayed statements are lies. No
assumption-tracking machinery in either system can catch this, and none is
supposed to. The lexical half of the question — *which* confusable identifiers a
system will actually accept — is studied systematically for Lean in
[`../Audits/Lean/StringIdentity/`](../Audits/Lean/StringIdentity/), whose answer
is mildly reassuring: every confusable Lean admits requires French quotes `«…»`,
which are conspicuous in source. Rocq accepts bare Cyrillic homoglyphs, which
are not.

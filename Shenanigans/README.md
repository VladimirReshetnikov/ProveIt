# Shenanigans

**Nothing in this directory is ordinary mathematics.**

Everything else in this repository proves theorems in the ordinary sense. This
directory does not. It is a catalog of the ways one can write

```lean
theorem Paradox : False
```

in Lean 4 and in Rocq/Coq, and get it accepted — organised by *what it costs you
to do so*.

A `False` derived here is a statement about a formal system or about a program.
It is never a mathematical fact, and never grounds for doubting anything proved
elsewhere in this repository. Nothing here is imported by the mathematical
developments, and nothing outside this directory depends on any of it.

## The organising question: what does the audit report?

Every route to `False` gives something up, and the four top-level directories
are exactly the four answers to *what*.

| Route | The `False` is | `#print axioms` / `Print Assumptions` says | Directory |
| --- | --- | --- | --- |
| **Assume what the theory withholds** | conditional — the hypothesis is in the statement | nothing; the cost is visible in the *type* | [`Paradoxes/`](Paradoxes/) |
| **Use a sanctioned escape hatch** | closed | names the hatch — or a non-default flag was needed, or the statement is not what it looks like | [`EscapeHatches/`](EscapeHatches/) |
| **Exploit an implementation defect** | closed | **nothing at all** — and that is the bug | [`KernelDefects/`](KernelDefects/) |
| **Look for a route and fail** | there is none | — | [`Audits/`](Audits/) |

The third row is the only one that is anybody's fault. The first is a permanent
fact about type theory; the second is a documented feature being used as
designed; the fourth is a negative result.

## Contents

| Path | Contents |
| --- | --- |
| [`Paradoxes/`](Paradoxes/) | Girard/Hurkens, Coquand–Paulin, Cantor, and the subsingleton-elimination barrier, each stated as an implication from an ingredient the system withholds, each axiom-free. Plus `Blockers.lean`, which machine-checks the exact judgment Lean refuses in every case. Lean and Rocq. |
| [`EscapeHatches/`](EscapeHatches/) | The sanctioned routes: `sorry`, `axiom`, `Admitted`, `native_decide` + `@[implemented_by]`, `Unset Guard/Positivity/Universe Checking`, rewrite rules, `-impredicative-set`, unchecked `addDecl` — and the two routes that defeat the audit rather than the kernel, `Spoofing.lean`/`Spoofing.v`. Lean and Rocq. |
| [`KernelDefects/`](KernelDefects/) | Genuine implementation defects. Lean: the name-keyed `Nat`/`String`/`reduceBool` accelerator family, `Expr.proj` index truncation, definitional-equality history dependence, with controls and a `leanchecker` verdict for each. Rocq: four fixed guard-checker and module-system defects, kept as regression witnesses. |
| [`Audits/`](Audits/) | Searches that came up empty, which is the useful part of their output. Level/def-eq/compiler fuzzers, the `Acc` and `Expr.proj` metatheory probes, and the string- and name-identity study. |
| [`Reports/`](Reports/) | Write-ups suitable for upstream bug reports, each pinned to specific toolchain versions. |
| [`CATALOG.md`](CATALOG.md) | **The completeness ledger.** Every known route in both systems, whether or not this directory represents it, with upstream issue numbers, affected version ranges, and a coverage mark. |

## Reproducing

Each category verifies itself. Every script builds in a scratch directory
outside the repository and **asserts** the documented verdict — exit code plus
the exact audit output — rather than printing something for a human to read.

```bash
pwsh Shenanigans/Paradoxes/verify.ps1        # All 6 paradox exhibits behaved as documented.
pwsh Shenanigans/EscapeHatches/verify.ps1    # All 14 escape-hatch exhibits behaved as documented.
pwsh Shenanigans/KernelDefects/Lean/verify.ps1   # All 6 modules behaved as documented.
pwsh Shenanigans/KernelDefects/Coq/verify.ps1    # All 4 Coq exhibits behaved as documented.
```

Verified on Lean `4.32.0` (`x86_64-w64-windows-gnu`, commit `8c9756b28d64`) and
The Rocq Prover `9.2` (OCaml 4.14.2).

## Ground rules for anything added here

1. **Know which category you are in, and say so in the file header.** The three
   that produce a `False` are distinguished by what the audit reports, not by
   how clever the construction is. A `False` that needs a flag is an escape
   hatch even if the flag is obscure; a `False` that needs an assumption is a
   paradox even if the assumption looks plausible.
2. **No `sorry` and no new `axiom` in `Paradoxes/`, `KernelDefects/`, or
   `Audits/`.** A `False` obtained by assuming one is worthless as evidence of a
   defect. `EscapeHatches/` is the exception and exists precisely to exhibit
   them — with the exact `#print axioms` output asserted.
3. **Every claim carries its audit, machine-checked.** In Lean that means
   `#guard_msgs in #print axioms foo`, so a toolchain change that alters the
   answer fails the build instead of silently invalidating the prose. In Rocq it
   means `Print Assumptions` with the expected substring asserted by
   `verify.ps1`.
4. **State the toolchain.** `lean` resolves its toolchain from the current
   directory, so results are meaningless without a pin. Prefer
   `elan run leanprover/lean4:<version> lean --trust=0 <file>`, and give a
   version matrix rather than a single verdict.
5. **Judge by exit code and the audit, never by grepping output for `error`.** A
   stack-overflow abort prints no `error` line and returns 127; a linter warning
   is not an error. `Lean.addDecl` is asynchronous in 4.32.x, so a `try`/`catch`
   around it silently reports kernel rejections as acceptances — use
   `set_option Elab.async false`, or the synchronous
   `(← getEnv).toKernelEnv.addDecl {}` and `Lean.Kernel.isDefEq`.
6. **Give every defect a control.** Acceptance of an exhibit means something only
   if a deliberately-broken twin is rejected by the same procedure. See
   [`KernelDefects/Lean/Controls/`](KernelDefects/Lean/Controls/).

## Context

For the perspective the `KernelDefects/` category should be read in, see Leonardo
de Moura's [*Who Watches the Provers?*](https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/).
Its argument is that a kernel bug is not a crisis but the expected cost of a
kernel fast enough to be usable, and that the defence is having several
independent implementations disagree: a term one kernel accepts and another
rejects is the design working. That is the standard applied here — every defect
is pinned to exact versions, given a control, and checked against an independent
judge where one exists. The
[Lean Kernel Arena](https://arena.lean-lang.org/) has since made that argument
operational, running a standard attack corpus against fifteen independent
checkers.

Lawrence Paulson's [*Broken proofs and broken
provers*](https://lawrencecpaulson.github.io/2026/01/15/Broken_proofs.html)
supplies the longer view from outside both systems, running back through
Isabelle/HOL, HOL88, LCF and PVS: soundness bugs recur in every prover, and their
practical consequences have been consistently small, because nobody's real
theorem turned out to depend on one. His sharper point is that the inadequacy of
a *model* of the world is a far likelier source of a wrong conclusion than the
unsoundness of a kernel.

Both cautions apply to everything below — and so does a third, which this
directory's own [`EscapeHatches/Lean/Spoofing.lean`](EscapeHatches/Lean/Spoofing.lean)
makes concrete: the likeliest way to end up believing something false is not a
broken kernel or a bad axiom, but a correct proof of a statement that does not
say what its reader thought it said.

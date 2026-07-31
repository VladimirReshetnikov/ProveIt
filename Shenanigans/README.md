# Shenanigans

**Nothing in this directory is ordinary mathematics.**

Everything else in this repository proves theorems. This directory does not. It
collects two related kinds of work:

* **Paradoxes of proof systems.** Girard's paradox, Hurkens' simplification of
  it, and the Coquand-Paulin counterexample are derivations of `False` from
  assumptions a type theory might plausibly have made but does not. They are
  stated as *implications*: each hypothesizes the ingredient Lean withholds and
  shows that granting it is fatal. A theorem here of the form `… → False` is a
  negative result about type theory — a proof that some rule *cannot* be added —
  not a defect in Lean.
* **Loopholes in kernels implementing those systems.** Probes of the Lean 4
  kernel: its accelerated `Nat` and `String` primitives, name and string
  identity, definitional-equality caching, and the checked `addDecl` path. Some
  of these are genuine soundness defects that produce an axiom-free `False`.
  Where that happens, the defect is a bug in an *implementation*, is reported
  upstream, and is recorded here with the exact toolchain versions affected.

Read a `False` in this directory as a claim about a formal system or a program,
never as a mathematical fact. Do not import any of it into ordinary
developments.

## Contents

| Path | Contents |
| --- | --- |
| [`Hurkens/`](Hurkens/) | Hurkens' form of Girard's paradox in Lean 4, axiom-free. Derives `False` from a hypothetical impredicative closure of `Type u` over itself, and from a Tarski-style universe decoding `El : V → Type u` with a section. Both isolate the one judgment Lean's predicative hierarchy denies: `(X : Type u) → F X` lands in `Type (u+1)`, never `Type u`. |
| [`Coq/`](Coq/) | The Coq side of both categories. `Paradoxes/` gives Girard/Hurkens as implications, plus the universe constraint that closes the one historical route to the hypothesis. `GuardChecker/` and `ModuleSystem/` hold four fixed soundness defects, each a proof of `False` on an affected toolchain and a regression witness on a fixed one. |
| [`KernelSoundness/`](KernelSoundness/) | Lean 4 kernel probes. `Mathematical/` holds the paradox-adjacent results (Coquand-Paulin, the Hurkens blocker, `Acc`/proof-irrelevance anomalies, projection-versus-recursor). `Lean/`, `Comparator/`, `Fuzz/`, and `StringIdentity/` hold accelerator, definitional-equality, and name-identity probes with their controls. |
| [`Reports/`](Reports/) | Write-ups suitable for upstream bug reports, each pinned to specific toolchain versions. |
| [`CATALOG.md`](CATALOG.md) | **Registry of all known Lean and Rocq type-system defects and kernel loopholes**, with what this directory does and does not yet cover. The working index for the goal of representing every one of them. |

## Ground rules for anything added here

1. **Never `sorry`, never a new `axiom`.** A `False` obtained by assuming
   something is worthless. Every claim carries a `#print axioms` audit.
2. **Distinguish the three categories**, explicitly, in every write-up: a
   property failing for the *declarative theory* (a metatheory result); failing
   for the *kernel as implemented* (a bug to report); or failing only on a
   version with an already-known, already-fixed defect (weak).
3. **State the toolchain.** `lean` resolves its toolchain from the current
   directory, so results are meaningless without a pin. Prefer
   `elan run leanprover/lean4:<version> lean --trust=0 <file>`, and give a
   version matrix rather than a single verdict.
4. **Judge by exit code and `#print axioms`**, never by grepping output for
   `error`. A stack-overflow abort prints no `error` line and returns 127; a
   linter warning is not an error. `Lean.addDecl` is asynchronous in 4.32.x, so
   a `try`/`catch` around it silently reports kernel rejections as acceptances —
   use `set_option Elab.async false`, or the synchronous
   `(← getEnv).toKernelEnv.addDecl {}` and `Lean.Kernel.isDefEq`.
5. **Keep controls.** A probe that shows a defect must be accompanied by the
   variant with the defect's key ingredient removed, demonstrating that the
   ingredient is essential rather than incidental.

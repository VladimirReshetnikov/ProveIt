# Coq — paradoxes and kernel loopholes

The Coq counterpart of [`Hurkens/`](../Hurkens/) and
[`KernelSoundness/`](../KernelSoundness/). Same two categories, same ground
rules (see [`../README.md`](../README.md)): a `False` here is a claim about a
formal system or a program, never a mathematical fact.

> **Warning.** Three files in this directory are proofs of `False` on a
> affected toolchain. They are *expected to be rejected* by a fixed one and
> are not part of any build: they are absent from
> [`_CoqProject`](../../_CoqProject) and nothing imports them.

## Contents

| File | Category | Verdict on Rocq 9.2 |
| --- | --- | --- |
| [`Paradoxes/Hurkens.v`](Paradoxes/Hurkens.v) | Paradox | **compiles**, four axiom-free audits |
| [`GuardChecker/HigherOrderFixpoint.v`](GuardChecker/HigherOrderFixpoint.v) | Defect (fixed) — rocq#21683 | rejected |
| [`GuardChecker/NestedMutualCrossCall.v`](GuardChecker/NestedMutualCrossCall.v) | Defect (fixed) — rocq#21682 | rejected |
| [`GuardChecker/UniformArgsLet.v`](GuardChecker/UniformArgsLet.v) | Defect (fixed) — rocq#21701 | rejected |
| [`ModuleSystem/AliasChainDeltaResolver.v`](ModuleSystem/AliasChainDeltaResolver.v) | Defect (fixed) — rocq#21685 | rejected |

## Reproducing

```powershell
pwsh Shenanigans/Coq/verify.ps1
```

Each exhibit is compiled in a scratch directory outside the repository, and the
script **asserts** both the verdict and a distinguishing substring of the
output. Expected final line: `All 5 Coq exhibits behaved as documented.`
Verified on **The Rocq Prover 9.2** (OCaml 4.14.2).

## Paradoxes versus defects

`Paradoxes/Hurkens.v` states Girard/Hurkens as *implications*: it hypothesizes
an ingredient Coq withholds — `Type : Type`, or a retract of `Type` into `Prop`
— and derives `False`. Those are permanent facts about type theory. The stdlib
[`Hurkens`](https://rocq-prover.org/doc/v8.9/stdlib/Coq.Logic.Hurkens.html)
module supplies them, and this file also records the one case where the
hypothesis was once reachable *for real*:

A submission to
[`codyroux/name-the-biggest-number`](https://github.com/codyroux/name-the-biggest-number/blob/master/Shenannigans.v)
(by jakobbotsh, annotated "Works in 8.9.1") built the retract from

```coq
Inductive foo (A:Type) := bar X : foo X -> foo A | nonempty.
```

whose constructor quantifies over `X : Type` in the *same* universe as the
parameter, so the small type `foo nat` could store an arbitrary `X : Type`.
With `up (down X) = X` by `reflexivity`, Hurkens gave a closed, axiom-free
`False`, which the submission used to "prove" `forall n, n < 7` — winning a
biggest-number contest by making the logic inconsistent.

On Rocq 9.2 the projection half still type-checks; the injection is refused:

```
The term "u" has type "U" while it is expected to have type "Type"
(universe inconsistency: Cannot enforce U.u0 <= foo.u0 because foo.u0 < U.u0).
```

That constraint is the fix, and it is the control for the file: the paradox is
unreachable precisely because the retract cannot be built.

## Why the defects cluster where they do

Of the eight Coq proofs of `False` catalogued in [`../CATALOG.md`](../CATALOG.md)
§3.1, three are guard-checker bugs and three are module-system bugs. Both
subsystems are reproduced here. The clustering is structural, not accidental:

* Coq checks recursion with a syntactic **guard checker** over `Fixpoint`
  definitions. Its job — decide termination from the shape of the term — is
  subtle, and all three bugs here are failures of one analysis, *uniform
  argument* computation for nested mutual fixpoints, reached three different
  ways (cross-calls, `let`-bound recursive aliases, higher-order passing).
  Lean compiles recursion to recursors and eliminators, so it has no guard
  checker and no analogue of this family.
* Coq's **module system** (functors, aliases, `Include`, delta-resolution) is a
  large piece of trusted infrastructure with no Lean counterpart at all.

Neither observation makes Lean safer overall — see
[`../KernelSoundness/`](../KernelSoundness/) for its own defects, which cluster
instead around name-keyed normalizer extensions and unchecked term
construction. The point is that the two systems' soundness risks live in
different places, so a catalog of one says little about the other.

## Sources

* Tristan Stérin, [*In search of falsehood*](https://tristan.st/blog/in_search_of_falsehood)
  — the systematic AI-driven search that produced seven of the eight Coq proofs
  of `False` recorded here (found by Opus 4.6; several were escalated to full
  derivations of `False` by ccz181078/mxdys).
* The [`rocq-prover/rocq`](https://github.com/rocq-prover/rocq/issues) tracker.
* [`codyroux/name-the-biggest-number`](https://github.com/codyroux/name-the-biggest-number).
* Stdlib [`Hurkens`](https://rocq-prover.org/doc/v8.9/stdlib/Coq.Logic.Hurkens.html).

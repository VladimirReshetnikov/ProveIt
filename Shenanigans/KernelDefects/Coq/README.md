# Rocq kernel defects — regression witnesses

Four soundness defects from the 2026 sweep, each a proof of `False` on an
affected toolchain and each **fixed upstream**. That makes every file here a
*regression witness*: it must be **rejected** by a current Rocq, and acceptance
would signal a regression.

Same ground rules as the rest of the directory (see
[`../../README.md`](../../README.md)): a `False` here is a claim about a program,
never a mathematical fact.

> **Warning.** Every file in this directory is a proof of `False` on an affected
> toolchain. They are not part of any build: they are absent from
> [`_CoqProject`](../../../_CoqProject) and nothing imports them.

## Contents

| File | Upstream | Verdict on Rocq 9.2 |
| --- | --- | --- |
| [`GuardChecker/NestedMutualCrossCall.v`](GuardChecker/NestedMutualCrossCall.v) | [rocq#21682](https://github.com/rocq-prover/rocq/issues/21682) | rejected — `Recursive definition of F is ill-formed` |
| [`GuardChecker/HigherOrderFixpoint.v`](GuardChecker/HigherOrderFixpoint.v) | [rocq#21683](https://github.com/rocq-prover/rocq/issues/21683) | rejected — `Recursive definition of russell is ill-formed` |
| [`GuardChecker/UniformArgsLet.v`](GuardChecker/UniformArgsLet.v) | [rocq#21701](https://github.com/rocq-prover/rocq/issues/21701) | rejected — `Recursive definition of F_let is ill-formed` |
| [`ModuleSystem/AliasChainDeltaResolver.v`](ModuleSystem/AliasChainDeltaResolver.v) | [rocq#21685](https://github.com/rocq-prover/rocq/issues/21685) | rejected — `Unable to unify` |

The Rocq paradoxes moved to [`../../Paradoxes/Coq/`](../../Paradoxes/Coq/), and
the flag-gated routes to `False` — including `Unset Guard Checking` and
`Unset Positivity Checking`, which reach the same failures *by design* — are in
[`../../EscapeHatches/Coq/`](../../EscapeHatches/Coq/).

## Reproducing

```powershell
pwsh Shenanigans/KernelDefects/Coq/verify.ps1
```

Each exhibit is compiled in a scratch directory outside the repository, and the
script **asserts** both the verdict and a distinguishing substring of the output.
Expected final line: `All 4 Coq exhibits behaved as documented.`
Verified on **The Rocq Prover 9.2** (OCaml 4.14.2).

## Why these four, and why they cluster

All three guard-checker defects are failures of the *same* analysis — uniform
argument computation for nested mutual fixpoints — reached three different ways:
cross-calls, `let`-bound recursive aliases, and higher-order passing. That is why
they share a directory rather than being filed separately.

The clustering is structural rather than accidental, and it is the sharpest
Lean/Rocq contrast this repository has:

* Rocq checks recursion with a syntactic **guard checker** over `Fixpoint`
  definitions. Deciding termination from the shape of a term is subtle enough
  that a single refactor —
  [PR #17986](https://github.com/rocq-prover/rocq/pull/17986), the V8.20
  nested/uniform-parameter rework — introduced **four** separate proofs of
  `False`, of which three are witnessed here. Worse, the fix for one of them
  ([#20555](https://github.com/rocq-prover/rocq/issues/20555)) introduced
  another ([#21683](https://github.com/rocq-prover/rocq/issues/21683)), the
  `HigherOrderFixpoint.v` case. Lean compiles recursion to recursors and
  eliminators, so it has no guard checker and no analogue of this family.
* Rocq's **module system** — functors, aliases, `Include`, delta-resolution — is
  a large piece of trusted infrastructure with no Lean counterpart at all.
  `AliasChainDeltaResolver.v` is one of a family; [#21051](https://github.com/rocq-prover/rocq/issues/21051)
  is the same defect for non-aliased functors, and
  [#22287](https://github.com/rocq-prover/rocq/issues/22287) — a universe-flag
  desync on module close, still **open** — is the newest.

Neither observation makes Lean safer overall: see
[`../Lean/`](../Lean/) for its own defects, which cluster instead around
name-keyed normalizer extensions, unchecked term construction in the
nested-inductive path, and C++ fixed-width integer truncation. The point is that
the two systems' soundness risks live in structurally different places, so a
catalog of one says very little about the other.

## Sources

* Rocq's own [`dev/doc/critical-bugs.md`](https://github.com/rocq-prover/rocq/blob/master/dev/doc/critical-bugs.md)
  — the maintainer-curated ledger of every soundness bug since 8.0. There is no
  Lean equivalent.
* Tristan Stérin, [*In search of falsehood*](https://tristan.st/blog/in_search_of_falsehood)
  — the systematic AI-driven search that produced seven of the eight Rocq proofs
  of `False` from this wave, four of them witnessed here.
* The [`rocq-prover/rocq`](https://github.com/rocq-prover/rocq/issues) tracker,
  label `kind: inconsistency`.
* Full ledger with affected version ranges: [`../../CATALOG.md`](../../CATALOG.md) §4.

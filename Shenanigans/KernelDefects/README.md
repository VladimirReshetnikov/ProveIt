# Kernel defects: `False` with a clean audit

The only category in this directory that is anybody's fault. A defect belongs
here when the derived `False` is **closed** — no hypothesis, no flag, no
`sorry` — and the audit reports **nothing**:

```
'boom' does not depend on any axioms
```

That signature is exactly what a correct kernel is supposed to make impossible,
which is why every exhibit here ships with a control that produces the *same*
signature by cheating (see
[`Lean/Controls/NegativeControl.lean`](Lean/Controls/NegativeControl.lean)).
Acceptance of an exhibit means something only because the control is rejected by
the same procedure.

Contrast with [`../EscapeHatches/`](../EscapeHatches/), where the audit names
the cost, and [`../Paradoxes/`](../Paradoxes/), where the cost is a hypothesis
in the statement.

## Contents

| Path | System | Substance |
| --- | --- | --- |
| [`Lean/`](Lean/) | Lean 4 | The name-keyed accelerator family (`Nat.add`, `Nat.beq`, the nine free names under `Init.Prelude`, `Lean.reduceBool`, and string-literal fabrication), `Expr.proj` index truncation, definitional-equality history dependence, and level-normalization incompleteness. With [`Comparator/`](Lean/Comparator/), which shows the Lean FRO's proof judge accepting one of them. |
| [`Coq/`](Coq/) | Rocq 9.2 | Four soundness defects from the 2026 sweep — three guard-checker, one module-system — all fixed upstream, kept as regression witnesses that must be *rejected*. |

## Reproducing

```bash
pwsh Shenanigans/KernelDefects/Lean/verify.ps1
```
```bash
pwsh Shenanigans/KernelDefects/Coq/verify.ps1
```

Expected final lines: `All 6 modules behaved as documented.` and
`All 4 Coq exhibits behaved as documented.`

## Why the two systems' defects cluster in different places

Of the Rocq proofs of `False` catalogued in [`../CATALOG.md`](../CATALOG.md) §3,
the great majority are guard-checker or module-system bugs. Neither subsystem
exists in Lean. Of Lean's, essentially all are in the three kernel *extensions*
Lean 3's own FAQ told you to disable with `-t0`: GMP-accelerated `Nat`
arithmetic, structure eta, and nested inductives.

* Rocq checks recursion with a syntactic **guard checker** over `Fixpoint`
  definitions, whose job — decide termination from the shape of a term — is
  subtle enough that a single refactor
  ([PR #17986](https://github.com/rocq-prover/rocq/pull/17986)) introduced four
  separate proofs of `False`. Lean compiles recursion to recursors and has no
  analogue.
* Rocq's **module system** — functors, aliases, `Include`, delta-resolution — is
  a large piece of trusted infrastructure with no Lean counterpart at all.
* Lean's **name-keyed normalizer extensions** are a large piece of trusted
  infrastructure with no Rocq counterpart: the kernel builds
  `g_nat_add = mkConst {"Nat","add"}` at startup and fires on any constant with
  that name, never checking that it is the real one.
* Lean's kernel is written in C++ with **fixed-width integer fields**, and
  `size_t`→`unsigned` truncation has now produced the same class of defect twice
  four years apart ([#1433](https://github.com/leanprover/lean4/issues/1433) in
  2022, [#12746](https://github.com/leanprover/lean4/issues/12746) still open).

Neither observation makes either system safer overall. The point is that the two
systems' soundness risks live in structurally different places, so a catalog of
one says very little about the other.

## The status that matters most

The Lean accelerator family in [`Lean/Accelerators/`](Lean/Accelerators/) is
**reported and deliberately out of scope upstream**, not unreported.
[lean4#13626](https://github.com/leanprover/lean4/issues/13626) was closed
2026-05-04 with the maintainers' position stated explicitly:

> The kernel assumes that the official prelude is used. If you use `prelude` you
> are responsible for making sure it matches the kernel's expectations, i.e. It
> is not supported to write arbitrary code after `prelude`.

Every exhibit in that directory is a `prelude` module, so the policy covers all
of them — including `NatGcdFreeName.lean`, which redefines nothing. The exhibits
remain useful as a precise description of where that boundary lies and what is
on the far side of it, but they are a *policy* boundary, not an open hole.

`lean4lean`'s [`divergences.md`](https://github.com/digama0/lean4lean/blob/master/divergences.md)
states the same fact from the other side, and is worth quoting because it makes
the assumption explicit rather than treating it as obvious: Lean does not check
that primitives are declared with the correct types and definitional behaviour,
*"This is required for soundness, but Lean is able to get away with it because
Lean ships its prelude and using an alternative prelude is not supported."*

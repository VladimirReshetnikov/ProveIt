# Audits: searches for a route, and what they did not find

The other three categories exhibit ways to derive `False`. This one exhibits the
*absence* of one. Each subdirectory is a systematic search for a soundness hole
in a specific mechanism, and in every case the headline result is negative —
which is the useful part of the output, and the reason the harnesses are kept
rather than deleted.

Category (see [`../README.md`](../README.md)): none of these produces `False`.
Where a search turned up something real but sound, it is recorded as an
*anomaly* — a gap between a mechanism and its specification, not a defect.

The Rocq column of this directory is empty. That is a genuine gap, not a claim
that Rocq has no analogous questions; see [`../CATALOG.md`](../CATALOG.md) §5.

## Contents

| Path | Question asked | Answer |
| --- | --- | --- |
| [`Lean/Fuzz/NatAcceleratorBoundaries.lean`](Lean/Fuzz/NatAcceleratorBoundaries.lean) | Do the kernel's fourteen name-keyed `Nat` accelerators agree with the compiled implementation at powers-of-two boundaries? | 39,510 applications: **0 divergences** — but the sweep's `shiftLeft` cap hid a kernel abort, see below |
| [`Lean/Fuzz/LevelFuzzer.lean`](Lean/Fuzz/LevelFuzzer.lean) | Does the kernel's `Sort a ≡ Sort b` agree with denotational equality of the level expressions? | 880 random levels, 774,400 pairs: **0 unsound**, 162 incompleteness cases (very likely all instances of [lean4#12747](https://github.com/leanprover/lean4/issues/12747)) |
| [`Lean/Fuzz/DefEqFuzzer.lean`](Lean/Fuzz/DefEqFuzzer.lean) | Can `Kernel.isDefEq a b` hold when the kernel's own `whnf` gives `a` and `b` different `Bool` constants? | 3,354 differing pairs: **0 unsound** |
| [`Lean/Fuzz/CompilerKernelDiff.lean`](Lean/Fuzz/CompilerKernelDiff.lean) | Does `Lean.Kernel.whnf` ever disagree with the compiler on closed terms over `String`/`Char`/`Nat`/`Int`/`UInt`/`BitVec`/`List`/`Array`? | 72 terms: **0 divergences** |
| [`Lean/Metatheory/`](Lean/Metatheory/) | Is the `Acc` + proof-irrelevance interaction exploitable? Is `Expr.proj` conservative over the recursor? | No, and no — but both produce sound anomalies worth recording. See [`Findings.md`](Lean/Metatheory/Findings.md). |
| [`Lean/StringIdentity/`](Lean/StringIdentity/) | Do Lean's components disagree about when two strings — hence two `Name`s, hence two constants — are the same? | **No soundness loophole and no checker break.** Every disagreement found fails closed. One genuine machine-level defect: `Name.toString` is not injective. |

## The one defect this directory has produced

**`Nat.shiftLeft` aborts the kernel.** `example : (1 : Nat) <<< 4294967296 = 0 := rfl`
terminates the `lean` process with `INTERNAL PANIC: Nat.shiftl exponent is too
big` on every toolchain from `v4.31.0` to `v4.33.0-rc1`, under `--trust=0`, from
one line of ordinary source. `reduce_pow` bounds its exponent and declines
gracefully; the shift helper has no bound and the runtime aborts.

It is a robustness defect, **not** unsoundness — the process dies rather than
continuing with a wrong value, which is the precise difference from
[lean4#8554](https://github.com/leanprover/lean4/pull/8554), where a `panic!`
that did *not* abort made `hasFVar` non-conservative. Write-up and controls:
[`../Reports/2026-07-31-kernel-shiftleft-panic.md`](../Reports/2026-07-31-kernel-shiftleft-panic.md).

The provenance is the useful part: the fuzzer capped `shiftLeft`'s exponent at
4096 to avoid allocating gigabytes, and that cap is exactly what hid the defect
on the first pass. A bound introduced for the harness's own safety is a place
where the harness stops testing.

## The two findings worth carrying forward

**`Expr.proj` is strictly stronger than the recursor, and this refutes a
specification.** For the kernel-level inductive `I2 (a : Sort u) : Sort u | mk :
a → I2 a`, `I2.rec` is restricted to `Prop` motives while `Expr.proj` eliminates
into `Sort v`. It is sound — any substitution making the structure a `Prop` also
makes the field a `Prop` — but it refutes the "a projection is equivalent to an
application of the recursor" desugaring that Lean4Lean's specification of
`Expr.proj` rests on ([arXiv:2403.14064](https://arxiv.org/abs/2403.14064)).
Upstream has the same observation open as
[lean4#7637](https://github.com/leanprover/lean4/issues/7637): *"primitive
projections are currently not conservative over recursors."*

**The kernel's `is_def_eq` is not transitive.** `A ≡ B`, `B ≡ C`, `A ≢ C` for
closed terms over `Acc.rec`. This is incompleteness — the safe direction — and
Carneiro's thesis §3.1 already establishes it, but it is worth having measured,
because the Lean Kernel Arena has since made it an official test category:
`tests/undecidability/alg-conv-trans-acc` scores `either` precisely because
inventing the middle term is a step no algorithm takes. The arena's companion
tests go further and exhibit a **subject-reduction failure**: a term the kernel
accepts reduces to one it rejects.

Both of these say the same thing from different angles, and it is the honest
summary of this whole directory: **Lean's declared conversion relation and the
algorithm implementing it are not the same relation, and the gap is permanent,
not a bug.**

## The `StringIdentity` result, stated precisely

The motivating worry was real: `Name` is the identity of every constant in Lean,
`Name`s are built from `String`s, and wherever two components of a system
disagree about string equality, something can be slipped past the one that is
checking. The answer is that Lean is byte-exact and uniform internally, and
every decision path in [`leanprover/comparator`](https://github.com/leanprover/comparator)
carries names as structural `Lean.Name` — no normalisation, case folding,
collation or dot-splitting anywhere.

The headline lexical result is a negative one: **no character Lean accepts in a
*bare* identifier is one that collation-, NFKC- or `Cf`-stripping comparison
would treat as equal to its absence** — 0 of the 43 invisible/ignorable
characters tested. Every such character requires French quotes `«…»`, which are
conspicuous in source. That is a meaningfully better position than Rocq's, which
accepts bare Cyrillic homoglyphs; the comparison is drawn in
[`../EscapeHatches/Lean/Spoofing.lean`](../EscapeHatches/Lean/Spoofing.lean) §3
and its Rocq counterpart.

# Bounded arithmetic graphs for command tails

[`ArithmeticCommandWord254.lean`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandWord254.lean)
represents the actual command-tail lookup and replacement by fixed Σ0 formulas
in every IOpen model. Their standard-Nat interpretations agree with the
[checked numeric command codec](command_word254.md) on every input.
This is the arithmetic basis for the now checked
[concatenation history](arithmetic_command_append254.md) and a later numeric
proof compiler. The latter remains open.

The argument order is `tailDef(out,z)` and `replaceDef(out,z,rest)`.
Here z is an unshifted original candidate code. A nonempty shifted word must
first subtract1; empty word0 is handled separately. Every raw natural code
decodes as an actual command, so these functions have no invalid-command case.

For an operation tag below3, the command has one parameter followed by its
tail. For AX, it has three parameters followed by the tail. The graphs preserve
the exact operation and parameters, using respectively two or four nested
right Cantor projections to locate that tail.

All extracted input fields are bounded by z. New nested pairs are bounded by
the reconstructed output. This separation matters: replacing the tail of
`MP0` with0 yields output0 even when the old tail is arbitrarily large.
`tailValue_le` proves the uniform bound needed for the subsequent
course-of-values concatenation construction.

The stored audit checks11 named axiom reports and22 callers, including generic
unique totality, both command layouts, output0 after discarding a large tail,
and a concrete example where failing to unshift selects the wrong tail.
All use only standard Lean axioms. The
[verification record](results/arithmetic-command-word254-verification.json)
and [independent review](results/arithmetic-command-word254-review.json)
identify the exact sources and dependency objects. This module is outside the
Std-only core umbrella; its only imports are the native command-word adapter
and the represented literal Cantor pairing.

The maintained runner freshly checks Cantor and this module:38 axiom reports
and42 callers in total, with14 core imports matched to the successful169-unit
source/object evidence. It records five existing Cantor style warnings and
zero new warnings. No dependencies are rebuilt or downloaded.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_command_word254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/dependency-checkout \
  --core-evidence /path/to/successful-169-unit-verification.json \
  --core-cache /path/to/its/core-cache \
  --output /outside/new-empty-command-word-check
```

# Internal algebra of command words

[`ArithmeticCommandWordLaws254`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandWordLaws254.lean)
proves the word identities needed to compose the numeric compiler blocks.
They hold for arbitrary internal codes, without interpreting a nonstandard
code as an externally finite list.

For raw command code `z`, tail replacement preserves the outer tag, sets its
tail to the supplied word, and overwrites a previous tail replacement:

```text
first(replace(z, r)) = first(z)
tail(replace(z, r)) = r
replace(replace(z, r), s) = replace(z, s)
replace(z, tail(z)) = z.
```

These four identities hold in every IOpen model and follow from the actual
Cantor projections and the short/long command split. They retain every
command argument, including all three arguments under an AX tag.

In every IΣ1 model, represented concatenation also satisfies

```text
append(a, 0) = a
append(append(a, b), c) = append(a, append(b, c)).
```

The proofs use Σ1 order induction on the left word; the other operands stay
fixed. The tail bound places each induction call below the current shifted
word. The established exact append recurrence and tail-replacement identities
then prove the equations. This avoids an induction over external command
lists, which would not cover all internal inputs.

The [verification](results/arithmetic-command-word-laws254-verification.json)
and [independent review](results/arithmetic-command-word-laws254-review.json)
cover six axiom reports and seven callers, including composition of four
words. The narrow check reuses the represented-append prerequisites and
freshly checks only this extension and its audit. The identities do not yet
prove command execution or the PA consistency equivalence.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_command_word_laws254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/dependency-checkout \
  --append-evidence /outside/successful-command-append/verification.json \
  --output /outside/new-empty-command-word-laws-check
```

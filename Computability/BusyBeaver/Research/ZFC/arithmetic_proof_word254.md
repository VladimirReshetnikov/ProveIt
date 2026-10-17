# An arithmetic history of compiled proof words

[`ArithmeticProofWordRow254`](../../Lean/BusyBeaver/ZFC/ArithmeticProofWordRow254.lean)
and [`ArithmeticProofWord254`](../../Lean/BusyBeaver/ZFC/ArithmeticProofWord254.lean)
represent a numeric proof-to-word computation at every internal input of an
IΣ1 model. Fixed Σ1/Δ1 graphs define an unconditional history of command words
and a public output gated by the existing twelve-rule proof checker. The
module proves actual IΣ1 and PA derivability of the output's unique totality.
Its command execution contract remains open.

The history starts with word 0 at proof code 0. At index `raw + 1`, it splits
`raw` into tag `raw % 12` and payload `raw / 12`, decodes that payload, and
selects one of the [actual compiler blocks](arithmetic_command_blocks254.md).
The step index is already the predecessor; there is no second subtraction.

| Proof tag | Unconditional word construction |
| --- | --- |
| 0 | Discard block, independently of payload validity. |
| 1 | MP block, using both earlier child words. |
| 2 | GEN block, using the child code in the whole payload tail. |
| 3–10 | The eight original leaf blocks, with the original argument projections. |
| 11 | Bundle leaf, independently of its freshness gate. |

The row graph accepts arbitrary tags and returns zero outside these twelve
cases. The actual history selects tags by remainder modulo 12. Its earlier
entries are command words, not checker results. Invalid nodes receive raw
words with no execution guarantee.

The internal prefix theorem identifies every bounded history entry with
`rawWord` at that code. Child bounds come from the already proved Cantor and
quotient inequalities. This yields the exact course-of-values recurrence
for every internal proof code. Out-of-range history lookups are separately
proved to be zero.

The public function is

```text
compiledWord(code) =
  if ArithmeticHistory254.value(code) = 0 then 0 else rawWord(code).
```

Thus validation remains the original computation, used once at the output.
A rejected proof gets the empty shifted word; an accepted proof gets its raw
compiled word. An accepted MP or GEN parent has accepted children by the
[internal checker recurrence](arithmetic_history_recurrence254.md), supplying
the hypotheses needed for the later execution induction.

Three zero conventions remain distinct: proof code 0 is invalid, shifted
word 0 is empty, and raw candidate 0 is the actual command `MP 0`. This module
does not execute an empty word by decrementing it to a raw candidate.

The fixed totality sentence says that every proof code has a unique output
satisfying `compiledWordDef`. Arithmetic completeness is applied after
establishing that sentence in every IΣ1 model. The standard-model theorem
`compiledWord_nat_gate` identifies the validator gate with the existing
natural checker; agreement of the entire raw word with the structural
compiler is a separate subsequent adapter.

The [verification](results/arithmetic-proof-word254-verification.json) freshly
checks both new modules and their audit, with twenty-eight axiom reports and
twenty-one callers, using only standard Lean axioms and no warnings. The
[independent review](results/arithmetic-proof-word254-review.json) checks the
rule arguments, internal recurrence, single validator gate and provider
identities. The combined prerequisite cache records which checked Cantor
object it selects: prior runs had the same source but distinct object bytes.
They are recorded separately rather than treated as identical objects.

The reproducible runner accepts explicit successful prerequisite records and
relocated matching caches. Its default source and audit identities are fixed:

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_proof_word254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/dependency-checkout \
  --blocks-evidence /outside/successful-command-blocks/verification.json \
  --recurrence-evidence /outside/successful-history-recurrence/verification.json \
  --output /outside/new-empty-proof-word-check
```

The remaining obligations include full compiler agreement, accepted-proof
execution, scheduler and binary-trace transport, and internal proof
transformations between C254 and ZFC. Unique totality alone establishes none
of those comparisons and changes no machine state count.

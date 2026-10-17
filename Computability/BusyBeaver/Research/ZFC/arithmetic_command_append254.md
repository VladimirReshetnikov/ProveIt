# Represented concatenation of command words

[`ArithmeticCommandAppend254`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandAppend254.lean)
represents concatenation of the actual shifted command-word codes by fixed
Σ1 and Δ1 formulas. It proves unique total evaluation in every IΣ1 model,
including nonstandard inputs, and agrees with the native command-list
concatenation on every pair of ordinary natural numbers.

The public graph has arguments `appendDef(out, left, right)`. Empty word 0
remains distinct from raw candidate 0, which encodes `MP 0`. The definitions
do not execute an empty word as that candidate.

## The internal recurrence

For a fixed right word, a primitive-recursive history begins with that word
at index 0. At successor index `raw + 1`, it stores

```text
replaceValue(raw, history[tailValue(raw)]) + 1.
```

Here `raw` is already the predecessor of the shifted word code. Subtracting
again would select a different command. The earlier bounded tail theorem gives
`tailValue(raw) ≤ raw`, so the child lookup is inside the existing history.

The new bounded-induction lemma proves, at every internal index,
`history[left][i] = appendValue(i, right)` for `i ≤ left`. Together with the
exact sequence-append equations this yields

```text
appendValue(0, right) = right
appendValue(raw + 1, right) =
  replaceValue(raw, appendValue(tailValue(raw), right)) + 1.
```

The same module proves that every lookup beyond the history is zero, and
that `appendValue(left, right) = 0` exactly when both inputs are zero. The
latter will justify positivity when constructing a nonempty refutation word.

Strong induction over ordinary Nat identifies this recurrence with the
[native word adapter](command_word254.md) on all codes. No parser-validity or
fuel premise occurs in that identification. The module also exports actual
IΣ1 and PA proofs of the fixed sentence asserting unique append evaluation.
Those are totality theorems; compiler execution and the PA consistency
equivalence remain separate obligations.

## Verification

The [verification record](results/arithmetic-command-append254-verification.json)
and [independent review](results/arithmetic-command-append254-review.json)
identify the final source and audit. The audit has 24 named axiom reports and
30 callers, covering arbitrary internal inputs, the exact recurrence,
nonempty output, out-of-range lookups, native list concatenation and the two
object-theory totality results. All reports use only standard Lean axioms.

The narrow runner reuses the checked Cantor and command-tail modules and
their 14 matched core imports. It freshly compiles only this extension and
its audit. For a fresh arithmetic prefix, first run
[`check_arithmetic_command_word254.py`](check_arithmetic_command_word254.py),
then supply its output record here:

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_command_append254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/dependency-checkout \
  --command-word-evidence /outside/command-word-check/verification.json \
  --output /outside/new-empty-command-append-check
```

The [command-block circuits](arithmetic_command_blocks254.md) now use this
append graph to represent the actual leaf, MP and GEN command constructors.
Their symbolic encodings agree with the existing compiler blocks.
The [internal word laws](arithmetic_command_word_laws254.md) additionally
prove right identity and associativity in every IΣ1 model, using the exact
recurrence and raw tail-replacement identities.

No compiler, scheduler or binary simulation theorem is inferred from these
arithmetic operations. The next compiler uses a history of raw command words
and the existing proof checker as a final validity gate; invalid public
outputs are empty word 0.

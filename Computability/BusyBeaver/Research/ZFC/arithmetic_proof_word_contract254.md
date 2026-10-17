# A Π1 induction interface for compiler correctness

[`ArithmeticProofWordContract254`](../../Lean/BusyBeaver/ZFC/ArithmeticProofWordContract254.lean)
proves that the required compiler contract admits induction in IΣ1. It
retains arbitrary initial top and saved-stack registers, which the MP case
needs when it executes its major premise on a changed stack.

The contract says that a word, started with accumulator and cache zero,
either halts or returns its specified conclusion with the saved stack intact:

```text
Contract(word, target) :=
  forall top, stack,
    eval(word, state(top, stack, 0, 0)) = 0
    or eval(word, state(top, stack, 0, 0)) = state(target, stack, 0, 0)+1.

Good(code) := validator(code)=0
  or Contract(rawWord(code), validator(code)-1).
```

The validator, raw-word generator, evaluator and state constructors are
total Δ1 functions. Their equality predicates are therefore Δ1, and the
universal top/stack quantifiers make `Good` a Π1 predicate. The bounded
prefix `forall i <= code, Good(i)` is also Π1. The checked arithmetic library
supplies Π1 induction in every IΣ1 model. No bound on changing registers or
compiler output sizes is introduced.

`good_of_step` reduces the full theorem to the exact successor premise
`forall raw, PrefixGood(raw) -> Good(raw+1)`. The premise remains explicit:
this module alone does not assert that the twelve-case row step holds.
`major_input_of_prefix` separately demonstrates that an accepted earlier
child's contract applies at top zero and stack `P(minorTarget, savedStack)`.
The halt alternative remains necessary because an intermediate NIP may
encounter falsity even when the final target differs from falsity.

The [verification](results/arithmetic-proof-word-contract254-verification.json)
freshly checks the module and its six-probe/eight-caller audit, with only
standard Lean axioms and zero warnings. It reuses 31 matched project
prerequisites; different Cantor objects with identical sources are recorded
as distinct alternatives. The [independent review](results/arithmetic-proof-word-contract254-review.json)
checks the Π1 classification, changed-stack instance and explicit remaining
premise. The portable wrapper also passes preparation with maintained
sources. This later preparation does not invoke Lean or repeat the proof
check.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_proof_word_contract254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --word-evidence /outside/successful-proof-word/verification.json \
  --run-evidence /outside/successful-command-run/verification.json \
  --output /outside/new-empty-contract-check
```

The next module must discharge the successor premise from the actual
validator recurrence, child bounds and compiler-block contracts. This
induction interface alone proves no consistency equivalence or machine bound.

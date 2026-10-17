# An internal refutation word for every accepted falsity proof

[`ArithmeticRefutationWord254`](../../Lean/BusyBeaver/ZFC/ArithmeticRefutationWord254.lean)
constructs an explicit represented word that halts from every internal
working-state code whenever the actual validator returns 2: conclusion 1
(falsity) plus its acceptance marker. The word is the literal `AX(0,1,1,0)`
prefix followed by the unchanged raw compiled proof and the original
`DROP0, NIP0, NIP0` terminator.

AX clears the accumulator and cache. Its new top and saved stack may contain
arbitrary internal values, which the [compiler contract](arithmetic_proof_word_correct254.md)
already handles. The compiled proof either halts or leaves falsity on top
with accumulator/cache zero. In the latter case the terminator loads falsity
into cache and halts on its final NIP. Cantor projection/reconstruction
expresses every working code as a four-register state; the theorem requires
no special initial registers.

The word has a fixed Σ1 graph and a unique positive output for every internal
proof code, including invalid codes. Its halting contract applies to accepted
falsity proofs. Both the word and the universally quantified working code
range over the arbitrary IΣ1 model.

The [fresh source and audit check](results/arithmetic-refutation-word254-verification.json)
passes eleven axiom reports and twelve callers, with standard axioms only
and zero warnings. It reuses 38 source/object-matched project modules. The
[independent review](results/arithmetic-refutation-word254-review.json)
checks the arithmetic quantifiers, reset and termination arguments, and
exact artifacts. The portable wrapper passes maintained-default preparation;
that preparation invokes no Lean process.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_refutation_word254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --correct-evidence /outside/successful-correctness/verification.json \
  --output /outside/new-empty-refutation-check
```

This supplies the represented compiler-to-command-word refutation direction.
The subsequent [scheduler composition](arithmetic_enumerator_refutation254.md)
now proves the forward scheduling implication in PA. Command-halting
soundness from a certified initial state, arithmetic-to-binary simulation and
the internal PA consistency equivalence remain open.

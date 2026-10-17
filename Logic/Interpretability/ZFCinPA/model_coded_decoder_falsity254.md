# Decoded falsity and primitive contradiction

[`ModelCodedDecoderFalsity254`](Lean/ZFCinPA/ModelCodedDecoderFalsity254.lean)
proves, in every IΣ1 model,

```
Provable ZF (decode 1) ↔ Provable ZF Bottom.
```

The decoder's source code 1 is membership(0,0), with free label zero.
It is not the target syntax for Bottom. The forward direction first supplies
an actual internal proof of its negation and then cuts the two proofs.
The reverse direction uses an explicit explosion proof constructor.

The ordinary fixed sentence `∀ x, x ∉ x` follows from Pairing and Foundation:
apply Foundation to the singleton of x. The proof uses the existing
completeness theorem for this one standard sentence, including its handling
of equality structures. D1 then quotes that finite ZF theorem into every IΣ1
model. The checked `specializeCode` opens its bound variable at free label
zero. This does not invoke semantic completeness for arbitrary internal
formula or proof codes, and does not require an internal formula to be
standard.

The generic contradiction and explosion operations have fixed total Σ1
graphs. They construct literal cut, weakening and truth-introduction codes
from supplied internal proofs. Their validity theorems use the actual
internal `Proof` predicate and the expected formula-typing premises.

The [successful check](results/model-coded-decoder-falsity254-verification.json)
passes eight ordered axiom reports and twelve callers, using only the three
standard Lean axioms, with zero warnings. Source and audit took 4.663 and
2.377 seconds on pinned Lean 4.32.0, one thread and a 4 GiB limit. The exact
24-project closure, six external boundaries, actual first Lean/Omega
providers, all 71 inputs and the fresh object are checked. No dependency was
built or downloaded.

The three failed attempts needed explicit model-binder types, a fixed universe
for ordinary completeness, the actual membership-operator API, and quotation
numeral identities. The final theorem statements and raw proof operations
are unchanged. Records, logs and source differences are preserved in the
[publication record](results/model-coded-decoder-falsity254-publication.json).

The maintained successful record is byte-identical to the original. The
portable runner freezes the final source/audit hashes; default and relocated
preflights run no Lean proof builds. Four controls reject Python `-O`, nonempty
output, a wrong first Omega provider and a corrupted isolated MP object.

```sh
python -B Logic/Interpretability/ZFCinPA/check_model_coded_decoder_falsity254.py \
  --dependency-root /path/to/built-dependency-checkout \
  --output /fresh/external/decoded-falsity-check
```

`--decoder-cache` relocates all 24 exact project objects, and
`--namespace-cache` supplies the complete Foundation namespace mirror.
`--prepare-only` validates preparation without compiling proofs.

This closes the decoded-falsity endpoint. Translation of accepted C254
histories into ZF proofs, the full binary runtime refinement and the PA
nonhalting/consistency equivalence remain separate.

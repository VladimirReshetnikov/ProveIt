# Source-only review of endpoint drafts

The following source hashes were inspected against the relevant native
endpoint, erasure, embedding, induction and syntax definitions:

| Draft | SHA-256 |
| --- | --- |
| `IPRAReferenceAQ29.lean` | `f3bc3a57bf0a5352da4bb43c2e59fa8f67020ebc8254a3653633da15fadde5e8` |
| `IPRAReferenceNoZero.lean` | `dc7aedc9022416a273d42a2c92f54f953b2c493c77a0ffb651938642a9a5e100` |
| `IPRAReferenceRefutationReading.lean` | `f1b8bd5f0cd6309bb3f61b7a4559f28a9d1bcab80a278037fd16c430f60e557e` |
| `IPRAReferenceAQ29Direct.lean` | `04488adfc9ad5cd62b08311f60f6a433ea653e044cc2450ce029bc52c5c93c50` |
| `IPRAReferenceRoundtrip.lean` | `d7d59614ae1e1fe859cfc458ee08b64555ad5b8b16e3f2956a3033c1c0dfc619` |
| `IPRAReferenceInductionTransfer.lean` | `7f1886edb6c6402bb45e86f02bb9ed15d8f5cc3ba8113fed86edbd073c5c437d` |

The proposed AQ29 assembly uses the same positive-shift expression as the
native theorem, and the no-zero reader retains its two split-natural terms.
The direct refutation reader takes the same Foundation `rho`, reads equality
and less-than via the stated PR-code translation, and uses the intended
rewrite direction in the assembled endpoint. The roundtrip's equality and
defining image lemmas return complete native axioms, which the current source
uses directly. No additional definite typing or rewrite mismatch was found
in this limited source inspection.

**No Lean elaboration was run.** In particular, dependent pattern matching
and simplification in the NNF reader, the no-zero `congr` and finite-vector
steps, the induction wrapper's definitional equality, draft imports, and the
AQ29 endpoint's final simplification remain untested. Source inspection does
not establish a proof, a coherent object provider, standard-model semantics,
or equivalence with any alternative ZFC proof coding.

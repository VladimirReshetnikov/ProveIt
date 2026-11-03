# Independent 90-operation iPRA join audit

The retained attempt03 result reports `PASS`. Its endpoint contains four
closed Lean entailments, with no explicit theorem hypotheses. Let `N` be
`IPRAExpressionNative.nativeNoZero (positiveShift (graph byteP).output)`,
`R` be `mappedNativeRefutation embedding`, and `C` be
`Semiformula.lMap embedding sourceSentence`. The exact statements are:

| Theorem | Theory | Proven equivalence |
| --- | --- | --- |
| `standard_consistency` | `standardTheory` | `N 🡘 ∼R` |
| `standard_translated_consistency` | `standardTheory` | `N 🡘 Cᴺ` |
| `reference_consistency` | `referenceTheory` | `erase N 🡘 ∼erase R` |
| `reference_translated_consistency` | `referenceTheory` | `erase N 🡘 erase (Cᴺ)` |

Here `graph byteP` is the fixed four-byte-port 90-operation Lean graph;
`positiveShift` replaces each input by its successor before the no-zero
sentence is formed. `sourceSentence` is Foundation's ZFC consistency
sentence, and `ᴺ` is the repository's negative translation. The fourth
theorem therefore refers to the erased negative translation, not an assertion
that the displayed PDF has been parsed in Lean or that an untranslated
classical consistency sentence is literally the right-hand formula. The
theory, encoding, and translation definitions in the repository are
authoritative. The two additional endpoint lemmas establish the positive
model bridges used to construct these four derivations.

The independent retained check reconstructed the initial and final fresh
project union, compared all 425 producer receipts and dependency guards with
their selected current files, and verified the exact QSchema-repair and
stage-425 receipts. It checked all eight compiled source copies, stage
commands and output objects/companions; stage 04 had exactly the separately
approved three warnings and all other stages had no detected warning or
error. All six endpoint axiom reports list only `propext`,
`Classical.choice`, and `Quot.sound`.

It parsed every retained header-reader log and independently recomputed
reachability: 1,605 selected project modules and 79 direct external names
before compilation, then 1,609 project modules and 79 external names after
compilation. It checked that all eight newly built stages are selected by the
final closure, that the four affected standard modules replace the old
objects, and that recorded direct package/sysroot files and companions remain
unchanged. It also checked every recorded preflight and sampled resource
measurement. Samples are periodic, not continuous monitoring.

The independent observation exited zero with empty stderr and did not replay
Lean. The author observed the outer attempt03 process exit zero in its tool
terminal; no separate outer-process receipt was persisted, so that exit is
author-observed rather than independently authenticated here. Individual
stage and header-reader exits and logs are retained and checked. The selected
project objects and direct package/sysroot inputs were audited, while full
package-transitive, dynamic, and historical source-to-object ancestry remain
outside this audit. The external decimal 90-row PDF was checked separately;
there is no Lean parser or file theorem binding it to `graph byteP`.

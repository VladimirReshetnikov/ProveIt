# Independent 89-operation iPRA join audit

The retained author join and its separately captured outer process both
report success. Its endpoint contains four closed Lean entailments, with no
explicit theorem hypotheses. Let `N` be
`IPRAExpressionNative.nativeNoZero (positiveShift (graph byteP).output)`,
`R` be `mappedNativeRefutation embedding`, and `C` be
`Semiformula.lMap embedding sourceSentence`. The exact statements are:

| Theorem | Theory | Proven equivalence |
| --- | --- | --- |
| `standard_consistency` | `standardTheory` | `N 🡘 ∼R` |
| `standard_translated_consistency` | `standardTheory` | `N 🡘 Cᴺ` |
| `reference_consistency` | `referenceTheory` | `erase N 🡘 ∼erase R` |
| `reference_translated_consistency` | `referenceTheory` | `erase N 🡘 erase (Cᴺ)` |

`graph byteP` is the fixed-byte-port 89-operation Lean graph; the positive
shift replaces each input by its successor. `sourceSentence` is Foundation's
ZFC consistency sentence, and `ᴺ` is the repository's negative translation.
The theory, encoding, and translation definitions are authoritative. Two
additional endpoint lemmas provide the symbolic and byte-port positive model
bridges. All six endpoint axiom reports list only `propext`,
`Classical.choice`, and `Quot.sound`.

The independent check verified the outer exit-0 receipt, endpoint source,
command, log, output object and companions, and sampled resource guards. It
reconstructed the fresh union of 2,707 initial files and 2,708 final files,
rechecked the prior 90 endpoint and its 425 producer receipts, and checked the
89-halt selected objects and companions. It parsed all 64 retained post-header
batches and recomputed reachability: 1,631 selected project modules and 79
direct external names. It verified every final selected project object and
companion and the direct package/sysroot selections. Samples are periodic,
not continuous monitoring.

The author result SHA-256 is
`77d82979cc040aadecad2e859e69037f8de1d4a70bda65a6457f47d97d73dc4e`;
the endpoint object SHA-256 is
`9fa5ea9073d2190c130465ef26a7bf9554548746c4649da080e02a252e1d45e2`.
The independent observation exited zero with empty stderr. It did not replay
Lean, and full package-transitive, dynamic, and historical source-to-object
ancestry remain outside its scope. The separate decimal PDF has external
graph and payload checks, but no Lean parser or file theorem binds it to this
expression.

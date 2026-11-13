# Independent review of the standalone 13/87 iPRA source

The proposed three endpoint statements and their proof directions agree with the existing source interfaces; no concrete source-level mismatch was found. The draft's `noZero87` is byte-identical to the corresponding definition in the retained 86/87 native endpoint. It denotes the split-natural no-zero sentence for the positive shift of the literal 13-variable expression at the current four ports. The checker independently parses all 87 row declarations, variable and port indices against the pinned graph, checks their live input domain and operation census, reruns the published degree-51 factor certificate, and reproduces the author's receipt. Those checks remain external Python evidence rather than Lean file semantics or a PDF interpretation.

The distinction between targets is correct. The imported `translated_refutation` yields `noZero87 ↔ ∼(lMap embedding refutation)ᴺ`. `equationComparison` takes that intermediate and `zfcEquiv` to yield `noZero87 ↔ ∼mappedNativeRefutation embedding` in `nativeTheory`. `IPRAStandardTheory.provable_iff` is oriented `standard ↔ native`, so `.2` is the correct transfer from native to standard. The separate translated client uses `zfcEquiv` in the other role: because it states translated `sourceSentence ↔ ∼mappedNativeRefutation`, its right-to-left direction follows the no-zero-to-native-refutation direction, while its left-to-right direction precedes the converse. Both displayed entailment compositions have that order. They do not prove either sentence or identify every other possible consistency coding.

The retained matched 236-module fixed-snapshot continuation provides additional historical evidence beyond the draft's earlier translated-refutation record: it reports matched author/independent `IPRAAdaptiveNativeZFC.equivalence87`, and the target source, 87 translated-refutation source and 87 literal source are byte-identical to the current workspace. Its object hashes and direct inputs match across the paired states. It is still historical: the comparison documents source drifts, inherited project-origin qualifications and package/dynamic ancestry, and it did not compile this new standalone client. There is no separate established theorem about physical `equation.pdf` for this graph. Source/object compatibility, tactic elaboration, the new standalone endpoint and axiom reports remain unverified.

The checker pins its inputs, runs the author's checker and existing degree certificate, compares the exact sentence and composition interfaces, checks the historical paired rows and independently parses the 87 source/graph rows. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/current2011-adaptive87-ipra-standalone-independent/check.py | cmp - reviews/current2011-adaptive87-ipra-standalone-independent/receipt.json
```

No Lean/build/staging or edit to the author packet was performed.

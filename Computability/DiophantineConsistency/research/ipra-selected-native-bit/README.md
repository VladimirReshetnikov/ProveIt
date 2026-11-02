# Intuitionistic Boolean range for the selected bounded checker

This exploratory Lean extension strengthens the existing
[`selected_checker_endpoints`](../ipra-selected-refutation-verifier/draft-src/IPRASelectedCheckerConsistency.lean)
result. It defines `nativeBitSentence c` as the universal closure of the
native reading of `bitMatrix c`: at every input, the selected code returns
zero or one. The theorem `nativeBitOfClassical` shows that the previously
proved classical-PRA `bitSentence c` yields an actual derivation of this
native bit sentence in `nativeTheory`. The proof applies the existing
`IPRABitConvention.transferOpen` uniformly to the open bit matrix and closes
the resulting family with `IPRANativeDisjunctionWitness.closeFamily`; it
does not attempt the problematic atom-by-atom rewriting of the earlier drafts.

The theorem `selected_checker_boolean_endpoints` then states that **one and
the same** arity-one primitive-recursive code has a provable Boolean-range
sentence in each of `nativeTheory` and `standardTheory`, and that the
standard theory proves both 13-variable no-zero sentences equivalent to the
absence of a bound on which this code returns one. The code is existentially
chosen in Lean; no numeral is extracted. The checker still concerns the
bounded matrix of Foundation's selected ZFC refutation formula, not a
separately specified proof-code verifier. This result does not assert ZFC's
consistency or compare the selected encoding with arbitrary other encodings.

The proof was run twice in an exploratory overlay whose `LEAN_PATH` is
`/tmp/ipra-selected-verifier-guarded-author-20261101/lib`, then
`/tmp/ipra-aq29-fresh-project-pair/author/lib`, then
`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`. It relies on the
existing guarded selected-checker author outputs and their audited parent,
rather than rebuilding their ten additions in the same invocation. The actual
successful terminal exits and the earlier failed native-bit attempts are
recorded in [`exploratory/terminal-observation.json`](exploratory/terminal-observation.json);
the second successful invocation's full diagnostic output is
[`exploratory/native-bit.log`](exploratory/native-bit.log). Lean reports
`propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`. These are
Lean metatheory dependencies, not additional object-theory axioms. This is
not yet a guarded complete-chain or matched peer replay. The earlier
selected-checker packet's historical parent, package-transitive, dynamic,
between-observation and Foundation wrapper-exit qualifications apply.

# Sign25 no-alias endpoint attempt: partial failure

The author observed outer runner session `64713` exit **1**. The first stage,
`Sign25DirectNoAliasNative`, compiled with child exit 0 and recorded an object
hash. Its `native_equivalence` theorem report lists the metatheory axioms
`propext`, `Classical.choice`, and `Quot.sound`. The second standard endpoint
stage passed dependency inspection but failed compilation with child exit -6
and a Lean interpreter memory exception under `-M2800`. The translated stage
and final runner postflight were not attempted.

The native theorem is a successful child result within an overall failed run;
it requires independent source, provider and artifact audit and does not
establish that the full runner passed or that the standard and translated
endpoints compiled. Sampled memory and point-time provider guards are not a
complete dynamic or package-transitive ancestry trace. The output uses the
existing Fin25 symbolic expression; no nine-variable Jones endpoint, Lean
degree, external JSON semantics or PDF binding follows. Captured state and
logs are copied from the isolated output. The separately recorded numeric
outer exit is not inferred from child state. The [independent terminal
audit](../../../reviews/nine-sharing-sign25-endpoint-no-alias-terminal-independent/README.md)
checks the partial result, including its provider limitations.

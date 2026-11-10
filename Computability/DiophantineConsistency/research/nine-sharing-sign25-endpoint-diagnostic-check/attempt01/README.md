# Sign25 split endpoint diagnostic: failure

The author observed outer runner session `13406` exit **1**. The first stage,
which only imports `Sign25DirectPolynomialBridge`, compiled with exit 0 and
an object hash in `state.json`. The second stage, which includes local
irreducibility attributes and the `Fin 25` expression alias, passed dependency
inspection and failed compilation with child exit -6 and a Lean interpreter
memory exception under `-M2800`. Neither the bridge theorem nor axiom-report
stages were attempted, and final postflight did not run.

The successful import and failed second stage narrow the failure to this
diagnostic's second invocation; they do not distinguish import-boundary,
attribute or alias elaboration as the trigger. Sampled memory and provider
guards retain the limits described by the runner, without a complete dynamic
ancestry guarantee. No iPRA endpoint, Lean degree, JSON or PDF result follows.
Logs and state are copied from the isolated output; `outer-result.json`
records the observed numeric session exit separately. Independent audit is
available [here](../../../reviews/nine-sharing-sign25-endpoint-diagnostic-terminal-independent/README.md).

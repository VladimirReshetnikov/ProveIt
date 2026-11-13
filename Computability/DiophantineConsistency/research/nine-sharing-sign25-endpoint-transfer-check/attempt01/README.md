# Sign25 direct theory-transfer wrapper: failure

The author observed outer runner session `76453` exit **1**. The first standard
wrapper's dependency scan succeeded, but Lean compilation exited -6 with an
interpreter memory exception under `-M2800`. Replacing the intermediate iff
projection with direct `transfer native_axiom` therefore did not make this run
pass. The translated stage and final postflight were not attempted; the
precise cause of the interpreter exception remains unknown.

The provider is the independently audited successful native child of a
previous failed outer run, not a producer with successful full postflight.
This attempt creates no standard or translated endpoint. Point-time guards,
sampled resource observations and inherited ancestry carry their documented
limitations; no Lean degree, external JSON or PDF binding follows. The isolated
state and logs are copied here and `outer-result.json` separately records the
numeric outer exit. The [independent terminal audit](../../../reviews/nine-sharing-sign25-endpoint-transfer-terminal-independent/README.md)
checks the failed result and partial-provider scope.

# Sign25 wrappers using partial native provider: failure

The author observed outer runner session `95304` exit **1**. The first standard
wrapper's dependency scan succeeded but Lean compilation exited -6 with an
interpreter memory exception under `-M2800`, despite the local irreducibility
settings. The translated wrapper and final postflight were not attempted. The
precise failure cause is unknown.

The provider is the previously independently audited successful native child
of a failed outer run, not a producer with successful full postflight. This
attempt creates no standard or translated endpoint. Point-time provider
guards and sampled resource observations carry their documented limitations;
no Lean degree, external JSON semantics or PDF binding follows. The isolated
state and logs are copied here, and `outer-result.json` separately records the
observed numeric session exit. The [independent terminal audit](../../../reviews/nine-sharing-sign25-endpoint-wrappers-terminal-independent/README.md)
checks the partial-provider and failure evidence.

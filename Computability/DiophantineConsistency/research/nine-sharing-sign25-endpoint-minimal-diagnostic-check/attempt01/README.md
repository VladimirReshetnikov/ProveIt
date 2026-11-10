# Sign25 minimal endpoint diagnostic: failure

The author observed outer runner session `59941` exit **1**. The first stage,
which imports the bridge and checks the existing bridge theorem, compiled with
child exit 0 and an object hash in `state.json`. The second stage, which adds
the typed Fin25 expression alias without local irreducibility attributes,
passed its dependency scan and failed compilation with child exit -6 and a
Lean interpreter memory exception under `-M2800`. The separate attribute-only
stage was not attempted, and final postflight did not run.

This shows that local irreducibility attributes are not required for this
diagnostic's alias-stage failure; the alias module also has namespace, section
and `open` commands, so its precise failing command is not isolated. Sampled
memory and provider guards retain their documented limits and are not a full
dynamic ancestry trace. No iPRA endpoint, Lean degree, JSON or PDF result
follows. Logs and state are copied from the isolated output; the separate
`outer-result.json` records the numeric outer exit. The [independent terminal
audit](../../../reviews/nine-sharing-sign25-endpoint-minimal-diagnostic-terminal-independent/README.md)
checks the retained evidence and qualification.

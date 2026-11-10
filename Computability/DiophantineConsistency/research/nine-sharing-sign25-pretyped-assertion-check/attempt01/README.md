# Sign25 pretyped full assertion: partial failure

The author observed outer session `91004` exit **1**. The first generic
standard theorem and generic equality-transfer theorem compiled with child
exit 0, an object, and axiom reports `[propext, Classical.choice, Quot.sound]`.
The second full concrete assertion and definitional equality also compiled
with child exit 0, an object and the same reported metatheory axioms. The third
stage, specializing the generic theorem via the pretyped assertion and sign25
bridge, passed dependency inspection but its compile exited -6 with an
interpreter memory exception under `-M2800`. The original-assertion wrapper
and final postflight were not attempted.

The first two stages are successful children of an overall failed run and
require independent source/provider/artifact audit. They do not establish a
concrete sign25 standard or translated endpoint. Point-time guards, sampled
resource observations and inherited provider ancestry carry their documented
limits; no Lean degree, external JSON semantics or PDF binding follows. Copied
logs and state are retained here, and `outer-result.json` records the observed
numeric outer exit separately. The [independent partial terminal audit](../../../reviews/nine-sharing-sign25-pretyped-assertion-terminal-independent/README.md)
checks those results and qualifications.

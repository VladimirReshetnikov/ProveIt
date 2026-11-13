# Thirteen-variable 70/140 and 71/128 forms

This is the adapted `ModelThirteenForms` source from the fresh-model packet,
compiled against the checked four-helper completion/bridge and the captured
current-base provider overlay. It proves same-valuation zero equivalences
from `expressionAt70` and `expressionAt71` to `expressionAt69`, the
corresponding bridges, and native/standard iPRA mapped-refutation
biconditionals. The external JSON/graph-to-source binding is a separate
[frontier audit](../../reviews/thirteen-current2011-forms-frontier-independent/README.md).

Actual outer session 79419 exited 0; both nested Lean runs exited 0. The
compile log retains two linter warnings about unused section variables and
an unused variable name; it contains no error or `sorry` report. The retained
[state](attempt01/state.json) SHA-256 is
`a7a108e579b6a18f357efacbbc5c8547831b555bfcb3507bf72d34dd8a58aa1f`;
the output object SHA-256 is
`34445fbe3361116a892e8b5a351c2957fb4cad700179dd0b4212421f8cc7067d`.
The source SHA-256 is
`788fb1c2a31d04dc6848243423306f4d64d5b5c5069d09ea60ec584520dcb554`;
the runner SHA-256 is
`871205246e00c52bb71b9a86f3d450aa9053092b3596821c525465abf3722cce`.
Compilation ran 5.604 seconds, with peak sampled session RSS 2,894,278,656
bytes and minimum sampled host available memory 18,812,813,312 bytes; no
stop, descendant or monitor error was recorded.

The subsequent [axiom-report client](../thirteen-current2011-final-checks-4g/README.md)
checks the two standard endpoint declarations. This run uses a sampled 5-GiB
session RSS stop, sampled 10-GiB host floor, 180-second timeout and Lean
`-M4000`; transient spikes, escaped descendants, complete dynamic imports and
package-transitive ancestry are outside its scope.

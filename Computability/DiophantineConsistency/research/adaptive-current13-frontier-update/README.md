# Current2011 thirteen-variable tradeoff

The factored [13-variable, 87-operation, degree-51 graph](../adaptive-first-root-factor87/README.md)
has a recorded matched historical native-iPRA endpoint for its exact Lean
expression; see the [provenance audit](../../reviews/current2011-adaptive87-ipra-provenance-status/README.md)
for the fixed-snapshot and provider limitations. Its graph and degree binding
are externally checked rather than Lean file-semantics or total-degree proofs.

The [13-variable, 88-operation, degree-30 four-square graph](../adaptive87-four-square-current88-30/README.md)
uses the same current2011 fixed ports. Its same-valuation zero equivalence
to the 87 graph over ordinary integers and its finite degree calculation
have an [independent review](../../reviews/adaptive87-four-square-current88-30-independent/README.md).
This trades one additional operation for degree 30. Its all-model Lean
bridge, internal iPRA endpoint and coherent current-source replay are not
yet checked; it must not be reported as having inherited those proofs merely
from the ordinary-integer argument.

Neither profile is claimed to be globally minimal, and neither result proves
ZFC consistent. The maintained equation and PDF are separate artifacts.

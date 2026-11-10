# Sign25 typed specialization diagnostic draft

The typed-sentence attempt compiled its generic and sentence-definition stages
then encountered an interpreter memory exception while elaborating the typed
standard endpoint. This source-only, fail-stop diagnostic replays the first two
stages, then tests the typed-sentence and bridge imports alone, elaboration of
the standard assertion, and elaboration of the generic theorem applied to the
current expression and bridge. No `sorry` or added axioms are used. Each test
is a separate module, so its failure locates only that invocation and does not
establish the exact cause of earlier resource exceptions. No endpoint follows.

The current-expression provider survey and source/guard limits match the
reviewed typed-sentence packet. Independent review and a slot are required.

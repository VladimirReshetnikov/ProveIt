# Source-current PRA parameter and Herbrand refresh

After upstream generalized `PRAFormulaParameters.qr_rew` and made
`PRAUniversalSyntax` reuse it, two fresh isolated builds rebuilt 17 affected
committed modules, including the universal-presentation equivalence, strict
universal syntax, existential-sequent structure, finite witness selector and
open-matrix selection. All source, object and complete-log hashes match. The
replay verifies the frozen source and inherited local object manifest; it uses
`/tmp/herbrand-universal-preparation-author/lib` only as an inherited object
provider and explicitly rebuilds the affected committed modules. Foundation,
Mathlib and unchanged earlier local objects remain inherited cache boundaries.

The [author packet](pra-parameter-current-author-replay/) preserves the
original exploratory 18-module run, including the uncommitted Preparation
module. The reproducible 17-module manifest excludes that module. The
[independent driver, state and logs](pra-parameter-current-root-replay/) record
the accepted source-current result. This refresh does not establish standard
PRA identification, general witness extraction or conservation.

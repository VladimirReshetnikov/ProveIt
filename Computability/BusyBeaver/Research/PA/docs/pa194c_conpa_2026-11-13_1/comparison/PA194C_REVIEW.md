# Independent review of the PA194C composition

The reviewed dense table has SHA-256
`d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b`.
The native table has SHA-256
`b35d80b01ce9c2e95c8b29222881f40928247cdeffac322e4643f4f6694cd33c`.

The construction was inspected separately from its author. Its six edited rows
are confined to the command controller. The raw table retains 134 fixed
controls and 67 axiom readers; the seven supplied pairwise-disjoint reader
folds give 194 controls. Their local simulation and complete incoming-history
checks are run on the final simultaneously modified table. The builder checks
all 4,749 primitive outcomes for both raw and folded machines. The independent
literal-tape verifier derives its four generic list lemmas from the actual
modified table and resolves the new source by two algorithms.

The strongest source binding is direct: the complete 3,649-instruction ordinal
control graph equals the `rebuilt_195C/source.instructions.json` member of the
current, Git-bound PA195C archive. This equality was checked independently
from the archive bytes, rather than relying on the construction's copied
reference fixture. `pa194c_source_identity.json` records the exact hashes.
The author's explicit 24-site source-tail replacement agrees with that binding.

The primitive-case engine checks finite positive progress when a case closes.
Its contracts cover arbitrary natural registers, both decrement branches, and
arbitrary finite nonempty spare lists. The exact whole-tape blank initialization
reaches the common source seed, so no unexplained physical prefix is omitted.
The reverse finite-trace argument still needs to be stated: a literal halt
cannot occur inside a certified nonhalting primitive block, and positivity
bounds the number of source blocks required to cover a finite physical trace.
This is the ordinary PA-formalizable induction used by the inherited argument.

No structural collision with an existing 194-state construction remains:
`verify_novelty.py` checks all seven recognized current 194-state byte forms,
covering the three positive manuscripts and rejected scanner quotient. It
compares exact action-graph vectors, even after forgetting the initial state
and allowing tape reflection or global symbol exchange. Every comparison fails
to identify the new graph with an old one, as required for material novelty.

The remaining dependency is explicitly logical, not an uncovered physical
experiment: the uniform PA consistency calibration of the inherited PA195C
source. The new proof should cite or include that ordinary source argument,
then apply the positive simulation transport. It should not describe the
integrated conditional iPRA endpoint or existing standard-model Lean theorems
as a newly completed internal PA biconditional. No such new kernel theorem was
checked by this review. No mathematical or machine-binding defect was found in
the reviewed composition.

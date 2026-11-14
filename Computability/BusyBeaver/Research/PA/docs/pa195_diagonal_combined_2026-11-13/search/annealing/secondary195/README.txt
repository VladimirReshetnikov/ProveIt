Optional secondary witness PA195R
================================

This is a 195-state source variant found during the corrected 600-second
safe-variant search, at proposal 6,228,093. It is not a result below 195 and
is not the primary PA195DC deliverable.

Its 191-token emitter exchanges A and H in the two unrestricted positions
of the restricted rho8 axiom, preserving the dominated parameter d <= D.
The full restricted axiom family is unchanged because A and H range
independently. The other six heads, their order, the diagonal Gamma gate,
and the outer controller are exactly the inherited versions.

The new physical implementation has 134 fixed states + 69 AX reader nodes
- 8 compatible history folds = 195 working states. The supplied executable
checker verifies all 32 two-cell fold cases, all 4815 source contracts for
both raw and folded tables, complete free-algebra output equality to the
permuted-rho specification, unchanged arithmetic boxes, exact 58154-step
blank initialization, and complete source CFG agreement between two
resolvers. These checks passed. No independent end-to-end Lean/Rocq endpoint
or novelty claim beyond the recorded search witness is made here.

Use the primary packet's inherited baseline directory:

    python3 verify.py ../../../machine/baseline195

The source grammar, complete native/dense table, label map, fold certificate,
and verification receipt are included. The primary PA195DC construction
uses a different command controller and remains the report's main result.

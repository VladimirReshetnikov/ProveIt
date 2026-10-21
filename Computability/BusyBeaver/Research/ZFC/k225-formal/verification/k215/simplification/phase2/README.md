# Second proof simplification checkpoint

The literal K215 machine and its halting and nonhalting endpoint statements are
unchanged. The [Lean check](lean/README.md) validates the 185-module primary
closure, rebuilding affected modules in a private copy of the pinned earlier
objects. Both typed clients pass: all ten axiom reports use only `propext`,
`Classical.choice`, and `Quot.sound`, with zero audit warnings. This is an
incremental check, not a second full fresh closure replay.

The main simplification is [offset-bisimulation symmetry](source-symmetry/README.md).
One forward certificate now proves both directions of source correspondence.
The data file shrinks from 653,569 to 456,548 bytes, sixteen reverse-check modules
are removed, and the primary import closure shrinks from 201 to 185 modules.
The forward data and every affected forward/site certificate were rechecked.

The [dominated-implication proof](rho8-global/README.md) shares a later schema
before five earlier instances. The selected proof has 629 theorem nodes and
735 compact Rocq instructions, down from 674 and 780. Lean's rendering at this
checkpoint has 128,177 bytes; Rocq's has 22,673 bytes. The Rocq endpoint's seven
affected modules and four closed assumption reports pass, as does a focused
recursive check of the changed dominated-rule module. Earlier full-build
receipts remain the basis for reused objects.

The [register determinism proof](rmdag/README.md) shares four car cases and four
cdr cases instead of repeating their induction arguments. Its theorem and
`propext`-only axiom report are unchanged; the source shrinks from 17,209 to
12,989 bytes. The [enumerator contracts](../enum-contracts/README.md) also reuse
their continuation and AX-pop arguments.

The proof producers and finite search are untrusted. Kernel proof terms and
the saved exact source/dependency/object/log bindings establish these results.
The original machine, external mathematics, attribution, earlier checkpoints,
and failed attempts remain available. No internal PA derivation is claimed.

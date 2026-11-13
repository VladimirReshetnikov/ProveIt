# Supported slots and symbolic copy-position bounds

These exploratory model clients extend the selector-digit argument to all
ordinary positions in the symbolic low-mask support. `support_mask_digit`
and `support_slot` prove the mask shape and digit-at-most-one consequence for
an explicitly supplied standard index in the support, distinct from special
position 1063, when the stated per-slot no-carry and model-position conditions
hold. `fixed_graph_support_bounds` obtains the same graph-derived witnesses
and applies this to every such index.

`CompactCopySupport` checks that each of the 41 `position` entries in the
symbolic kernel lies in that support and differs from 1063. Its graph client
therefore obtains a common `N,w` and, for each of those 41 positions, proves
the corresponding digit at most one whenever `0<k<8807*N` and
`k % 8807 = position i`. It retains graph zero, positivity, the symbolic tuple
and arbitrary `K`. It does not prove that the retained K or masks equal these
definitions, identify a graph column with a weighted finite sum, establish
fractional-rotation alignment, decode the machine or give an iPRA theorem.

Sessions 51068 and 41995 actually exited 0 without warnings; all five named
axiom reports are `[propext, Classical.choice, Quot.sound]`. The second client
used an **exploratory combined overlay**: the direct-K author-side library and
several position-client objects from a separate scratch build, with 143 common
`.olean` hashes compared at one point. Companion files and the full transitive
or dynamic ancestry were not independently verified for this combination. It
is not a paired replay. Two earlier copy-client attempts failed on reduction
depth and an invalid substitution tactic; their failure-derived `sorryAx`
reports are not accepted. See `observation.txt` for commands and actual exits.

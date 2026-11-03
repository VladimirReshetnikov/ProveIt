# Carry-free physical transport columns for a compact word

`CompactMarkedPhysicalColumn.lean` joins the reduced-hypothesis physical
transport residue to the aligned symbolic zero-carry theorem. For
Σ₁-definable row and dummy functions, it assumes a `CompactWord row N s`,
`1 < N`, `s < N`, and `dummy j ≤ 1` for every model index `j`. For every
`j < N` and local phase `q < 8807`, Lean proves that:

* the cyclic carry at global phase `8807*j+q` is zero; and
* radix-`2^67` digit `q` of the actual normalized `blk` cell equals the
  exact raw symbolic-stencil column at global phase `8807*j+q`.

The temporal shift is exactly `67*(8807*s) = 590069*s`. The proof obtains
the actual product, cell-plus-block and origin bounds from the previously
checked marked-word and packed-cell results, and identifies the cyclic
remainder with the physical represented block word using the partial
transport theorem. It assumes neither a complete `PackingInput` nor any
high-mask no-carry condition. It does **not** yet prove that the resulting
raw columns satisfy the high mask, establish a graph zero, bind retained
coefficient bytes, or prove iPRA equivalence.

The first bounded attempt failed on two local rewrites of addition order and
the subdigit base; its source and compiler log are retained in
`observations/attempt01`. The corrected single-author run, tool session
`97839`, exited 0 without warnings or `sorryAx`; its named axiom report
lists only `propext`, `Classical.choice`, and `Quot.sound`. Direct dependency
guards, the full selected project union overlay and selected controller,
symbolic-kernel and static-mask root inventories remained unchanged. The
complete provider-overlap comparisons, selected inventories, command,
source/object hashes, dependency listing, log and terminal receipt are in
`observations/attempt02`.

This is a mixed-provider author-side build, not a paired replay or a fully
authenticated dependency closure. Package, transitive, dynamic-loading and
between-observation ancestry remain inherited.

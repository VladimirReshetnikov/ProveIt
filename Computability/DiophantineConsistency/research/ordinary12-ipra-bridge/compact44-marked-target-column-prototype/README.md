# Exact physical target-column digits

`CompactMarkedTargetColumn.lean` proves that, for every valid cell of a
supplied compact word with Boolean dummy values, the actual normalized block
has digit `1 + 2^51` at both local phases 4393 and 5495. The assumptions
are Σ₁-definability of the row and dummy functions, `CompactWord row N s`,
`1 < N`, `s < N`, globally Boolean dummy values, and `j < N` for the cell.
No high-mask or complete `PackingInput` premise is used.

The proof combines the exact carry-free physical-column theorem with the
selected-band aggregate. The low-mask slot theorem supplies the broad
zero-support fact used by the checked foreign-band geometry: the opposite
band and all bare rotations vanish at each target. The temporal term also
vanishes there because the whole-cell shift preserves local phase and those
phases lie outside the source support. This does not assert high-mask
safety at any other phase, a graph zero, retained-byte binding or an internal
iPRA theorem.

The selected-band module is a byte-for-byte copy of the earlier checked
source rebuilt as an object on the word provider. Bounded single-author
session `14945` exited 0 without warnings or `sorryAx`, with unchanged sampled
direct dependencies; its source, runner, log, dependency list and receipt are
in `observations/band-attempt01`.

The first target-column attempt failed on numeral casts in a selected-band
rewrite; its exact source and compiler output are in `observations/attempt01`.
Corrected single-author session `52717` exited 0 without warnings or
`sorryAx`; its named axiom report lists only `propext`, `Classical.choice`,
and `Quot.sound`. Direct dependency guards, the full selected project union
overlay and selected controller, symbolic-kernel and static-mask root
inventories were unchanged. Provider-overlap comparisons, inventories,
source/object hashes, command, dependency listing, log and receipt are in
`observations/attempt02`.

These are mixed-provider author-side builds, not paired replays or fully
authenticated dependency closures. Package, transitive, dynamic-loading and
between-observation ancestry remain inherited.

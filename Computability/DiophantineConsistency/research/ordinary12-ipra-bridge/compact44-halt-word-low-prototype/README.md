# Low-mask safety of the actual halt-derived word

`CompactHaltWordLow.halt_word_low` takes the model-internal hypothesis
`first (run T)=0`. For every `j` below the chosen halt-derived cell count
`581197^(2T+4)`, it proves that the radix-`2^(67*8807)` digit at `j` of the
actual constructed outer word with zero dummy function is exactly
`packedCell (haltRow T j) 0`. This digit has no binary carry against the
symbolic compact low mask, and the same is true after adding the single
dummy pulse `2^(67*1063)`.

The row exclusion needed by the base no-carry theorem follows from the
constructed `CompactWord.tile_ne`; it is not an extra assumption. This
conclusion covers the ordinary low mask, including cell zero as a raw
no-carry statement. It does not establish the separate origin condition
involving `cell 0 - 1` and `mask + 1`, the actual perturbed outer word,
product/block/high-mask conditions, a complete `PackingInput`, graph zero,
or an iPRA theorem. The symbolic finite-list mask's connection to retained
literal/display bytes remains subject to the separate existing binding
audit.

The first two guarded attempts exited 1 because the client lacked an explicit
definability instance and then used a nonmatching rewrite expression; their
failed source snapshots and observations are retained. Corrected tool
session `36675` exited 0 without warnings or `sorryAx`, and the theorem axiom
report contains only `propext`, `Classical.choice` and `Quot.sound`. The
mixed project-provider overlay had 523 distinct file names and 514 identical
overlap pairs; their hashes and the sampled direct-import/companion guards
were unchanged across the run. The recorded source providers, package,
transitive and dynamic-loading ancestry remain inherited, and the check is
single-author rather than an independent full-closure replay. The `/tmp`
provider paths can disappear.

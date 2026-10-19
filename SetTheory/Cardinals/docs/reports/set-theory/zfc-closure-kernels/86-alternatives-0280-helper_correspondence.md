# Modular correspondence for the optimized prefix helper library

## Result

The20 helper mappings proposed in
`../machine_encoding/permuted_prefix_helpers_right.py` are individually
semantically equivalent to their original Dag254 counterparts on **all
natural register valuations**. The executable finite check passes209 pairs
of decrement/exit control states. This is stronger than reconstructing the
whole old AX word once, and is sufficient for modular ordinary reasoning
about arbitrary new balanced macro words, including the reparameterized one.

This is an ordinary finite graph-bisimulation proof justified below. No new
Lean RegisterPath certificate bridge or binary-table simulation is asserted.

## Independent comparison

`prefix_helper_correspondence.py` reads the pinned219-node Dag254 and the
original203-node prefix source as data. It uses the separately audited
`verify_reassociation.Decoder` implementation of literal path consume/strip/
increment rules, not the helper-mapping producer's whole-word assertion.
For each mapped helper:

1. Check its break/continue escape bounds are exactly(0,0).
2. Wrap the helper as `(helper; HALT)` so the ordinary return becomes an
   observable terminal exit instead of restarting the helper accidentally.
3. Extract the complete primitive instruction CFG, with both successors of
   every decrement guard.
4. Starting at each entry or successor, follow only control-only break/
   continue jumps and increment instructions until the next decrement or
   terminal exit. Reject an epsilon/increment-only cycle. Record the finite
   increment vector, one count for each register.
5. Compare the old and new increment vectors and the next decrement register
   or terminal opcode. At a decrement compare both corresponding successors.
   Memoize matched pairs of next-guard states, giving a finite bisimulation.

All20 comparisons pass. Their old/new leaf counts and209 matched guarded
states are stored in `prefix_helper_correspondence_results.json`.

## Why the comparison proves the needed contract

Break/continue instructions change only the program path, not the registers.
A finite block of increments changes register r by its recorded count; these
increments commute, including repeated increments of one register. Therefore
matched blocks send equal register valuations to equal valuations. The next
instruction is the same decrement/test on the same register, so equal inputs
choose the same branch and produce equal outputs. The selected successors
are again related. A terminal exit matches a terminal exit.

Induction over the number of encountered decrement guards proves equality of
all finite terminating computations and their final registers. An infinite
computation must cross infinitely many guards, because the checker rejects
any infinite control/increment-only block. Bisimulation therefore also
preserves divergence. The helper escape-bound check guarantees that this
sentinel-return comparison is compositional inside any larger sequential
macro word, rather than relying on a special surrounding continuation.

Thus every clean-state Hoare contract proved for the old helper in
`L2Lib254.lean`, `L2Macros254.lean` or `L2Control254.lean` transfers as ordinary
mathematics to its mapped helper. In particular the read-u helper still takes
one candidate field into scratch1, the following move consumes that scratch,
and all formula constructors preserve the required clean scratch invariant.
The exact source-layer interpretation of the changed AX word follows by
composition of these individual contracts and its checked symbolic stack
emission. The formula/schema proof and the physical decoder/startup proof
remain separate layers.

## Mapping

| Original helper | Optimized prefix helper |
|---:|---:|
|166 push a|43|
|121 push b|48|
|168 push c|63|
|171 push zero|39|
|177 push one|91|
|119 implication|57|
|181 membership|79|
|180 universal|58|
|182 equality|58 followed by increment TW|
|218 negation|92|
|178 conjunction|132|
|183 existential|94|
|176 read b|60|
|158 read u into scratch1|18|
|208 move scratch1 into TW|30|
|192 copy c for gate|160|
|131 destructive gate comparison|171|
|211 restore c copy|11|
|197 move a to b|172|
|161 push a then implication|68|

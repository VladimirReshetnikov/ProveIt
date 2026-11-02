# Exploratory graph-derived selector bounds

For fixed symbolic beta, low and high masks, arbitrary natural K, positive
graph coordinates and the literal graph zero, the model-level theorem
`fixed_graph_selector_bounds` obtains a common `N,w` with the existing
radix, repunit and weighted-congruence conclusions. With
`q=1+v 0*p 0` and `C=q-v 1-v 2`, it also proves:

* `dig 67 C 0 = 1`;
* for every **standard natural** `j<943` with `j≠1` and every model `k`
  satisfying `k<8807*N`, `0<k`, and `k%8807=(j:V)`, the digit `dig 67 C k`
  is at most one;
* for every model `k` with the same range and positivity conditions and
  `k%8807=1`, that digit is zero;
* the earlier global high-mask `NoCarry` assertion remains available.

The local `selector_slot` and `excluded_slot` lemmas take the per-position
low-mask `NoCarry` premise explicitly. The proof combines the previous
symbolic mask classes and per-position extraction with the audited generic
digit bounds. The position `k=0` is handled only by the separate origin
conclusion; it is not silently included in the positive-position argument.

Exploratory session 51915 actually exited 0 without warnings; all three exact
axiom reports were `[propext, Classical.choice, Quot.sound]`. The source,
object, command and observations are recorded in `observation.txt`. This is
a single-side scratch-provider compile using the exploratory per-position and
mask-class objects, not a source-frozen pair or independent artifact audit.
The tuple is symbolic; the result does not identify the retained bytes or K,
construct a word or fractional rotation, derive a clean carry or the local
943-row decoder premise, prove machine correctness, or establish an internal
iPRA theorem.

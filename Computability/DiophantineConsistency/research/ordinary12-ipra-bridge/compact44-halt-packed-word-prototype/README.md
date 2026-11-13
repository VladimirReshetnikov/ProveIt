# Model halt to a bounded marked packed word

`CompactHaltPackedWord.halt_packed_word` starts with a model element `T`
satisfying `first (run T) = 0` in an arbitrary model of IΣ₁, plus an
arbitrary Σ₁-definable dummy function. It uses the specific represented row
lookup from the halted machine's tiling word, the stride
`581197^(T+1)`, and the cell count `581197^(2T+4)`. For the actual packed
word constructed from these rows and dummy values, Lean proves:

* the row function is Σ₁-definable and satisfies the marked `CompactWord`
  conditions, including cyclic neighbor matching;
* the packed word is positive and below `2^(67*8807*N)`;
* all its 67-bit digits at positions below `8807*N` are at most one;
* its selector, payload-copy and dummy digits have their specified values
  in each of its `N` cells. Dummy values are taken modulo two.

The halt assumption is **internal to the model**, and neither the statement
nor this incremental check supplies an external halt, a complete low/high
mask and product certificate, a graph zero, or an iPRA derivation. The
result gives the marked constructed word needed by that later construction.

The guarded single-author run, tool session `97528`, exited 0 with no
warnings or `sorryAx`; the theorem's Lean axiom report contains only
`propext`, `Classical.choice` and `Quot.sound`. Its mixed project-provider
overlay contained 523 distinct files; all 514 overlapping file names had
identical hashes in both source providers. The full per-file inventory,
direct-import and companion snapshots, command and compiler output are
retained under `observations/attempt01`, and both the provider inventory and
sampled direct guards were unchanged after the run. The word, halt and
package providers' transitive, dynamic-loading and between-observation
ancestry remains inherited. This is not an independent replay or an
authenticated complete dependency closure; `/tmp` provider paths are
ephemeral.

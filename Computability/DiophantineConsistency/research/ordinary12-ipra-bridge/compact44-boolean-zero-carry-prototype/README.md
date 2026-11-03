# Zero carry for Boolean word families

`CompactBooleanZeroCarry.lean` proves a general model-theoretic strengthening
of an existing heterogeneous cyclic `CarryInput`: if **every** source word
has radix-`2^w` digits at most one and the total coefficient mass plus one
is at most `2^w - 1`, then every cyclic carry is zero and each output digit
equals the unmodified raw column sum. The proof constructs a new carry input
with cap one and carry bound zero; no zero-carry conclusion is assumed.

This is a generic conditional lemma. It does not yet show that every source
word in the compact symbolic stencil, especially the temporal word, is
Boolean; prove the concrete coefficient-mass inequality; identify all raw
columns with the physical normalized blocks; establish high-mask no-carry;
or produce an iPRA theorem.

The bounded single-author compile, tool session `12969`, exited 0 without
warnings or `sorryAx`; its named axiom report lists only `propext`,
`Classical.choice`, and `Quot.sound`. The source and object hashes, command,
dependency listing, log and unchanged sampled direct dependency/companion
guards are in `observations/attempt01`. It inherits the project provider's
package, transitive, dynamic-loading and between-observation ancestry; it is
not a paired replay or a complete independently authenticated closure.

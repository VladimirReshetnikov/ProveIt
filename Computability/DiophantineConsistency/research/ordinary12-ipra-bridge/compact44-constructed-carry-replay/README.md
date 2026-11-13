# Guarded object build for the compact carry client

This is an exact copy of the previously checked
[`CompactConstructedCarryInput.lean`](../compact44-constructed-carry-input-prototype/CompactConstructedCarryInput.lean),
now compiled with an output object so later clients can import it. It
contains the packed-digit and bounded-digit transfer lemmas and the
conditional `symbolic_product_carry` theorem for the exact cyclic product.
Its hypotheses and scope are described in the linked original README.

The bounded single-author run exited 0 without warnings or `sorryAx`, with
unchanged sampled direct dependency and companion guards. Its five named
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The source, runner, dependency scan, log and terminal receipt are retained
here. This does not reproduce all imported project sources, authenticate
package/transitive/dynamic ancestry, identify the temporal product or prove
a graph zero or iPRA endpoint. Provider paths under `/tmp` are ephemeral.

# Independent review: corrected natural-79 recorded ancestry

An independent breadth-first reconstruction checks the 40 natural-80 and 41
corrected natural-79 lexical frontier seeds against the retained P72 and base
producer records. The sole added name, `Compact44.ReducedNormSigned`, was
already reachable from the 40 earlier seeds. Both traversals produce the same
recorded project closure: 627 P72 producers, 919 base producers, 4,414 recorded
edges, and 80 distinct external leaf names. Their module and leaf digests match
the reviewed observation.

The checker separately rechecks the 41 seed source and object file hashes and
resolved paths. The extra seed is P72 row 69; the observed row hash, source and
object hashes, two recorded dependencies and 60 direct guard slots match the
new receipt. It also replays the pinned independent natural-80 review, which
in turn replays the independent root74 source/object/edge and 29,860-slot guard
review. The author's new receipt also reproduces. No mismatches were observed.

This is a comparison of recorded edges, not an authentication of their
historical completeness. Only the final P72 row is anchored by pinned progress
metadata; row 69 and other row hashes are current observations. The reads are
non-atomic, can race with changes and do not reserve files. The checks do not
establish full package, toolchain, implicit or runtime closure, Lean resolution,
compatibility, elaboration, iPRA derivability, or PDF binding. No Lean or
staging was performed.

To reproduce while retained `/tmp` paths remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-corrected-recorded-ancestry-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-corrected-recorded-ancestry-independent/result.json
```

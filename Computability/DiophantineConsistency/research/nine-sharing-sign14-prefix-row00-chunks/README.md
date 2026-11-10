# Row00 short prefix chunks

These 22 short ASCII files concatenate, in manifest order, to the exact
689-byte `row00.prefix` candidate. The first is 19 bytes, ending at the
shared07 subtree boundary; subsequent chunks are at most 32 bytes. The
author's [checker](check.py) verified every length/hash and exact ordered
concatenation; the [independent external audit](../../reviews/nine-sharing-sign14-prefix-row00-chunks-independent/README.md) passed; the packet is frozen. This comparison is an
external check, not a Lean theorem about a live filesystem or the original
JSON. A separate Lean probe may establish a property of the bytes embedded
from an individual chunk at elaboration.

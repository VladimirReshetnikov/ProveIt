# Source and finite review of the MC byte assembly draft

This read-only review covers the **unchecked** corrected
`CompactLowByteAssembly.lean`, its generator, the twelve generated boundary
sources and their generator, the closed byte recipe, and the referenced
symbolic interval and reconstruction sources. It does not compile Lean or
establish that the draft is accepted by the kernel.

The initial assembly source (SHA-256
`6009c59fea3d4c26597d0eee8f4fc3817517e13d0a336f93b41f85bf95d96e25`)
used `2^(8*j)` window lemmas directly against a `256^j` goal in four
branches. The draft author preserved that version and corrected the source
to introduce and apply the `256^j = 2^(8*j)` rewrite. This review pins the
corrected assembly source SHA-256
`cceaf2af001850fa8887f52e80109fc7e9255342f0fb2187c5a5df65ef759f8a`
and its generator SHA-256
`899a1f90c50cf0664ac7b6226d34319bcc9c7f38c9c8000fb56ac6b12c79f1c4`.
The correction is a source inspection, not evidence that the draft compiles.

The independent finite audit finds that the prefix, first dense interval,
three extra dense intervals, six gap intervals, tail and twelve boundary
intervals cover every index in `[0,73759)` exactly once. The boundary
intervals account for 142 positions. It runs the generators in fresh
temporary directories and compares all twelve generated boundary source
bytes and the generated corrected assembly bytes to the reviewed files; it
also checks that each boundary theorem's range and denominator match the
corresponding assembly case. The two separately defined dense-window recipes
are textually equal.

The review independently reconstructs the natural number from the pinned
symbolic support as `2^(67*8807) - 1`, minus one at each support position and
two additional units at the special position 1063. Its 73,759 little-endian
bytes match the decompressed retained `MC.bin.gz` exactly. The separately
parsed byte recipe also matches every raw byte. These are external finite
checks of source and filesystem data; neither is a Lean theorem about the
payload, gzip, PDF, generated source or `lowNat`. The kernel-checked list,
window and reconstruction statements retain their own provider and
provenance qualifications.

[`audit.py`](audit.py) performs these checks without modifying the source
directories; [`capture.py`](capture.py) retains the output, source hashes and
terminal receipt under [`observations`](observations/). The earlier successful
audit without the independent assembly-generator comparison is retained in
[`observations-before-generator-comparison`](observations-before-generator-comparison/).
No additional source-level interval or recipe mismatch was found, but the
remaining Lean compilation and full dependency audit remain necessary.

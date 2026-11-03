# First sixteen symbolic MC byte windows

`CompactLowBytePrefix.prefix_windows` proves in Lean, for every `j < 16`,
that `firstBytes.getD j 0 = (lowNat / 256^j) % 256`, with
`firstBytes = 254 :: List.replicate 15 255`. It applies the checked symbolic
two-digit byte-window theorem and evaluates only these 16 local cases. This
is a finite **prefix** certificate; it is not a proof for the remaining
73,743 byte positions or a complete retained-coefficient binding.

Separately, `python3 -I -B check_prefix.py` decompressed the hash-pinned
retained parent `MC.bin.gz`, confirmed its full raw SHA-256, and compared
its first 16 bytes to the same explicit byte sequence. The actual successful
external output in `observations/payload-attempt01` records the prefix
`feffffffffffffffffffffffffffffff`, the 73,759-byte total, and unchanged
compressed bytes. Checker SHA-256:
`76db124fad3aebf1553fb93e27877c8376cda01199eb6771090dc2b058c277c7`;
output SHA-256:
`09a45cddc782206fa914007ad9fc747ba00ee96db5bdf417fd4d45ba136c958d`.
The correspondence between the external bytes and the Lean literal, gzip
decoding, the supplement's link to the parent, JSON and PDF bytes remain
external provenance, not Lean file theorems.

The bounded mixed-provider author run `observations/attempt02` exited 0
without warnings or `sorryAx`; recorded direct dependency and companion
guards and the generic byte-window provider were unchanged. Source SHA-256:
`0b426b497e70f1a189f2b5a6ff3d1a0a9b88b485b94f8f1d72bae8235992e8ba`;
object SHA-256:
`4ae4828a3988536838aa0d07cb7ea7814c23166fc4913a148585343e4a8ca84b`.
Lean reports `[propext, Classical.choice, Quot.sound]` as metatheory
dependencies, not iPRA axioms. The initial attempt failed because it used
`prefix`, a reserved Lean token, as an identifier; its source and error log
are retained. This is an author-side check, not a paired replay or full
symbolic/package/dynamic ancestry audit; guards are point-in-time.

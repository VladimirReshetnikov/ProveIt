# Independent source review of the compact low-product theorem

The reviewed source is retained byte-for-byte in
[`reviewed-source.lean`](reviewed-source.lean), with SHA-256
`ede777aa5829a92bbd5dbd0ccf91ad08b45468a1b05711ea5dd5129953a398ca`.
It matches the source hash in the original author-side
[`low-product-attempt02` terminal receipt](../../research/ordinary12-ipra-bridge/compact44-kernel-split-prototype/observations/low-product-attempt02/terminal.json).
The source was recovered from the recorded author-run directory after the
workspace source had already been corrected; its hash was verified against
that receipt. This review concerns the **original** checked bytes.

The reviewer checked the claimed mathematical scope: for every model of
IΣ₁ and `x < 2^(67*3297+1)`, the source casts the exact natural kernel
split into the model, bounds the lower-part product below
`2^(67*8793+1)`, and uses the fact that the isolated top term is a multiple
of `2^590069` to identify the exact product remainder modulo that base with
the lower-part product. The smallness condition on `x` is an explicit
theorem hypothesis; the theorem does not itself prove a whole normalized
block bound, a packing condition or a graph zero. No defect was found in
these stated theorem conclusions in the source review.

The original comment before `low_product_lt` says **“at least fourteen
unused radix digits”**. That description is too strong: the proved bound
`2^(67*8793+1)` forces the 13 complete radix-`2^67` slots 8794–8806 to be
zero and leaves 66 additional unused bits in slot 8793. Slot 8793 itself may
be nonzero. This is a documentation issue; the theorem statement contains
the correct exponent. A later source correction and its own build should be
assessed using their separately retained evidence.

At review time the originally reported object in the author directory had
SHA-256 `6809794226cb11d579bee3a3c1d744520ac49f34cbdefab187e6ac1fa65eb41f`,
matching the original receipt. The retained compiler log hash was
`bdb709290bfb123dff4dccae4366e71aaab9e241e16af196a4e41ba89bbf7f04`,
also matching the receipt; the receipt reports exit 0 and unchanged sampled
direct dependencies and selected mixed overlay. This is a point-in-time
source and artifact review, **not** an independent Lean compilation, paired
replay, or authentication of the inherited transitive, package,
dynamic-loading or between-observation ancestry.

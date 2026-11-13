# Expanded compact/iPRA rebuild: stage 266 exact-warning retry

The rejected attempt emitted eleven linter warnings: unused simp arguments,
an unused and unreachable `rfl`, and unnecessary sequencing. It had no error
or `sorryAx`. This retry preserves the source and accepts only the complete,
source-pinned warning log after path normalization; it does not suppress
warnings. Mutation checks reject added, missing and altered warnings, an added
error, and an added `sorryAx`. This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, plus the rejected attempt's dependency guards. It
quarantined the rejected object and rebuilt the unchanged source. Lean exited
0 in 6.889 seconds; the exact warning verifier and final guards passed at
266/425, with source and direct dependencies unchanged. Retry and quarantined
object SHA-256s both equal
`1cae5502955e62c4f5838b1f53e043cc73b2ab8c196b8608fe3181c9b86b5975`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `563030a91b6943ecedad64e3d061b6efaf8fd9439ebe014de345ae5a12c5b2c4`,
`ff7b263bf54dedcc15db623c0869b157d34e33195faec3a8c0b0c9f57259f58b`,
`34b600113b35c63779639db4b80bb78b6027c160417fff80411fb2abb3a15f7c`,
`ee6e2d4004b4197c5b4d2e52388e2673e3b801bedcffc1fa4805eabf684b4b4f`, and
`d9ebd6f7e6f1db823ebf419fea9e0f0ebfb61096d24d8f61e30f3172906252cd`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,493,136 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
159 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.

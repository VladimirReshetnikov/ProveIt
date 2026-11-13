# Expanded compact/iPRA rebuild: stage 316 exact-warning retry

The rejected attempt emitted eight warnings: one deprecated `push_neg`, three
broad simp discrimination-tree keys and four unused simp arguments. This
retry keeps the source unchanged and accepts only the complete, source-pinned
warning log after path normalization; no warning is suppressed. Five mutation
checks reject added, missing and altered warnings, an added error and an added
`sorryAx`. This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 16.312
seconds; the exact warning verifier and final guards passed at 316/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`46cf01d55ba0724905e6b3eeb075a4ee72f34679920617fc48afbdb112a3e880`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `14c41ee24aa6be978eac4b22e342bc4d4946fb7cddc38a8e81e529dcbd1634e2`,
`2fc433ab16cdab754d8386c6175396d1a8e2b17466d373513b03cbcb3359621f`,
`8564b0ee9aec933716b0c7ee784d2c23c7ae8762a74c41f41ecb4dcaa8f5e42e`,
`e390dd8d324c6b2f15dc59d62df4f28b6c2671228c068f512dace7eb336e63c4`, and
`df561cfe13086dc1f6281f5818c2c64a159e12b17e34eea58097b22296138f27`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,462,564 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
109 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.

# Expanded compact/iPRA rebuild: stage 419 source correction

The earlier stage 419 failed because the selected pre-existing
`InternalInterpretation` object lacks the newer source helper
`consistent_of_falsum_transfer`. The workspace correction inlines that short
proof in `QSchema.consistent_ZF_of_native`, preserving its statement and
avoiding replacement of the shared provider object. The failed source, receipt
and error log remain in the stopped packet.

`repin.py` verifies the exact failed source, log and receipt, the previous cone,
the new workspace source and the single intended replacement. The old and new
source SHA-256s are
`80c040905d9d0565f17f6cce8d8036549096088fc2a3559d9c7f6f752b8caa0a` and
`0a8ffaa78ef63fe51f4b9c35ddea5ee28908204a4e4a06376b43c285c88ca0c1`.
The new cone SHA-256 is
`b5eb6a00e30599c49a851b38746582c75f1eaba2e6c9a66ed6a8adec9f4dc424`;
all earlier baselines are checked with only intended source corrections
accounted for, and the new baseline is stored separately.

Lean compiled the corrected stage without warnings in 4.294 seconds, exit 0;
its object SHA-256 is
`7ab7b6088e1342086f8b8b105b5e5f886d7e927917d008481c52208f362e39e8`.
Source and direct dependency guards were unchanged, all earlier receipts,
source pins, warning baselines and selected overlay were rechecked, and the
wrapper reported 419/425. Runner SHA-256 is
`bc9c4d84e4a6b49e55c28cd972edd033c03a16e73d139991102518ec529b0069`.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,552,756 KiB; short children or overlaps can be missed. This fixes
one encountered missing reference, not historical source origin for selected
objects. This author prefix is not an iPRA endpoint, independent replay, or
full provider audit; package and dynamic ancestry remain open.

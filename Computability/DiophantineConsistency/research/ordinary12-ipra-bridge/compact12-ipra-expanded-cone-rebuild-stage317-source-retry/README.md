# Expanded compact/iPRA rebuild: stage 317 source correction

The earlier stage 317 failed because the selected pre-existing
`InternalInterpretation` object lacks the newer source helper
`consistent_of_falsum_transfer`. The workspace correction inlines that short
proof in both `LSchema` consistency-transfer theorems, preserving their
statements and avoiding replacement of the shared provider object. The failed
source, receipt and error log remain in the stopped packet.

`repin.py` verifies the exact failed source, log and receipt, the previous cone,
the new workspace source and the two intended replacements. The old and new
source SHA-256s are
`f7edf5e44ae544506a97859e7ab8937f9d69ff6b89cc821350dfb1b6f1be09f5` and
`c68dbfb6e9b152ab71654de3a2b2cf3559ebe1f8e616edabd12e24209ea568f2`.
The new cone SHA-256 is
`eb5a8a3c8efb7b1d936d4c77ba2c6d201aff6d03f23c9e1697dd2b518aefcbf2`;
both earlier baselines are checked with only the intended source corrections
accounted for, and the new baseline is stored separately.

Lean compiled the corrected stage without warnings in 3.112 seconds, exit 0;
its object SHA-256 is
`02b9e5a2bc149a36dc02f2ec4041052a55691ab27b745616809b132619319f88`.
Source and direct dependency guards were unchanged, all earlier receipts,
source pins, warning baselines and selected overlay were rechecked, and the
wrapper reported 317/425. Runner SHA-256 is
`a2390feba5e6b02c062aa9b7da6335373611056dc39aa22a5696c8513d3aeced`.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,521,068 KiB; short children or overlaps can be missed. This fixes
two encountered missing references, not historical source origin for selected
objects. `QSchema` also references the newer helper and may require work. This
author prefix is not an iPRA endpoint, independent replay, or full provider
audit; package and dynamic ancestry remain open.

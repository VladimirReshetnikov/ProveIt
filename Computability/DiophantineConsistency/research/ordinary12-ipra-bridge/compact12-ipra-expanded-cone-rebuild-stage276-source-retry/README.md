# Expanded compact/iPRA rebuild: stage 276 source correction

The earlier stage 276 failed because the selected pre-existing
`InternalInterpretation` object lacks the newer source declaration
`consistent_of_falsum_transfer`. The workspace correction inlines that
short proof in `NativeSchema.consistent_ZF_of_native`, preserving its theorem
statement and avoiding replacement of the shared provider object. It derives
the target consistency statement directly from the already checked refutation
transfer. The original source and failed log remain in the stopped packet.

`repin.py` verifies the exact failed source, log and receipt, the old cone,
the new workspace source, and the single intended text replacement. The
old and new source SHA-256s are
`266f7f619e3f01fc0a64c38036b14a5854c7264fef0cceb999a437fefab99982` and
`d6042135723adce366def247894e63cd3ad5d05d1dc57256718e6c82100f3210`.
The new cone SHA-256 is
`aa2ec030a843382be4dc6fe621174d80d46bf9799d9b52d1616dac52661a9699`;
the independently retained old baseline is checked with only this source
correction accounted for, and the new baseline is stored separately.

Lean compiled the corrected stage without warnings in 4.027 seconds, exit 0;
its object SHA-256 is
`010d53037c1500000228e4d7619cbc877622048c08a9c88663321e9918f657ed`.
Source and direct dependency guards were unchanged, all earlier receipts,
source pins, warning baselines and selected overlay were rechecked, and the
wrapper reported 276/425. Runner SHA-256 is
`1f6f2b0daf803bcde884325e0f0e98696b51f54edac0aaf03b9bc9fa558324b6`.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,501,012 KiB; short children or overlaps can be missed. This fixes
one encountered missing declaration; it does not establish historical source
origin for selected objects. `LSchema` and `QSchema` also reference the newer
helper and may require further work. This author prefix is not an iPRA
endpoint, independent replay, or full provider audit; package and dynamic
ancestry remain open.

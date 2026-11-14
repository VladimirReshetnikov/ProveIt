# Marking against the imported runtime tape layouts

`PA194MarkRuntimeStandard.runtimeMarkPositive` combines the checked
non-first-position marker execution with the imported `M6.Runtime` list
encodings. For every ordinary natural-valued, nonempty prefix of at most eight
registers and any selected register, remaining file, left tape and finite
suffix, it runs the explicit PA194 primitive-recursive clock from the numeric
encoding of `M6.Runtime.sepsR` and ends at native control 3 (dense 17) with the
numeric encoding of `M6.Runtime.sepsM` at that same position. Its exact
half/parity tape convention and clock appear in the theorem. `runtimeMarkFirst` similarly binds the three-step first-position run, reaching
native control 1 (dense 15). Together these cover all nine physical positions.

The dense-to-native control names in this note follow the packet’s label
metadata. The Lean execution theorems use dense controls; they do not prove a
full-table native/dense conjugacy.

This theorem is a standard-natural-number specialization, not a claim that
ordinary Lean truth alone establishes PA provability. The corresponding
all-model result and its explicit native-iPRA sentence are documented in
`MARK-ALL.md`; the input and output layout bindings use the standard source
semantics.

Run `check-mark-runtime.sh` with the pinned overlay environment documented in
`MARK-ALL.md`. It rebuilds dependencies and checks theorem axiom reports. Set
`TMPDIR=/dev/shm` if root-disk space is limited.

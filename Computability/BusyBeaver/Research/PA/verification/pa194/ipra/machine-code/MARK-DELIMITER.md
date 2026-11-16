# First-register marking delimiter

`PA194MarkDelimiter.modelMarkDelimiter` proves the exact three-step delimiter
part of the PA194 register-marking routine for all models of classical PRA,
including nonstandard tape halves. The control labels are for the pinned dense
PA194 table. Starting in dense state 113 (native 51) on a tape beginning `01`
with arbitrary tail, it changes that `1` to `0`, moves left across the first
delimiter, and reaches dense state 15 (native 1). The theorem gives the exact
binary half/parity relationship for both tape halves. The three literal row
calculations are in `PA194MarkRows.lean`.

`PA194MarkDelimiterSentence.nativeIPRA` is the corresponding universally
closed equality proved in native intuitionistic PRA. It uses explicit
primitive-recursive codes and the existing classical equality-to-iPRA
translation. The finite state labels and the count of three steps are
standard syntactic constants; the tape values can be nonstandard.

This delimiter theorem covers the first physical register only. It does not
select later registers, establish the transition from the marker's exit to the
increment engine, interpret the source dispatch, or prove either direction of
a consistency reduction.

Run `check-mark-delimiter.sh` with the pinned iPRA and Foundation overlays
used by `check-native-scans.sh`. The checker rebuilds the dependencies and
rejects any `sorryAx` in printed theorem dependencies. Set `TMPDIR=/dev/shm`
if temporary disk space is limited.

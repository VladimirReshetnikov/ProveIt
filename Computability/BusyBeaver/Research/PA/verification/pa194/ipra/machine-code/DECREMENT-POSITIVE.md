# Positive-register decrement

`PA194DecrementPositive.modelPositiveDecrement` proves the complete physical
positive-decrement arithmetic box of the pinned PA194 table in every model of
classical PRA. It begins at dense control 1 with an arbitrary fixed finite
prefix followed by a marked register of value `v+1` and an arbitrary fixed
suffix. It traverses the prefix, performs the four-step selected-delimiter
update, and returns across the prefix to dense control 7. The returned numeric
file has the selected value `v`, with the prefix and suffix preserved. The
encoded clock and output are explicit primitive-recursive functions; each
register value and tape suffix may be nonstandard in the candidate model.

`PA194DecrementPositiveSentence.nativeIPRA` is the corresponding universally
closed equation in native intuitionistic PRA for each fixed prefix/suffix
arity. Its terms build the marked positive input boundary directly. It is
derived from the machine-specific all-model theorem via the existing equality
transfer.

The theorem assumes entry into the positive-decrement box with the register
already marked. It does not establish the zero-register case, the full source
instruction, or either PA consistency implication.

Run `check-decrement-positive.sh` with the pinned overlay environment described
in `MARK-ALL.md`. It rebuilds dependencies and checks theorem axiom reports.
Set `TMPDIR=/dev/shm` if root-disk space is limited.

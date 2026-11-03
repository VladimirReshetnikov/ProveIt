# Boolean digits in an aligned temporal rotation

`CompactAlignedTemporalBoolean.aligned_digit` proves that rotating by
`67*e` bits selects the corresponding base-`2^67` digit via the existing
cyclic index, for positive model length and a source word below the period.
The proof uses the model multiplication/modulo cancellation theorem and the
existing aligned-window rotation identity.

`word_temporal_boolean` applies that identity to the represented compact
word: for any definable row and dummy functions, positive `N`, arbitrary
model `e`, and `k < 8807*N`, the temporal rotation by `67*e` has radix digit
at most one. This supplies the temporal Boolean premise needed by the
zero-carry argument for aligned exponents. It does not assert that a
particular controller exponent is aligned, prove high-mask safety or the
physical block-to-cyclic-remainder bridge, construct graph zero, or prove an
iPRA endpoint.

The guarded single-author run exited 0 without warnings or `sorryAx`; its
two named axiom reports list only `propext`, `Classical.choice`, and
`Quot.sound`. Direct dependency and companion records were unchanged. The
source, command, dependency scan, log and receipt are retained under
`observations/attempt01`. Package, transitive, dynamic and
between-observation provider ancestry remains inherited; `/tmp` paths may
be ephemeral.

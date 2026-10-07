# Bounded OEIS fixture

`oeis_fixtures.json` contains exactly 64 nonnegative integer terms of A078510,
indices 0..63, from the supplied official revision 21 (11 September 2025),
reviewed 4 October 2026. Neil Fernandez is credited for the sequence;
Antti Karttunen is credited for the predecessor recurrence.

Source: https://oeis.org/A078510

The fixture is a short test input, not a redistributed database record.
Its metadata, structure, integer types, complete byte checksum, and all 64
computed values are checked. Both the closed recurrence and the separately
step-generated geometric construction reproduce it. `DATA_SOURCES.md` gives
source provenance and limitations. No numerical amplitude fixture is used.

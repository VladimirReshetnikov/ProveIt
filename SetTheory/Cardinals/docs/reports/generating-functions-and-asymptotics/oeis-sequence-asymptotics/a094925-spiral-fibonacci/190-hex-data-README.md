# Bounded attributed fixtures

The sole data file, oeis_fixtures.json, contains 41 listed A094926 integers,
38 listed A094925 integers, 106 A258639 fractional digits, and 77 fractional
digits of the A094925 original-index amplitude. It includes only those bounded
fixtures, their OEIS repository URLs, offsets, retrieval date, and schema.
It is not a complete OEIS record, b-file, downloaded program, or research log.

The underlying records were read on 4 October 2026. A094925 and A094926 credit
Yasutoshi Kohmoto as their author. The 2015 asymptotic conjectures are attributed
to Manfred Scheucher; A258639 credits Manfred Scheucher and Vaclav Kotesovec.
The numerical values are prior source data, not a new-digit claim.
See ../DATA_SOURCES.md for record versions and source/overlap limitations.

The shared-coordinate recurrence uses a0=0,a1=1 for A094926(n), and a0=a1=1
for A094925(n+1). The latter source begins at index 1. Its source amplitude
is C1/phi, not the zero-based amplitude C1. A258639 gives digits after the
decimal point for C0; its zero integer part is not stored as an extra digit.

The mandatory verifier pins SHA-256
f00dac9c0a61db7a1f77f1ca20db09c495bd1992d003d223c2ab6f3ce4b3b454
and validates the schema, term/digit counts, types, offsets, and exact source
URLs. Well-typed term and digit corruption tests must fail. No mutable remote
record is fetched at runtime. Hashes detect edits relative to the authored
source; they are not signatures against replacement of both code and fixture.

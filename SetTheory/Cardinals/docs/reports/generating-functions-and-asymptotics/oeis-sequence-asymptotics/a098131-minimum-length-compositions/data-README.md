# Small attributed fixtures

The sole data file, oeis_fixtures.json, contains 24 terms for each of
A098131 (offset 0), A098132 (offset 1), and A098133 (offset 1), for a total
of 72 integer values. It does not contain full OEIS records or b-files.
Each record retains its source URL and credit. DATA_SOURCES.md gives
attribution, terms, and the report's empty-composition normalization.

The mandatory exact checker validates the closed fixture schema,
identifiers, offsets, term counts, integer types, URLs, and attribution,
then compares every value to the binomial implementation. Independently
multiplied GF tests and exhaustive small-composition tests check that
implementation separately. Fixture text is never executed. Fixture data
is fixed; reproduction makes no network requests and does not rewrite it.

# Historical timing records

The initial benchmark and initial sieve-follow-up records are retained rather than
discarding exploratory measurements. They were made before later strict input
preflights, graph-checker union-by-size, and the gcd-minor extension. Their exact
source-hash maps are inside each JSON file. The final delivered code may therefore
not match those historical hashes. Exact old source snapshots are not distributed;
these records are provenance, not a reproducible native-baseline comparison.

All article tables and current claims use the separate final files
`../benchmark.json` and `../sieve_followup.json`, rerun against the delivered core
code. Those files record matching before/after core source hashes. No historical
time is silently merged into the final samples. The initial aliasing observations
motivated testing cycle lengths on both sides of multiples of 32; the final
follow-up retains the failing multiples instead of selecting only successes.

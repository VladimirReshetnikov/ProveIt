# Bounded inputs

- oeis_fixtures.json: attributed official A096537 prefix, 15 terms n=0..14;
  attributed official A096542 example, nine rows n=0..8 (45 coefficients)
- generated_coefficients_48.json: author-generated integer regression vector,
  49 values n=0..48; this is not an official b-file

The A096537 page advertises a b-file for n=0..200, but it was not retrieved or
used. The mandatory result states official_A096537_bfile_used=false. Values
at n=15..48 must not be called verified official terms.

Each file has a distinct exact schema and pinned SHA-256 digest. Wrong types,
Boolean integers, wrong counts, modified provenance, duplicate JSON keys,
non-finite JSON numbers, and changed bytes fail closed. Checks are explicit
exceptions, so Python -O does not disable them. Replay never regenerates or
silently replaces either input fixture. Source URLs and credits are recorded
in the JSON and in DATA_SOURCES.md.

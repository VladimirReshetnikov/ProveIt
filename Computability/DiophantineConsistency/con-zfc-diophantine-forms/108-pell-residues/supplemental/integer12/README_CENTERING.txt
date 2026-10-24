CENTERED TWELVE-INTEGER POLYNOMIALS

The new equation files are:
  equations/centered12_integral2400.json    degree 2400, 210 live operations
  equations/centered12_rational2368.json   degree 2368, 216 live operations
Both use twelve unrestricted integer variables and the exact six coefficients
under inherited/root_fusion/coefficients/. Every other file from the parent
integer12 subtree is retained byte-for-byte. PARENT_LICENSE and
PARENT_NOTICE.md preserve the incoming archive's outer attribution.

Read proofs/CENTERING_PROOF.txt for the complete new mathematical argument.
These are exact polynomial changes of the parent n coordinate; no new
semantic calibration premise is introduced. The parent README and proofs
describe the inherited constructions and proof status, not the new metrics.

From this directory, Python 3 with its standard library is sufficient:
  python3 check_centered12.py
The checker reads the delivered graphs, rebuilds them, reads and authenticates
all six actual coefficient payloads, proves each exact coordinate translation
against the unchanged parent graph, checks the central cancellation identities,
and checks the weighted degree and nonzero leading-monomial certificates.

To rebuild the delivered graphs:
  python3 build_centered12.py --variant rational --output equations/centered12_rational2368.json
  python3 build_centered12.py --variant integral --output equations/centered12_integral2400.json

The full parent subtree came from
ConZFC_Valuation_and_Signed_Certificates_2026-10-23.zip.
provenance/CENTERING_PARENT_ARCHIVE.json records that archive's SHA256 and
the exact bytes of every extracted parent file.

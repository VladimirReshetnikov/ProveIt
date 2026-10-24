# Signed-power bootstrap and alternative certificate interfaces

Start with report.pdf and its editable report.tex. This package contains explicit ordinary polynomial candidates, mathematical proofs, and finite reproducibility checks. It does not claim global minimality, a consistency decision, or a new end-to-end Lean/Rocq/object-language ZFC certificate.

## Main completed candidates

- guards/signed34_sextic.json: one sum-of-squares polynomial in34 unrestricted integers, exact degree6,19 residuals. Its new signed-power bootstrap and transport absorption remove a genuine scale coordinate before monic projection.
- low_degree/p13_degree30.json:13 strictly-positive unknowns,degree30,94 live arithmetic operations.
- low_degree/p12_product_split2.json:12 strictly-positive unknowns,degree114,105 operations.

The latter two trade smaller degree for one additional operation relative to selected incoming counterparts. The existing41-integer quartic and30-integer octic remain unbeaten here. Mixed_source projections are examples, not records: prior25-positive sextic and20-positive octic dominate the new26/21-variable versions.

The certificates and direct folders investigate genuinely different proof-certificate interfaces. They are NOT completed smaller Diophantine consistency endpoints. Their universal mathematical lemmas, diagnostic examples and outstanding compilation obligations are distinguished explicitly.

## Offline replay

Requirements: Python3.10+ and SymPy (used for exact symbolic polynomial identities). No package installation or network access is performed by the replay.

Run:

    python verify.py
    python verify.py --replay-originals
    python negative_controls.py

The default replay authenticates the release, creates a temporary copy, authenticates/extracts all eight original incoming ZIPs, runs new builders/checkers and independent audits, and compares selected regenerated files byte-for-byte. The optional flag additionally executes all eight original root verifiers in further clean temporary copies. Original archives and the extracted release remain unchanged. Three corruption controls demonstrate fail-closed integrity checks, not a semantic proof.

The original ZIPs are retained under incoming/ to make provenance and inherited coefficient data independently inspectable. Their SHA256, Git-blob hashes and arrival/placement revisions are in INCOMING_PINS.json. They are not silently treated as trusted executable downloads: source execution surfaces were inspected and the replay is offline. Extracted sources are deliberately omitted from this outer archive and created only inside replay temporary directories.

See DEPENDENCIES.md and component proofs for exact theorem boundaries. Counts of binary arithmetic operations charge fixed-scalar multiplication and squares, with fixed numeral leaves free; they are not bit complexity. Natural, positive and unrestricted domains are never interchangeable without an explicit reduction.

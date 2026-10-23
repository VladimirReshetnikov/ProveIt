# Positional certificates for the affine-gap sources

Three frozen candidate layouts:
- gapN116_H2068_code.json / _kernels.json: 86 records, W116, H2068.
- gapNq116_H2082_code.json / _kernels.json: 85 records, W116, H2082.
- gapNmirror116_H2057_code.json / _kernels.json: 86 records, W116, H2057.

The reflected candidate has all three kernel leading coefficients positive.
The leading source coefficient is beta+2, because its quadratic and linear
layers tie. Full local proof: PROOF.md; report section: section.tex.

Required sibling sources: ../source/gapN86_source.json and
gapNq85_source.json with their mathematical coordinate-change proof.

Reproducible read-only checks:

    python verify_certificates.py
    python rebuild_kernels.py
    python test_certificates.py

The main checker reconstructs exact polynomials over 35 formal variables.
Normal and -O checks are byte-identical. The tamper tests update the kernel's
code hash coherently before checking structural corruption; they do not
merely exploit stale hashes. Six mutations are rejected in both modes.

Package these six candidate JSON files, CERTIFICATES.json, VERIFICATION.json,
REBUILD.json, TEST_RESULTS.json, the three check scripts, README.md, PROOF.md
and section.tex. Search scripts, inputs, logs and binaries are discovery-only
and need not be distributed. They establish no optimality claim. In particular,
valid narrower106-label experiments had worse target heights and are discarded.

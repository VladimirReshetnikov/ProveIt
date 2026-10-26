# Validation of this release

The complete replay is `python3 -B verify.py`; repeat with `-O` to check
that verification does not depend on Python assertions. Both modes passed.
The JSON receipts in `verification/RELEASE_NORMAL.json` and
`verification/RELEASE_OPTIMIZED.json` record the twelve replay stages and
their output identities. All reconstruction that writes files runs in a
disposable copy of the package.

The replay covers twelve direct projection profiles, three raw pooled
systems, all seventeen power requests in the parent frame, and three compact
positive-domain equations. The projection checker rejects sixty deliberate
corruptions. Across the twelve direct equations it authenticates 1,356 unit
pivots and gives 1,247 nonzero modular partial-derivative witnesses, proving
that every declared input occurs in its actual polynomial. The 87-variable
endpoint has separate normal and optimized receipts, which agree exactly.

The article checker independently parses all 162 printed parent residuals
and all twelve complete pivot lists. The article exporter checks all four
generated inputs against their frozen definitions. A separately assigned
review additionally parsed every entry in the printed seventeen-request
table and reconstructed the actual parent multiplication, Pell-norm,
singleton and pooled-power rows; its results are recorded in
`proofs/PROJECTION_REVIEW.md`.

The compact checker verifies its arithmetic circuits and exact leading
forms without importing the circuit producer. The fixed coefficient bytes
are reconstructed from the finite seed and recipe, including their original
raw and compressed hashes. These checks remain active with optimization.

The main report was compiled twice with pdfLaTeX and every page rendered
for visual inspection. The final compilation has no undefined references,
overfull boxes or LaTeX warnings. The 29-page PDF and every TeX input needed
to rebuild it are supplied.

`MANIFEST.sha256` authenticates the release files. The top-level verifier
checks this manifest when present. Receipt files created during the initial
mathematical replay record that the release manifest was not yet present;
this is intentional, since the manifest is generated after the report and
receipts are complete. A final replay of the extracted archive checks the
finished manifest as well as the same mathematical artifacts.

These are finite algebraic and reproducibility checks. The unbounded
oriented-pooling proof, positive-domain lift, and inherited C222/ZF/ZFC
calibration have their separately stated mathematical scopes. This release
does not claim a new end-to-end proof-assistant compilation or a proof of
consistency itself.

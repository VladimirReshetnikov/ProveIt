Minimum-norm finalizers: 15 positive unknowns, exact degree 44
===========================================================

gap_minima75.json: 75 live binary operations (40 multiplications).
gap_minima76.json: 76 live binary operations (40 multiplications).
Historical ordinary_gap_sos78.json: 78 operations, same degree.

Run: python3 verify.py
The verifier uses only Python's standard library and prints exactly one
JSON object with status PASS. It also writes verification_receipt.json.

MINIMA_PROOF.txt gives all formulas, a complete integer minimum proof,
exact zero-set scope, inherited dependencies, and degree certificates.
minima_supplement.tex is a compact optional report-appendix fragment.

Both new JSON circuits point to fixed_coefficients.json, which binds
all four native coefficients to local gzip payloads. This is the
complete package-31 tuple, not four free parameters. See SOURCE_PINS.json
for immutable full commits, repository paths, Git blob identities, and
SHA-256 digests of every inherited file. Source files' old binding text
is preserved as historical metadata and is superseded in both new
circuits by their explicit local binding.

To regenerate both new circuit descriptions:
    python3 build_minima.py

For modular evaluation:
    python3 evaluate.py 75 1000003 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
The last 15 inputs are J F alpha z f h i T s w tau eta zeta e gamma.
For 75 the transport input is original z. For 76 it is z_old-1.

The finite certificates prove binding, count, liveness, and exact degree.
The unbounded minimum proof is ordinary mathematics; the compiler and
ZFC refutability interpretation are inherited ordinary mathematical
dependencies. No new end-to-end kernel certificate is supplied here.

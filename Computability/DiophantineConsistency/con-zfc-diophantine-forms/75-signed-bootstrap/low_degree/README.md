# Adaptive transport-carrier composition

- `p13_degree30.json`: thirteen positive variables, degree30,94 live gates.
- `p12_product_split2.json`: twelve positive variables, degree114,105 gates.
- `p12_sos_split2.json`: twelve positive variables, degree172,104 gates; companion, not a new degree record.

Rebuild and audit with Python3 and no third-party packages:

    python build13.py
    python build12.py
    python check13.py
    python check12.py

Both checkers also pass with `python -O`. PROOF.md is the full ordered
mathematical argument with named dependencies. section.tex is a report section.
FAILED_ROOT_MERGER.md records the investigated but invalid eleven-variable
shortcut. Do not present it as an endpoint. The source coefficient tuple is
inherited, not regenerated here; SOURCE_PINS.json pins the exact proof inputs.

This component combines two previously separate mechanisms. It does not claim
a qualitative breakthrough, global minimality, or a new Lean/Rocq certificate.

Exact coefficient dependency: COEFFICIENT_BINDING.json identifies all four payload members, their original archive and hashes, and the unsigned little-endian gzip encoding. From the package root, extract them with:

    unzip incoming/con-zfc-congruence-carriers.zip "con-zfc-congruence-carriers/coefficients/compact44/*" -d extracted_coefficients

Decode each gzip payload with gzip, then interpret its bytes as an unsigned little-endian integer. K0 is the stored K port. MF is the already shifted MF_source port and must not be shifted again. Never mix coefficient ports from separate instances.

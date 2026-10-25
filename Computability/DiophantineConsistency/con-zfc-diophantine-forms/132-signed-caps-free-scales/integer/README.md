# Eleven-variable main-radicand saturation

New nondominated exact degree/live-operation pairs:

- 352/132, free scale and sharp center (primary).
- 364/131, free scale and simple center.
- 376/127, free scale and no center.
- 428/123, weak scale and no center.

All use eleven unrestricted integers and the same six authenticated source34 numeral payloads. The new degree352 endpoint is a 15.38% degree reduction from the incoming416 endpoint, at seven additional arithmetic gates. Two dominated comparison equations396/128 and412/127 are retained and audited, not counted as frontier results.

PROOF.md gives the complete ordinary arithmetic proof, including c=0, parity before scale recovery, three-way coprimality, new square-root saturation, strong/auxiliary coordinate restoration, the strengthened fifth-power projection bound, and fixed-strong-pair supported interpolation. section.tex is report-ready.

Reproduce offline with Python3 standard library only:

    python build.py
    python check.py
    python -O check.py

No downloaded source is fetched during replay. The six actual numeral payloads and their finite reconstruction recipe are in coefficients/. All named unbounded proof dependencies and licenses are retained locally and authenticated by SOURCE_PINS.json. The finite checker does not import the builder, contains no removable assertions, checks every live register and all exact cancellation identities, authenticates/reconstructs the complete constants, certifies attained degree at the actual constants, and rejects mutations.

No proof of consistency, ten-variable endpoint, global optimum, new end-to-end proof-assistant certificate, or encoded object-ZFC derivation is claimed. The ZFC-provable equivalence with syntactic consistency is the ordinary arithmetic reduction composed with the explicit inherited native/compiler/refutation calibration.

# Complete mixed121 Wang943 coefficient tuple

The direct compiler ports are `beta`, `K0`, `MC`, and `MF`. The fixed values
are defined in report section 3 and COEFFICIENT_BINDING.json, with
`B=2^1064921`, native digit base `rho=2^121`, and cell length 8801.
Read beta.bin, K.bin, MC.bin, and MF_source.bin respectively as minimal
unsigned little-endian integers. All four must be used together.

`MF_source=MF_native+B-1` is the already shifted high mask. The similarly
named native mask is not the fourth arithmetic input. The raw files total
533,099 bytes; gzip files are transport encodings of those same integers.

Run `python3 build_coefficients.py` to rebuild the tuple and finite checks.
This uses only the standard library and never runs the encoded machine.
The separate script `../reviews/audit_coefficients_independent.py` rebuilds
the tuple from a distinct implementation without importing this generator.
Both scripts resolve paths relative to their own location.

The construction keeps the pinned K215 transition table and ordered
Wang943 tile list. It combines package 25's mixed-radix decoder and compact
layout with package 24's general odd-dimension Boolean padding argument.
The mathematical proof includes the controller for
`1064921=11^2*13*677`, padding prime 2341, step 2340, and the canonical parity
properties required by the signed interfaces. Finite checks supply the
literal layout and modular facts; the proof supplies unbounded soundness
and completeness.

Original source identities appear in `../sources/SOURCE_MAP.json`.
`upstream/wang943_tiles.json` is the authenticated frozen comparison list.

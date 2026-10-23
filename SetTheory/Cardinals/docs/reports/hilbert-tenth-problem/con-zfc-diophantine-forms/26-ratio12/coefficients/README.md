# Wang943 parity tuple: smaller fixed coefficients

This directory supplies a new complete four-coefficient tuple for the
inputless native compiler. It retains the exact inherited 943-tile Wang
language while placing copy digits on even exponents. Spatial tests then use
odd exponents, permitting the unit radix shift `DR=rho=2^625`.

The largest actual coefficient has **9,766,251 bits**, down from 13,201,251
bits in the prior compact Wang943 backend. The base remains `B=2^(5^10)`.
The four actual compressed payloads total 19,820 bytes and decompress to
4,882,894 bytes. These compressed sizes do not measure coefficient height.

## Binding

The root `COEFFICIENT_BINDING.json` is the entry point used by the arithmetic
JSON files. Every path in that wrapper is relative to this `coefficients/`
directory. It identifies the same complete tuple as the internal canonical
binding below. Its `source_bindings` point directly to the four delivered
gzip files under `compiler/coefficients_parity/`; its file records distinguish
compressed file hashes/bytes from the uncompressed integer hashes/bytes.
The canonical binding's paths are relative to its own `compiler/` directory.

Use every port from `compiler/COEFFICIENT_BINDING.json` together. The four
literal unsigned little-endian integers are supplied as
`compiler/coefficients_parity/{beta,K,MC,MF_source}.bin.gz`. The arithmetic
port named `MF` is the shifted `MF_source`; the native high mask is
`MF_source-beta`.

Both the twelve-positive-variable construction and the twenty-four-integer
construction in the main report use this whole tuple. Their root reductions
are independent of the layout change; compatibility, including odd-scale
completeness, is proved in `PARITY_COEFFICIENT_PROOF.md`.

## Offline reproduction

Run `python3 reproduce_coefficients.py` with Python 3.10 or later. No
nonstandard packages or network access are required. This regenerates raw
and compressed coefficients, the tile order and scalar layout, and invokes
the independent semantic and byte/geometry auditors. The frozen raw hashes
are checked at the end. The `load_ports()` function loads the four actual
integers directly from delivered compressed bytes.

Two separate implementations reconstruct the complete new tuple without
importing its builder. The further mathematical review is recorded in
`audit/INDEPENDENT_PARITY_COEFFICIENT_REVIEW.md`.

The raw `.bin` files and Python cache folders may be omitted from the archive;
the four gzip files contain the complete literal coefficients. A replay
generates the raw files before the independent byte comparison.

## Mathematical proof and attribution

`PARITY_COEFFICIENT_PROOF.md` gives the complete new tuple formula and adapter
proof, including arbitrary bit rotations and the upper-dummy spill case,
all target identities, clause separation, unique anchor alignment, carry
and positive-slack bounds, origin masks, and actual-rank adjustment.
`compiler/WANG943_COEFFICIENTS.md` contains the inherited language proof;
its larger historical coefficient layout is superseded here by the explicit
parity tuple, not mixed with it. The literal K215 machine and notices are
included under `compiler/upstream/` and `licenses/`.

The mathematical proof imports the existing universal native arithmetic
compiler and exact K215/ZFC-refutation theorem. The finite verifiers establish
their stated concrete claims; no end-to-end proof-assistant certificate or
consistency proof is asserted.

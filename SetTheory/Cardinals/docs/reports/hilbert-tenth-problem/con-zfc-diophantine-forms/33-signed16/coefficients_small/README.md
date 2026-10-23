# Smaller optional coefficient tuple

The complete tuple has `B=2^1012625`, retaining the 943-tile language and
the full positive and odd-scale native/Pell interface. Its four actual
integer payloads total 506,644 raw bytes, supplied as deterministic gzip.
This reduces the previous best base exponent `5^9=1953125` by 48.1536%.

`PROOF.md` gives the full adapter and generalized Boolean rank-control proof.
`COEFFICIENT_BINDING.json` identifies all four ports. **Replace all four
together; the MF port is already shifted by B-1.**

The main signed16 polynomial in the parent package deliberately retains its
source tuple. This directory is a separately proved coefficient improvement;
it does not silently change any fixed polynomial elsewhere in the package.

```sh
python3 build.py
python3 audit_independent.py
```

The standard library suffices. Each `.bin.gz` payload decompresses to the
minimal-width unsigned little-endian integer with no header. Decode with
`int.from_bytes(gzip.decompress(path.read_bytes()), 'little')`.

Finite verification checks the recipe, geometry, bounds, populations,
modular identities, and materialized bytes. The unbounded equivalence uses
the stated ordinary compiler and K215 calibration; no end-to-end Lean/Rocq
certificate or global optimum is claimed.

The inert JSON inputs and ProveIt licence are copied from commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`; exact hashes are in
`SOURCE_HASHES.json`. Tile language, mixed-radix decoder, and inherited proof
credit belong to ProveIt package 27 and its cited predecessors. This package
adds the stride-two geometry, the L=8101 choice, and its complete rank adapter.

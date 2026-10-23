# Wang943 coefficients with B = 2^1012115

`PROOF.md` gives the complete ordinary mathematical compiler adapter.
`COEFFICIENT_BINDING.json` identifies the new four-port tuple. Use all four
ports together. The high-mask port is already shifted by `B-1`.

The four exact fixed integers are supplied in `coefficients/*.bin.gz` as
gzip-compressed minimal-width unsigned little-endian payloads with no
header. The four uncompressed sizes sum to 506,664 bytes; largest coefficient
bit length is 1,016,946. These are already materialized finite integers,
not programs that wait for a refutation.

Reproduce with Python 3 and no third-party packages:

```
python3 build_coefficients.py
python3 audit_coefficients.py
```

The first program reconstructs the Wang943 language from the literal
K215 transitions, checks all finite native identities and the explicit
prime controller, and writes the exact coefficients. The second program
does not import the first: it reads the four exact integers, reconstructs
their definitions from the separately pinned tile list, and checks the
finite interface and controller again.

The new parts are the occupied label widths `[9,10,9,10]`, a single source
anchor feeding two separate synchronization targets, compact zero-mask
padding, and an explicit prime controller avoiding power-of-five rounding.

Compatible arithmetic systems may bind to this tuple without changing
their variable counts, degrees, or arithmetic-operation counts. A Jones
specialization requires fresh indices for its newly bound source quartic.
Ordinary proof status and all semantic dependencies are explicit in
`PROOF.md`.

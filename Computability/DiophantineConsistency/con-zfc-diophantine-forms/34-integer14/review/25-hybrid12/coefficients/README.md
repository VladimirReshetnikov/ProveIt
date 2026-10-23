# Wang 943 coefficients with mixed-radix clauses and external padding

This package supplies a complete replacement four-port tuple for the
inputless native compiler interface used by ProveIt's Con(ZFC) Diophantine
constructions. Its base is `B=2^(5^9)`, its largest coefficient has 1,958,376
bits, and its four exact integers occupy 977,220 uncompressed bytes.

The main mathematical argument is in `PROOF.md`. The reductions compared
there use the repository snapshot
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`.

Run the independent read-only check with Python 3:

    python3 -B verify_independent.py

Regenerate coefficients and receipts, if desired:

    python3 -B build_coefficients.py

The gzip payloads in `coefficients/` decompress to unsigned little-endian
integers with no header and minimal byte length. `COEFFICIENT_BINDING.json`
specifies all four ports, including the crucial shift
`MF_source=MF_native+B-1`. Replace the entire tuple together; no port mixing.

The construction changes coefficient size only. It preserves the variable
counts, degrees and gate counts of every compatible arithmetic skeleton.
It is an ordinary mathematical adapter supported by exact finite checks,
not a new proof-assistant certificate or a consistency proof.

## Attribution and inherited dependencies

The 943-tile language, binary occupied-edge encoding, four-anchor support,
population interface and correctness proof are based on the repository's
`19-wang943` package. This package adds mixed-radix clause fields, external
population padding and the short-transport geometry; it does not claim
the inherited components as new. It was developed with OpenAI assistance.

The literal machine table is unchanged from
`Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm`, SHA-256
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
Keep the repository's machine attribution and license notices when placing
these materials in ProveIt. The surrounding report must preserve the
logical dependency on the pinned K 215 endpoint and native compiler theorem.

## Source references

* [Original Wang943 compiler proof](https://github.com/VladimirReshetnikov/ProveIt/blob/ae3007ca4467011e0e051c84acb4a1dd13971b0e/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/19-wang943/compiler/WANG943_COEFFICIENTS.md)
* [Earlier compact geometry](https://github.com/VladimirReshetnikov/ProveIt/blob/ae3007ca4467011e0e051c84acb4a1dd13971b0e/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/19-wang943/compiler/WANG943_COMPACT_LAYOUT.md)

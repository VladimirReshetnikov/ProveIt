# Saturated nine-variable certificates

These four literal circuits retain the whole compact54-sharp tuple and the
H2082 source. They change the auxiliary Pell certificate by removing one
factor of D from its second norm.

| Circuit | Domain of all9 inputs | Live binary operations | Exact degree |
|---|---|---:|---:|
| `saturated_positive.json` | Strictly positive integers | 434 | 1628768 |
| `saturated_natural.json` | Nonnegative integers | 441 | 1628768 |
| `saturated_radical_positive.json` | Strictly positive integers | 1074 | 1103950 |
| `saturated_radical_natural.json` | Nonnegative integers | 1081 | 1103950 |

The ordered inputs are b,g,h,s,w,C,i,j,n. All names in `named_nodes` are
shared polynomial values rather than additional unknowns. Counts include
each live binary addition, subtraction and multiplication, all scalar
products and all squares. Constant leaves and reuse are free. Every node
and every declared input is live. The natural circuits equal the positive
circuits after increasing all9 inputs by one; the natural j directly
supplies the resulting j0=j_positive-1.

The ordinary existential equivalence is reviewed in `PEER_REVIEW.md` and
proved in the retained `source/PROOF.md`. These are new polynomials, not
identity rewrites of the frozen440-gate polynomial. Their refutation and
Con(ZFC) interpretation still composes with the named unbounded native/Pell
and source-calibration arguments. This checkpoint supplies no new Lean or
encoded object-ZFC derivation, and does not claim independent unsolvability.

The cheap positive endpoint improves both the440-gate, degree1845940
H2082 baseline's cost and degree. The radical form trades nine operations
against the1065-gate degree1158228 form for a lower degree. These are measured
comparisons of concrete circuits, not minimality claims.

## Complete fixed data and provenance

All11 signed fixed leaves reference
`../gap2082-compact54/fixed/BINDING.json`. The complete shared binding is
authenticated against the identical raw arrival member, including all
1565018 uncompressed leaf bytes. Those leaves are reconstructed exactly
from the same four original compact54-sharp ports, totaling215492 raw bytes.
MF_source is already shifted once. No port is individually substituted or
left as a free coefficient parameter.

`PINS.json` records the original archive
`con-zfc-saturation-and-projection-2026-10-23.zip` at arrival440dd03ab8,
SHA256 `ff9c3bb17a009b2ec11453b840a56aeb34f37144487e89cd65d5e96e5fc48b1c`.
It binds every retained raw member and each generated circuit. All circuit
nodes and mathematical metadata are byte-for-byte reconstructed as the
original arrival after reversing the single fixed-binding path relocation.
The ordinary proof, license, exact polynomial tables, original verifier and
440/447-gate source parents are retained. The large shifted tables are gzip
copies of the complete original JSON bytes, not sampled summaries.

The raw11-leaf binding SHA256 is
`e8fd5a7e4ced4e298d37a7a07ca89a14474777f61c62afc54318e1ec7edf12fd`;
the coherent four-port binding SHA256 is
`d176bcc6bf4b09fda67d9ffc0ced40471b0f72522b0772f06372fc80f20e654c`.
The shared reference avoids duplicating payloads, while retaining every
literal numeral needed to evaluate these circuits in the repository.

## Replay

From this directory, with Python3.12 or newer and only the standard library:

```sh
python3 verify.py
python3 -O verify.py
```

Both produce identical PASS receipts. The wrapper authenticates the
inspected original verifier before loading it, adapts only its compressed
table reader, and runs all its local algebra, circuit, domain, topology,
shifted-coefficient positivity, exact-degree and negative-control checks.
It independently authenticates every shared payload byte and reconstructs
all11 signed leaves from the four ports. It also checks complete unique
weighted leaders for both majorants and both defects. The finite algebra
verifier is independent of the arriving builders; this wrapper does not
claim a second independently implemented polynomial engine.

No incoming tree, previous candidate or Lean file was changed.

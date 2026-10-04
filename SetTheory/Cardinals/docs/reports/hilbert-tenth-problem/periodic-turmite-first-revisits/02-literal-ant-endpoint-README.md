# Paid residue endpoint component

## Result and scope

This self-contained packet proves and checks an endpoint selector relative to the already established 174-operation bounded ant-history relation. It selects the canonical coordinate residues

    x = 481225262775 modulo 481238074400,
    y = 29948 modulo 576000,
    incoming heading east, before departure.

These are the only reachable accepting clause of the separately frozen literal U15-to-ant interface, after its north-facing coordinate normalization. No color stencil is needed. The endpoint statement applies to any parent history satisfying the contract in CONTRACT.md, whether or not it is a valid universal load. The literal interface's exclusivity theorem is a separate input when interpreting the event as U15 halting.

Two fully literal alternatives are included:

| New positive witnesses | Equations | Fixed-numeral source | Literal-1/3 source | Maximum endpoint degree |
|---|---:|---:|---:|---:|
| HxPlus, HyPlus, BoundCol | 3 | 42 = 37M+5A | 101 = 94M+7A | 605950 |
| U, V, Uq, Vq, BoundCol | 5 | 42 = 37M+5A | 101 = 94M+7A | 576001 |

Gate outputs are computed integer expressions, not extra quantified variables. Equations and aliases are free in this component's source ledger. Multiplication by any fixed constant is charged. The 42-operation model has prescribed exact K,C,D numeral ports; they must not be freely guessed. The 101-operation model constructs them using only literal 1 and literal 3. Degrees expand all gates and count W, FinalHead, FinalSignPlus and the new witnesses as variables; fixed numerical coefficients do not contribute. No sum-of-squares or other single-polynomial combination is included.

These are endpoint-component counts, not a new total for 174, a universal arithmetic certificate, or a raw-input loader. Initial-board encoding, board translation/padding, input dilation, periodic background arithmetic, and final polynomial combination remain separate obligations. No upstream code or arithmetic schedule was executed, and no giant numeral was materialized. The construction descriptions are exact compact arithmetic DAGs, not numerical evaluation claims.

## Read in order

1. CONTRACT.md: parent ports, exact variable/count/degree conventions, coordinate normalization, source pins and remaining obligations
2. ENDPOINT_AUDIT.md: soundness, necessity, zero-quotient cases, strict column bound, heading and original shared chains
3. FOLDED_ENDPOINT_ADDENDUM.md: three-witness 42-operation fold and its unchanged 101-operation strict cost
4. FIVE_WITNESS_ENDPOINT_ADDENDUM.md: five-witness source, witness bijection and degree tradeoff
5. literal_source_verification.json: independently interpreted complete DAGs, including every constant-construction gate

The historical 43-operation fixed-numeral predecessor and its 101-operation strict counterpart are preserved byte-for-byte. Their historical absolute paths in notes identify where the audits were conducted; no external path is required for replay. Phrases in historical notes about an untouched "174-operation interface" mean the prior history certificate was not changed, not that it has been composed with this endpoint or with the literal loader.

## Exact replay

Use ordinary Python3 and its standard library:

    python3 /absolute/path/to/this/packet/replay_all.py

The driver creates a fresh temporary copy, runs four own-code commands from cwd /, and compares all six source DAGs and four receipts byte-for-byte. It uses no network, upstream code, numeric giant powers, or other packet. The independent fourth command reads the six JSON DAGs as data and does not import the source generators. It interprets every gate as a sparse polynomial in a formal base Z and the actual variables, then specializes Z=3 mathematically. It checks acyclicity, exact opcodes, live gates, target powers, all asserted equations and exact leading degrees without evaluating giant coefficients.

Assertions are part of these checks. Do not use -O or PYTHONOPTIMIZE. replay_all.py and verify_literal_sources.py explicitly reject optimized mode and their guards are tested. The three preserved generator/audit scripts do not contain explicit optimization guards; they are unsupported and not run under -O. The guarded replay driver executes them only in normal mode. No optimized pass is claimed.

The finite tests include 17280 candidate small endpoints, 80 horizontal-fold positivity cases, and 192 five-witness correspondence cases. They support the general integer proof rather than replacing it. The packet contains only newly authored code/proofs/receipts and explicit own DAG data; no full third-party article or source archive is bundled.

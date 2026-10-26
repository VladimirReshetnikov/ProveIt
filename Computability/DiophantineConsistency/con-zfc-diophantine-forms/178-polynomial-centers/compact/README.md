# Polynomial centers in a compact Diophantine equation for Con(ZFC)

This component supplies five literal ordinary polynomials in ten strictly
positive integer variables. All four fixed coefficient integers are supplied
and reconstructed by a finite recipe. The center construction is described
in `PROOF.md`; the top-level research article gives the integrated account.

| Circuit | Binary arithmetic operations | Exact degree |
|---|---:|---:|
| `trace_inverse85` | 85 | 232 |
| `square_transport85` | 85 | 232 |
| `lower_center87` | 87 | 228 |
| `centered_transport88` | 88 | 224 |
| `quotient_center96` | 96 | 220 |

For each circuit the ordinary proof, composed with the explicitly retained
native/refutation calibration, establishes in ZFC that it has no positive
integer zero exactly when Con(ZFC) holds. This does not assert the absence
of zeros separately. It is not a claim of global simplicity or a newly
completed end-to-end Lean/Rocq proof.

The square-transport variant resolves the particular `b²` endpoint left
unproved in package 163, section 9. The three centered variants give degree
reductions at the displayed costs. Keeping the bV weight lets their graphs
share V and saves one operation relative to a direct shifted-carrier
implementation. The quotient variant uses a fixed scale of 2 and a
polynomial quotient; no variable denominator is introduced.

## Exact reconstruction and checks

Use Python 3.10 or later, standard library only:

```sh
python3 -B build.py --check
python3 -B rebuild_coefficients.py
python3 -B verify.py
python3 -B -O verify.py
```

The builder reads the pinned parent graph as data. The independent checker
imports no producer or parent verifier and covers every actual circuit gate
by free polynomial identities. It checks all input and constant liveness,
cost, exact degrees and complete highest homogeneous components, both
parent coefficient identities, retained source hashes, actual numeral bytes,
and deliberate operator corruptions. The coefficient recipe independently
reconstructs all four integers, including the required native MF shift.
The tests authenticate finite data and algebra; the unbounded mathematical
proof is separate.

To record a fresh receipt without changing a sealed delivery:

```sh
python3 -B verify.py --receipt ../compact_receipt.json
```

The `--skip-coefficients` option is a development-only partial mode and is
not used by the complete release verification. Stored normal and optimized
receipts are included. No checker searches for a zero.

## Literal equation and evaluation

Each `equations/*.json` supplies a topologically ordered list of binary
arithmetic operations. Registers are abbreviations, not extra unknowns.
The fixed integers are in `coefficients/` as gzip-compressed little-endian
unsigned bytes, with exact raw and compressed hashes in each equation.

`evaluate.py point.json --equation centered_transport88` exactly evaluates a
supplied JSON array of ten positive integers and reports the sign, zero
status, and bit length. It does not print the potentially very large value.
The variable order is J,F,alpha,i,T,w,s,n,eta,zeta.

## Provenance and limits

The comparison snapshot is ProveIt commit
`fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb`. `SOURCE_LEDGER.json` identifies
every retained source file and resolves deduplicated intake members to their
canonical repository locations. Both parent proofs and the required
Pell/native proof sources are retained under `parents/`; their historical
relative links may use original archive paths, so the ledger is the
authoritative local mapping. The coefficient recipe and inherited notices
and licenses are retained without altering their mathematical content.

The new contribution is AI-assisted research. Independent reviews in this
workflow are separate internal mathematical checks, not external human
peer review. The construction retains the native/K215 route; it is not a
new proof calculus. The direct-calculus component elsewhere in the
integrated submission has a different ancestry and complexity profile.

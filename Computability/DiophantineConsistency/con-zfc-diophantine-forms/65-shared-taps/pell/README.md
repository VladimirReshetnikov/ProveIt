# Fourteen positive variables: degree26/92 gates and degree30/85 gates

`section.tex` is the complete paper section; `proof.md` is the companion
plain-text proof. The two literal integer-polynomial circuits are:

| File | Positive unknowns | Exact degree | Live binary operations |
|---|---:|---:|---:|
| `circuits/p14_degree26.json` | 14 | 26 | 92 |
| `circuits/p14_degree30.json` | 14 | 30 | 85 |

Every named register is an abbreviation. The four coefficient ports are
fixed, fully materialized integers from the **whole** compact package44
tuple; MF is already shifted. Unknowns are strictly positive integers.
The polynomials are sums of five squares. An absence of zeros in this
domain is equivalent in ZFC to syntactic Con(ZFC), by the proved new
reductions and explicitly inherited ordinary native-compiler/calibration
theorems. Neither consistency nor inconsistency is assumed or concluded.

The new mechanism uses a single Pell root to impose a weaker modulus,
recover the exact Pell index, and then impose the full modulus. It deletes
the former index coordinate while also desaturating a scaled coordinate.
The new proof is an existence equivalence with explicit positive witness
restoration, not an identity on all old coordinate tuples.

The comparison is pinned to repository commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486`. The inspected fourteen-positive
comparison is degree52/79 gates; these are smaller-degree tradeoffs.
The fifteen-positive degree24/90 construction remains a separate point.
No globally simplest equation, variable-count record, end-to-end Lean/Rocq
certificate, or exported object-language ZFC derivation is claimed.

## Reproduce

Python3.10+ and the standard library suffice. From this folder:

```
python3 verify_all.py
python3 -O verify_all.py
```

The driver performs all rebuilds/checks in a temporary copy, checks the
source and payload hashes, compares the two regenerated circuits byte for
byte, and runs independent identity/degree/formula checks. The proof in
the article is necessary: finite evaluations cannot prove the unbounded
existence equivalence or decide whether a refutation exists.

For an evaluation modulo1000003 with all inputs equal to1:

```
python3 evaluate.py p14_degree26 --modulus 1000003 1 1 1 1 1 1 1 1 1 1 1 1 1 1
```

For the primary circuit the input order is
`j,F,alpha,z,f,i,T,x,Y,r,eta,zeta,u,gamma`.
For the degree30 companion it is
`J,F,alpha,z,f,i,T,w,Y,r,eta,zeta,u,gamma`.

The three universal local cancellation identities are verified by a small
exact sparse-polynomial engine. The independent checker also verifies
all operation counts/liveness,200 direct-formula comparisons,48 complete
univariate polynomial rays with the actual fixed coefficients,10,584
bounded carrier cases, and two transcription corruption controls. These
checks pass with assertions disabled. Analytic leading forms in the proof
establish exact degree, rather than treating the sampled rays as a proof.

## Contents

- `build.py`, `carrier14.py`, `candidate14.py`: deterministic DAG builders.
- `independent_check.py`: separate finite algebra/data audit; no builder import.
- `circuits/`, `METRICS.json`, `CHECK_RESULTS.json`: exact definitions and receipts.
- `coefficients/`: complete authentic compact coefficient payloads, builders,
  literal machine/tiles, native proof, auditor and licenses.
- `upstream/`: exact pinned mathematical source interfaces.
- `INDEPENDENT_PROOF_AUDIT.md`: separate internal AI-assisted proof review.
- `SOURCE_PINS.json`: exact repository provenance for imported material.
- `NOTICE.md`, `LICENSE`: attribution and license.

The selected intermediate library variables and residue checks do not add
quantifiers. The large fixed integers are represented in binary to make the
equation explicit without printing hundreds of thousands of decimal digits.

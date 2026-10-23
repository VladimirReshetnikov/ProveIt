# Positive-gap compact nine-variable circuit

This directory contains a frozen arithmetic-circuit specification and finite
audits for the new nine-variable candidate. Its quantified variables are
`b,g,h,s,w,C,i,j,n`. The positive-domain circuit has **465 live binary gates**
and exact total degree **1,797,796**. The companion on nonnegative integers
has 472 gates and the same degree. All large exponents in the definition are
fixed integers; no exponentiation by a quantified variable is used.

The coherent compact coefficient tuple is the whole native44 tuple. Its four
authenticated payloads and unchanged binding manifest are included locally.
The manifest calls the ports `beta,K,MC,MF_source`; the source formulas and
circuit recipes call the same four values `beta,K0,MC,MF`. Mixing these values
with ports from another tuple is not permitted.

## Reproduce the finite artifacts

Only Python's standard library is needed. From this directory, run:

```sh
python3 build_nine.py
python3 audit_circuit.py
python3 write_source_table.py
```

`build_nine.py` regenerates all four JSON circuits, the degree certificates,
and the gate ledger from the frozen source and packing layout. It performs a
small deterministic choice among six circuit implementations; it does not
search for a new code layout. `circuit.py` is its minimal binary DAG builder.

`audit_circuit.py` never imports either builder. It checks:

- exact variable names, topological ordering, complete liveness, and binary
  operation counts for all four circuits;
- gzip and raw SHA-256 hashes, actual bit lengths, and the complete coherent
  fixed coefficient tuple;
- every fixed coefficient recipe, the bound exponent 1,182,955, and the
  exact binary threshold calibration;
- 54 small symbolic fragments extracted from the literal DAGs, six symbolic
  polynomial identities, and exact common-ancestor expression normalizations
  proving the primary and certificate forms are identical;
- independent exact leading-degree propagation for both certificate DAGs,
  including 49 named degrees in each and final diagonal leading coefficient
  `2^186 * a^898488 * c^400`, which is positive;
- 264 modular implementation diagnostics at three moduli, including 12,804
  named-register comparisons with a separately written direct formula.

The modular comparisons are diagnostics, not an identity proof or an
unbounded semantic proof. The source-extraction certificate is audited
separately in the enclosing submission. The finite circuit audit neither
certifies the inherited native compiler/Jones semantics nor decides
consistency.

`write_source_table.py` expands 22 independently written, readable source
formulas and exactly compares them with all 86 weighted records over
`Z[beta,K0,MC,MF]`. It emits `source_equations.tex`, an input fragment requiring
the `amsmath` and `longtable` packages. The table includes residuals, row
target exponents, variable indices, and code weights. It explicitly identifies
the original transport coordinate and its relationship with the shifted
native coordinate.

The generated receipts are `generated/INDEPENDENT_CIRCUIT_AUDIT.json` and
`generated/SOURCE_TABLE_AUDIT.json`. The auditors also work with Python's
`-O` option because validity checks use explicit exceptions, not assertions.

## Primary specifications

`generated/gap_100_positive.json` and
`generated/gap_100_natural.json` are the operation-counted polynomials. The
two files ending in `_certificate.json` define algebraically identical
polynomials in a form that exposes their exact degree. Their additional
gates are proof artifacts and are not charged to the primary circuits.

`data/parent_source.json` is the new 86-record source, not a byte copy of a
historical upstream source file. `data/split_code.json` records the frozen
weights and target positions; `data/split_kernels.json` records the resulting
three univariate coefficient kernels. `DEGREE_AND_BINDING.md` explains the
compact calibration and degree formulas.

The mathematical consistency equivalence remains conditional on the
enclosing submission's explicitly stated native instance identification
and inherited semantic theorems. The full proof must include the positive
transport-coordinate bridge and the positive-gap source transformation;
the finite JSON checks alone do not establish that semantic conclusion.

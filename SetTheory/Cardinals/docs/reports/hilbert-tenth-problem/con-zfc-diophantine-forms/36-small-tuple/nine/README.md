# A smaller evaluator for the degree-best Jones equation

This directory combines package 30's 31-variable parent and tight finalizer
with package 27's radix-five homogeneous evaluation and exact coefficient
folding. It then rebinds every fixed coefficient to the new complete compiler
tuple in `../coefficients/`.

| Construction | Domain | Operations | Exact degree |
|---|---|---:|---|
| Package 30, pinned baseline | 9 nonnegative unknowns | 1840 | 120724 * 5^32 + 366 |
| Same polynomial, new evaluator | 9 nonnegative unknowns | **1587** | unchanged |
| Affinely shifted new evaluator | 9 positive unknowns | **1582** | unchanged |
| New compact-tuple instantiation | either of the above domains | same counts | unchanged |

The natural evaluator saves 253 operations (13.75%) on exactly the original
polynomial. This is not the fewest-operation nine-variable construction:
the retained nu=32 alternatives have lower operation counts and higher
degrees. No quartic with fewer than 31 variables is claimed here.

The new compact instance has `z_index = 2^4058127`, versus the old
`2^45933757`. The four port bit lengths are
`(1012115, 1016946, 1012115, 1012116)` in the order
`(beta,K,MC,MF_source)`. The huge fixed `y_index` is an explicitly bounded
58,905-term sum, not an unknown or an uninstantiated enumeration index.

## Files

- `compact/nine31_natural.json` and `compact/nine31_positive.json`: recommended
  coherently rebound circuits, including all nine input names and all gates.
- `compact/CONSTANTS.json`: all 402 nonzero weighted coefficient recipes,
  and the complete bounded definitions of z, y and the unused index u.
  Every unlisted weighted coefficient is zero.
- `compact/INDEX_BOUND_CERTIFICATE.json`: exact sparse power-of-two bounds
  checked for all 402 coefficient records.
- `compact/z_index.bin.gz`: actual new z, unsigned little-endian after gzip
  decompression. This is 507,266 raw bytes and 527 deterministic-gzip bytes.
- `compact/REBOUND_CHECKS.json`: materialization hashes and final metrics.
- `nine31_folded_natural.json` and `nine31_folded_positive.json`: original
  tuple versions, retained to distinguish exact polynomial optimization
  from subsequent coefficient rebinding.
- `coefficient_aliases.json`: exact literal and identical-recipe folding.
- `NINE_PROOF.md`: construction, identity proof and dependency boundary.
- `source/`: inert pinned source data, source proof, authentic original
  coefficient payloads and license.

There are 80 live fixed leaves in each recommended circuit: z, y, and 78
distinct nonliteral weighted coefficient recipes. None is existential.
The apparent 402 coefficients in the index recipe include literals and
identical recipes; replacing these by literals or shared fixed leaves is an
identity in the four compiler ports.

## Reproduce

From the containing package, run:

```
python3 nine/optimize_combined.py
python3 nine/rebind_compact.py --coefficients coefficients
```

The builder uses only Python's standard library. It checks the correction
polynomial as an exact sparse polynomial over the fixed ports and a formal
base variable, then checks 12,032 modular named-node comparisons against the
pinned baseline and 128 checks of the positive-domain affine shift.
The rebinding script verifies actual payload hashes and bit lengths before
recomputing the strict index bound. All final gates and inputs are live.

These audits establish the new algebra and coefficient instantiation. The
unbounded compiler, Pell and Jones arguments are ordinary mathematics
formalizable in ZFC, imported as identified in the report and source proof.
No new end-to-end Lean/Rocq certificate or proof of Con(ZFC) is claimed.

## Attribution

Upstream repository: VladimirReshetnikov/ProveIt, commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`, report packages 27 and 30.
The radix-five identity and coefficient folding come from package 27;
the 31-variable parent, tight magnitude companion finalizer, and degree
certificate come from package 30. `circuit_tools.py` adapts its small DAG
utilities from package 30; its license is retained as
`source/LICENSE.ProveIt`. New synthesis code is `optimize_combined.py` and
`rebind_compact.py`. The weighted-quadratic moment method in the builder is
an audited exploratory alternative, not the selected final circuit.

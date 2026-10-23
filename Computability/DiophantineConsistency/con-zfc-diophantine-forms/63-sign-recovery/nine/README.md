# Nine variables with a deflated polynomial majorant

This package defines an ordinary integer polynomial in nine strictly positive
integer variables whose zero set is equivalent, through the pinned ProveIt
source and compiler theorems, to the existence of a finite syntactic ZFC
refutation. Thus ZFC proves that it has no positive zero if and only if
Con(ZFC). The mathematical proof and its inherited dependencies are explicit
in `PROOF.md`; the supplied checkers do not claim to establish that entire
semantic theorem inside a proof assistant.

The new ingredient is an exact algebraic deflation of the radical majorant.
It uses the identity `e^2=16i^2D-i^2((40A-41)C^2+16)` to cancel a large
remainder, then certifies a seventh-order majorant by a 264-term expansion
with strictly positive coefficients.

| Literal equation | Domain | Variables | Exact degree | Binary operations |
|---|---|---:|---:|---:|
| `generated/order7_positive.json` | Strictly positive integers | 9 | 1,573,266 | 504 |
| `generated/order7_natural.json` | Nonnegative integers | 9 | 1,573,266 | 511 |
| Pinned package 59 predecessor | Strictly positive integers | 9 | 1,910,404 | 473 |

The degree decreases by 337,138, or about 17.6475%, with 31 additional
operations. This is a degree/size tradeoff; it is not a claim of an absolute
minimum or simultaneous improvement in every measure. Operations are binary
addition, subtraction and multiplication, including multiplication by an
integer. Fixed constants and register reuse are free. The 504 operations are
168 additions, 29 subtractions and 307 multiplications.

## Reproduce

Python 3.10 or later and its standard library suffice. From this directory:

```sh
python3 build.py
python3 verify.py
```

The build is deterministic. Verification requires no repository checkout,
network access, unprovided files, or third-party packages. All four native
coefficient payloads are included. `VERIFICATION.json` records the check
results from the delivered version. The auxiliary `*_certificate.json`
circuits compute `D^20` times the primary polynomial and are used to certify
the degree; their larger operation counts are not the primary cost claim.

## Files

- `PROOF.md`: definitions, exact positivity theorem, both directions of the
  finalizer, exact degree, and inherited semantic scope.
- `section.tex`: a LaTeX section suitable for inclusion in the parent report.
- `build.py`, `circuit.py`: explicit arithmetic circuit builder.
- `verify.py`: fixed-byte authentication, exact rebuilds, graph and degree
  checks, plus 480 comparisons with a separately written literal evaluator.
- `check_exact.py`: exact integer polynomial identities and all 264 positive
  coefficients, without importing the builder.
- `check_source.py`: inherited finite source isolation check, adapted to
  local paths and the actual base exponent.
- `data/`: the unchanged 31-variable source, split encoding kernels, and the
  new complete positive-coefficient certificate.
- `coefficients/`: the complete original31 tuple as compressed unsigned
  little-endian bytes, together with hashes and aliases.
- `upstream/`, `SOURCE_PINS.json`, `NOTICE.md`, `licenses/`: retained proof
  sources, exact attribution, source pin, and licenses.

## Inherited and new components

The native compiler, source system, source coordinates and targets, binary
encoding, exact population calibration, Jones ratio theorem, free carrier
coordinate, quotient shift, and positivity-first norm are inherited. The
deflated seventh-order majorant, its exact positive-coefficient certificate,
its adaptation to the nine-variable finalizer, and the resulting degree
certificate are the new contribution. The consistency endpoint continues to
use the existing K215 compiler; the proposed improvement is in the arithmetic
representation after that compiler.

The result is AI-assisted research with internal independent algebraic
checking. It has not received external peer review, and no new end-to-end
Lean or Rocq verification is asserted.

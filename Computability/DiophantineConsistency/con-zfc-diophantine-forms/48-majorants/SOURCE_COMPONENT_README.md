# Support-aware source coding for consistency equations

This is the self-contained arithmetic and source-proof component of the
October 23, 2026 research result. Read `SOURCE_PROOF.md` for the new theorem,
the explicit weights, the source equations, and the dependency boundary.
`data/parent_system.json` is the exact inherited 31-positive-variable,
22-quadratic source. Four fixed native ports are included in `data/ports`.

The new support certificate isolates 71 needed monomials among 528 pairs
using maximum weight 179, compared with the former full-Sidon maximum 799.
The second layout overlaps source bands while protecting all 22 outputs.

| Layout | Unknown domain | Exact degree | Evaluation operations |
| --- | --- | ---: | ---: |
| Uniform | 9 positive | 29,157,244 | 562 |
| Uniform | 9 nonnegative | 29,157,244 | 565 |
| Uniform | 10 integers | 53,325,896 | 595 |
| Overlap | 9 positive | 21,823,612 | 618 |
| Overlap | 9 nonnegative | 21,823,612 | 621 |
| Overlap | 10 integers | 39,914,856 | 651 |

These numbers use inherited finalizers unchanged. Other files in the
containing research archive may supply a separately proved improvement to
the nine-variable finalizer.

## Build and audit

Python 3.10+ and only its standard library are needed:

```sh
python3 code/build.py
python3 verify.py
python3 -O verify.py
```

The independent verifier does not import any builder. It expands the
literal parent, checks exact source identities and coefficient recipes,
binds every fixed port, checks all live gates, compares direct source
evaluations, and verifies three-prime exact-degree certificates. Its
`VERIFICATION.json` receipt does not certify unbounded unsolvability.

`generated/*.json` are literal division-free polynomial DAGs, not programs
with tests, hidden witnesses, or variable exponents. Every addition,
subtraction, multiplication and scalar multiplication is charged. Fixed
coefficient leaves and reuse are free. Their byte payloads and construction
recipes are nevertheless supplied explicitly and checked separately.

The nine-variable files ending `_degree_certificate.json` evaluate the
same polynomial through an exact telescoping identity that exposes its
leading cancellation. They are not the primary operation-count files.

## Attribution and boundaries

The source parent, complete native coefficient tuple, Jones/Sun arithmetic
and previous finalizers are inherited from ProveIt. Exact historical copies
and original notices are under `inherited`; `SOURCE_PROVENANCE.json` gives
their hashes and pinned repository paths. `code/circuit.py` is inherited
from package 45; `code/common.py` adapts package 40's coefficient and Horner
helpers; `code/nine_tail.py` and `code/ten_tail.py` transcribe the corresponding
unchanged finalizers. The new source builder, layout, support certificate
and independent audit were prepared with AI assistance.

All four native ports travel as one complete tuple. `MF_source` is already
shifted by the native base minus one. This package never splices ports from
different instances and never applies a second shift.

The mathematical theorem inherits the native compiler, literal-machine
calibration and arithmetic finalizer proofs. No new end-to-end Lean/Rocq
proof or object-language ZFC derivation is claimed. This is an explicit
equivalence construction; it proves neither Con(ZFC) nor its negation.

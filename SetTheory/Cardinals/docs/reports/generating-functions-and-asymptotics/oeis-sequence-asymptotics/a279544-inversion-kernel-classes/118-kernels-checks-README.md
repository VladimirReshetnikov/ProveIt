# Exact checks for the two inversion-sequence kernels

Python 3.10 or later; standard library only. No installation, network access,
source-paper copies, private research notes, floating-point decisions, or fitted
constants are required. From this directory run:

```sh
python -B check.py
python -B -O check.py
python -B validate_bundle.py --output /tmp/report118-validation.json
```

Exit 0 means PASS, 1 a named check failure, 2 an unexpected exception. An ERROR
never counts as a successful negative test. Every substantive guard is an
explicit exception, so optimization cannot disable verification. The
`--skip-integrity` flag is for development, not verification of a sealed bundle.
Outputs must be outside this checks directory.

## Exact scope

For each class the independent state dynamic program and the rational
root/Mobius-orbit formula agree at all 81 coefficients n=0,...,80. The tree
normalization is explicit: class214 targets s=0,p<=2; class1509 targets s<=1.
Independent brute-force forbidden-relation counts agree for n=0,...,8.
Only 29 class214 and 26 class1509 displayed OEIS terms are external checks.
The longer internal coefficients are not represented as externally verified.
All external values and definitions were checked on the linked OEIS pages on
2 October 2026. The fixture links the versioned primary source and records
the hash of the earlier finite-check record for provenance; that record is not
needed to replay this bundle.

Sparse exact polynomials verify the class214 kernel substitution, F-to-G
identity and factor expansion. Independent rational functions verify the
class1509 scalar source identity, reversed recurrence and root specialization.
The gamma-ratio recurrence independently recovers 3/8,25/128 and 15/8;
exact Laurent polynomials verify the first three inverse coefficients.
Finite threshold boundary tests include equality; they do not certify an
asymptotic threshold algorithm.

For class214 the critical derivative recurrence is recomputed at M=8 and 96,
including the exact conservative tail constants. Machin alternating rational
intervals enclose pi; scaled integer square roots enclose sqrt(pi). Decimal
endpoints use integer floor/ceiling only. Degree-five rational jets at M=64
use the closed Mobius iterate and reproduce every displayed h and c1,c2 bound.
The exact complex-circle bounds give 200000*(101/400)^64 for the H tail.

For class1509 exact rational inequalities prove the stated bound |yV|<2/3
conditional on the analytic majorization argument in the report. The original
N=24 nonzero-amplitude certificate is independently recomputed by 60-place
outward interval arithmetic and direct quotient automatic differentiation.
Its narrower independently obtained intervals lie inside the reported coarse
intervals; identical interval endpoints are not assumed. N=96 degree-five
interval jets reconstruct the square root coefficientwise and reproduce the
reported tighter C,c1,c2 bounds. The both-branch t circle has radius 1/10000;
the U,V tail is E=(32/15)*4^(1-N), the quotient tail is 100E, and coefficient
errors are 100E*10000^j. All interval divisions reject zero-containing divisors,
and all square roots reject negative lower bounds.

Normal convergence, analytic continuation, uniqueness of the dominant
singularity, singularity transfer, and eventual inverse rounding are analytic
proofs in the report. Finite tests cannot replace those arguments. Inverse
error constants and starting thresholds are existential. No numerical fitting,
full transseries, non-D-finiteness proof, or publication-priority claim is made.

## Strict inputs and replay

The JSON fixture has closed schemas; integer fields reject booleans; fraction
strings must be canonical and reduced. Floats, nonfinite values, duplicate
keys, missing/extra keys, incorrect array lengths, malformed decimals and
reversed intervals fail. Sizes and mathematical cutoffs are fixed before any
size-dependent calculation. Inputs are limited to 256 KiB, the inventory to 32
files and 64 entries. Symlinks and special files are rejected.

MANIFEST.json lists every ordinary file below this directory except itself.
There are no cache exclusions: unlisted bytecode fails. The manifest detects
changes but is not an authenticity signature against replacement of both code
and data. Run with -B; local imports disable bytecode writing too.

The replay harness verifies complete normal and optimized outputs agree,
repeats both modes in a fresh temporary copy, and verifies before/after hashes.
It mutates every fixture leaf individually and reseals those temporary copies,
so semantic corruption must be rejected by schema or mathematics. Additional
negative tests cover corrupted mathematical code, malformed data, changed or
missing files, unlisted files and bytecode, unsafe manifests, symlinks, FIFOs, oversized files, and zero-divisor/negative-square-root guards.
Each negative must return its exact named FAIL in both modes. Subprocesses are
limited to 45 seconds, with at most 4 in parallel and a 1200-second total deadline.
The actual successful mutation counts are recorded in the enclosing package's
verification_results.json after execution; no count is inferred from intentions.

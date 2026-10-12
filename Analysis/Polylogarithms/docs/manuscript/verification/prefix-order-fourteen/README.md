# Complete smaller-order-fourteen prefix certificate

For every integer (bge8), the original rational harmonic-tail matrix

```text
M[t,k] = B[2(t+k-6)] / (2(t+k-6))!
         * ((2b+2t-13)!/(2b-2k)!
            + indicator(k<7) (2t+1)!/(14-2k)!).
```

is nonsingular, with negative Bernoulli indices interpreted as zero.
The manuscript's Section 8.45 supplies the analytic coefficient model,
the exact reduction to a seven-square determinant, and the general
effective eventual theorem. These are mathematical dependencies of this
certificate. Together they give ordinary convergent polygamma-product
identities for every larger even order. This is formal rational coefficient
rank; it does not assert arithmetic independence of evaluated constants.

The exact sufficient threshold is (B_7=80640). The preserved threshold
program comes unchanged from the quartic reconstruction report. It expands
all 49 scaled entries and derives the coefficient norm and rational
comparison; the manuscript proves why this implies nonvanishing at every
integer (bge B_7).

The remaining 80,632 integers (8le ble80639) have nonzero residues modulo
the prime 7,340,033. Use the original matrix below (b=14), and the exact
retained determinant above it. All denominators are units modulo the prime.
The binary residue file contains every case, not a sample.

To reproduce the full threshold and both complete finite calculations:

```powershell
py -X utf8 check_completion.py
```

Requires SymPy, python-flint, NumPy and `g++`, with Python assertions enabled.
Run from any directory; generated tables, compiler outputs and regenerated
residues go into a fresh temporary directory. A separate replay receipt is
written here after all mathematical comparisons succeed. The preserved
binary payloads are never rewritten.

Two independent Bernoulli table algorithms agree on all 161,281 coefficients:
FLINT inverse-series arithmetic and standard-library exact integer Kronecker
convolution, each with the complete reciprocal-product identity checked.
The word bound prevents carries in the integer convolution. Native numeric
forward differences and Gaussian elimination agree with independent symbolic
Stirling coefficients and division-free subset determinants on every case.
Signed integer bounds are checked for every matrix dimension, including the
larger original matrices below the contraction threshold.

`rank14-bernoulli.bin` uses the little-endian `R14B` header, then the prime,
smaller half-order, threshold and greatest coefficient index as four uint32
values, followed by the complete uint32 coefficient table. The `R14D`
residue header stores the prime, smaller half-order, first and last case, and
case count, followed by all uint32 residues in increasing parameter order.
The source program enforces these formats and checks complete file equality
after regeneration. The certificate is exact finite arithmetic, with a
separate written infinite proof; it is not a proof-assistant formalization.

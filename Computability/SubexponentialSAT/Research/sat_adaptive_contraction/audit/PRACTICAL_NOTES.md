# Modular implementation of the joint Cauchy kernel

This package is a finite-precision implementation of the existing joint
Cauchy factorization. It is not an end-to-end SAT solver. The new work is
bounded modular arithmetic, safe symbolic cancellation of valuations,
reused denominator inverses, a streaming interface, and measured comparison
against both the archived implementation and a strengthened recurrence
control. The product recurrence itself already occurs in the independent
verifier of the joint-Cauchy packet and is not claimed as a new identity.

## Input and output

Let `L=2^a`, `N=L/2`, `R=2^i`, `0<=i<a`, and let `t` be a nonzero integer
in `[-L,L)` with valuation `i`. The input `zeta=(u,v)` is an exact integer
pair representing `u+v U` in the unramified quadratic extension with
`U^2+U+1=0`. Set `T=t+2^(a+1) zeta` and

    s_j = (j mod R) + 2R floor(j/R),  0 <= j < N,
    E_b = 2 floor(b/R) - popcount(floor(b/R)),
    w_b = a+1-i + 2 E_b.

The output contains the same normalized target and source factors as
`JointCauchyKernel.feature_tables`, reduced modulo `2^p`, and keeps exactly
those modes with `w_b<p`. It supports arbitrary signs of `t`, integer
prime-subring inputs, nontrivial extension inputs, nonunit `zeta`, and zero
`zeta`. It does not provide a generic unramified-extension implementation
or accept arbitrary rational `zeta` directly.

## Why finite-precision cancellation is safe

For each fixed row point `x=s_j`, maintain

    P_b(x) = product_{h<b} (x-s_h)/(T+x-s_h),
    Q_b(x) = product_{h<b} (s_h-x)/(T+s_h-x)

as an exact integer exponent and a unit residue modulo `2^p`. Each factor
is split *before* modular reduction: for example a nonzero integer
`d=x-s_h` has numerator `2^v2(d)` times an odd integer, and its denominator
is split into a power of two and a unit pair. Since the slot set has zero
at bit `i`, a slot difference has valuation below `i` or above `i`, never
exactly `i`. Consequently

    v2(T+d)=min(i,v2(d)) <= i,

and all denominator inverses are inverses of units after cancellation.
Multiplication of unit residues needs only `p` bits. Dividing by `2^E_b`
subtracts `E_b` from the separately maintained exponent; no modular
residue is divided by two. The prior integrality lemma guarantees the
remaining exponent is nonnegative. This is the reason no precision guard
bits proportional to `E_b` are needed.

The normalized row is `2^(-E_b) T P_b(x)/(T+x-s_b)`, and the normalized
source is `2^(-E_b) T Q_b(x)/(T+s_b-x)`. Multiplying the row by
`C(T)/(C'(0)T) * 2^(2E_b)` gives the target. The prefactor uses the same
valuation/unit method after cancelling its `q=0` factor symbolically.
When `zeta=0` its exact zero factor is handled explicitly.

Every omitted target has valuation at least `w_b>=p`, and every source is
integral. Thus the omitted rank-one terms vanish modulo `2^p`.

## Reusing inverses

The denominators depend only on the integer difference `d`, and there are
at most `2L-1` differences. Build their normalized units once. The standard
prefix-product batch inversion computes all inverse units with one ring
inversion and `3K` ring multiplications, where `K` is the number of distinct
denominators. A separate scalar modular inversion computes the prefactor's
odd denominator. Cached products of the inverse with the unit part of `T`
save two ring multiplications per active feature pair.

Batch inversion is an optional strategy; the benchmark also measures
separate inversion of the same cached units. It is not uniformly faster at
small precision. The main performance gain comes from keeping finite
precision, retaining only useful modes, and reusing products and inverses.

## Resource statement

Let `B` be the number of retained modes and let
`S=NB-B(B-1)/2`. Table construction uses `O(NB+L)` ring operations. For
nonzero `zeta` the instrumented count in the batch variant is exactly

    4K + (2L-1) + 5S - 2B

ring multiplications, at most one ring inversion (zero when B=0), and one additional scalar
inversion. Generating and sorting the difference set also uses
`O(NB+L log L)` elementary integer operations. Ring multiplication acts on
`p`-bit residues; standard batch inversion makes the bit cost
`O((NB+L) M(p) + I(p))`, apart from input normalization and the smaller
integer bookkeeping, where `M` and `I` denote multiplication and inversion
costs in the fixed degree ring. This bound describes the implementation
kernel; it does not change the global SAT exponent on its own.

The table API stores `O(NB+L)` ring elements, including its unavoidable
`2NB` output pairs. `iter_columns()` yields each pair of columns and uses
`O(B+L)` working ring elements, excluding consumer storage. Both variants
use polynomial resources in the parameters.

## Controls and reproducibility

`reference_joint_cauchy.py` is the unchanged archived source. The source
manifest records its original archive, internal path, and SHA-256.
`reference_recurrence.py` adapts the existing independent verifier's
quadratic-operation rational recurrence to both rational and quadratic
extension inputs, removes checking from the timed section, and gives it
the same cutoff as the modular implementation. Thus the reported speedup
against the recurrence control is not caused by forcing that control to
construct discarded modes or to run its verification suite.

`benchmark_kernel.py` includes exact-to-modular conversion in both exact
methods: producing tables modulo `2^p` is the matched task. It performs one
warmup, then five alternating-order paired measurements by default. Every
output must be exactly equal before timing results are accepted. It saves
all wall-clock and process CPU samples, medians, environment metadata,
operation counts, and output digests. The benchmark cases are small and
synthetic; the results are evidence about these local kernels only.

Run from this directory:

```bash
python3 check_modular_cauchy.py
python3 -O check_modular_cauchy.py --output validation_optimized.json
python3 benchmark_kernel.py --repeats 5
```

The checks compare exact target/source factors against two controls and
independently reconstruct the original polynomial matrix after cancelling
the designated factor. They test signed grid nodes, both arithmetic
domains, zero and nonunit parameters, multiple precisions, batch versus
separate inversion, streaming versus tables, random unit inverses, and
invalid inputs. Explicit exceptions remain active under `python -O`.

All data in `validation.json`, `validation_optimized.json`, and
`benchmark.json` must be interpreted under this local-kernel scope. No
claim of better wall-clock SAT solving, formal verification, or dominance
over implementations of unimplemented conditional proposals is made.

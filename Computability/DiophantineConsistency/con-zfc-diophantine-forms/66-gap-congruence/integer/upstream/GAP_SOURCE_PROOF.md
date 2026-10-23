# Positive gap coordinates: 89 to 86 quadratic coefficient records

## Exact pinned parent and domain

The inert `parent_source.json` is the incoming degree-separated construction's
31-positive-variable, 22-equation parent, SHA256
`1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`.
All four compiler ports must be inherited together. This transformation does
not change a port or replace the inherited refutation/calibration theorem.
Assume beta and K0 positive; the domain throughout this section is strictly
positive integers. The fixed ports MC,MF do not enter the following bijections.

First perform the incoming invertible row operations
rho14=r14+r2 and rho15=r15+r3. They give 89 coefficient records.
Write q=1+beta*J, k=eta+zeta and Y=a-E. Rows 4,5,6,7 say

Y=s*N, E=X*Y, c-eta=k*Y, P-k=E*(c-eta).

Thus on every positive root the two differences Y and c-eta are strictly
positive, as is P-k. Replacing the old P by T+k therefore gives a bijection
between old positive roots and positive roots in T. The inverse is T=P-k.
No Pell theorem is needed: these are four defining equations and positivity.
The only affected equations become

rho7 = T-E*c+E*eta,
rho8 = tau^2-T^2-T*eta-T*zeta-1.

Row 7 loses its two linear terms -eta,-zeta; row 8 has the same monomial
support with changed signs. This gives 87 records without increasing degree.
For positional compatibility the generated JSON calls the new T coordinate
`P`; its `coordinate_map` records old P = new P + eta + zeta.

## Two one-record improvements

Two alternative (not simultaneous) changes yield 86 records each.

N-gap version: replace old N by n+1. Rows 1,2 give old N=q^3. Since J>=1
and beta>=1, q>=2 and old N>=8, so n>=7 is strictly positive. Conversely,
a positive root in n maps to a positive old N=n+1. The inverse is valid
on every parent root. This replacement is a positive-zero-set bijection.

L-successor version: replace old L by ell-1. On every old root,
ell=L+1=q^2>=4; thus ell is positive. Conversely, rows 1,2 of the new
system force ell=q^2>=4, so old L=ell-1 is strictly positive. Again the
maps are inverse on zero sets. This version does not incorrectly treat
arbitrary ell=1 as a valid old coordinate: row 1 excludes it.

Both changes are affine with integer inverse. They preserve quadraticity.
The N-gap and L-successor changes are alternatives; composing them is not
claimed to improve the count.

## Reuse of the existing finite positional certificate

Using the same 31 weights and 22 targets in `split_code.json`, independently
expand every residual, group coefficients by witness monomial, form the
three degree-separated kernels and check every kernel/word interaction.
The results are:

- P-gap: 87 records, 22482 interactions.
- P-gap plus N-gap: 86 records, 22481 interactions.
- P-gap plus L-successor: 86 records, 22451 interactions.

All have zero target collisions. The maximum label remains 116; kernel
degrees are (1719,2020,1929), so the exact convolution height remains 2161.
The degree-2 leading coefficient remains +1, from row 5. In particular the
incoming unconditional positivity proof becomes stronger: its linear-kernel
degree is reduced by seven, from 2027 to 2020. The existing coefficient
majorant remains sufficient: the altered coefficients have no larger
port height or integer magnitudes than already bounded ones.

`build_gap_source.py` independently checks the parent's residual formulas
against its full literal monomial data, applies the stated substitutions,
and checks the finite coefficient-extraction identities over symbolic ports.
The resulting ordinary mathematical source equivalence is universal; these
finite polynomial checks are not a proof of the inherited compiler theorem
or a new proof-assistant certificate.

## A further 85-record source, requiring a new positional layout

Replace old P by T+k and old N by n+q, where q=1+beta*J. This is still
an affine substitution in the witness coordinates, with integer coefficients
depending only on the fixed port beta. On an old positive root,
n=q^3-q=q(q^2-1)>0. Conversely a new positive root maps to positive
old N=n+q and old P=T+k. The maps are inverse on zero sets; no divisor or
additional quantified coordinate is introduced. This produces 85 records.

The old positional layout is NOT valid for this source: one interaction
from the new J*s monomial in row4 contaminates row21. GAP_SOURCE_CHECKS.json
records this failure explicitly. A fresh, independently verified positional
certificate must accompany any final equation using gapNq85_source.json.
The coefficient source and its positive-zero-set bijection are valid
independently of any particular positional certificate. Source metrics are
not final equation metrics.

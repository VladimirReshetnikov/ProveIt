# The exact choice F=t^t is also sufficient

This further sharpening was proposed by the root research agent and
independently checked here. It is an optional semantic simplification of
`REDUCED_FRONT_PROOF.md`; it is not an improvement in collected term count.

## Label separation at the boundary

Let t>=2 and F=t^t. In a label-flow product, cancel the factors with label
zero. If the two remaining products have different factor counts, the
smaller count r is at most t. The smaller product is at most
`t^r(F+1)^r`, while the larger is at least `(F+1)^(r+1)`.
Since F+1>t^r, equality is impossible. Thus both counts are the same r<=t.

For each product polynomial P(Z)=product_(i=1)^r(1+a_i Z), with
1<=a_i<=t, its coefficient c_j at every degree 0<=j<=r satisfies

    1 <= binom(r,j) <= c_j <= binom(r,j)t^j <= t^r <= t^t=F.

The penultimate bound follows from
`binom(r,j)=binom(r,r-j)<=r^(r-j)<=t^(r-j)`.
Both product polynomials have a strictly positive coefficient at every
degree through r. Consequently the difference of corresponding
coefficients has absolute value at most F-1, even if one individual
coefficient equals F. The constant coefficients are both one.

The least-nonzero-coefficient argument modulo F therefore applies
unchanged: equality of the products at F gives equality in Z[Z], and
unique factorization recovers all positive-label multiplicities.

This is a difference bound, not the false claim that each individual
coefficient is strictly below F. For example, when r=t and all labels
equal t, both the leading and penultimate coefficients can equal t^t.

## Radius and simultaneous completeness

For t>=16, the proved lcm estimate gives

    lcm(1,...,t)^2 <= 16^(t-1) < 16^t <= t^t=F.

Thus B=binom(F+t,t), the linear radius R=F, and the affine radix q=4z+1
remain valid. All signed-bootstrap size estimates remain valid as well:
t^t>=16^16>2^32 and F>=t.

In completeness choose a sufficiently large **even** h in t=16+h^2.
Then t is even and

    v_2(F)=t*v_2(t)>=t>v_2(t!).

The original beta construction with y=F(2v+1)^2, odd B, parity choices
for the nine CRT representatives, even semantic anchor, and even x
therefore works exactly as before. The constructed q is an odd square
and hence has the required affine representation.

## Removing the repeated frame atom

The first power base is now exactly the already-present index t.
The original square frame includes both the square of that index and
the square of the separately named first base. After identifying the
base with t, the latter square can be removed from the frame definition.
The former remains, so the frame still strictly bounds every actual
base, exponent, and output atom. Its constant lower bound W>=258 is
unchanged. The canonical frame is simply reconstructed at the resulting
smaller value of W, so no pointwise preservation of the old frame witness
is asserted.

The literal deduplication removes exactly `-d^2` from the frame residual
before the original projection, with d=t0+16=t. The original t^2 index
atom is retained. This changes coefficients but neither the number of
variables nor the number of rows.

## Concrete equations and checks

The conservative and deduplicated variants have the same headline
metrics, although their literal coefficients differ:

| Profile | Variables over Z | Rows | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| Principal | 240 | 176 | 4 | 5020 | 7968 |
| Dense | 239 | 175 | 4 | 12746 | 7968 |

The (t+1)^t controls have 5018 and 12745 terms at the same other metrics.
They remain available and should not be described as dominated by this
optional refinement.

Rebuild and check:

    python3 -B linear_growth_base.py --base-t
    python3 -B linear_growth_base.py --base-t --dedup-frame
    python3 -B affine_radix.py
    python3 -B check_reduced_front.py --mode t_growth_dedup

The complete source and certificates are in `t_growth_source/` and
`t_growth_dedup_source/`; the final equations are in
`t_growth_front_{principal,companion}/` and
`t_growth_dedup_front_{principal,companion}/`.

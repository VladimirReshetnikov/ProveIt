# Exact verification of the compacted-path positive kernel

## Results

The proposed four-state kernel is exact, including for off-diagonal path prefixes. It reduces immediately to three states. Grouping horizontal runs gives an exact scalar positive renewal kernel, but that scalar kernel is nonlocal and not reversible by diagonal conjugation. The natural finite-state step operators cannot be jointly made self-adjoint. These observations do not prove the existence or value of the asymptotic amplitude.

Verification code: `verify_positive_kernel.py`; captured results: `verify_positive_kernel_results.json`.

- All 5,151 cells `0 <= m <= n <= 100` agree among the signed recurrence and the three-/four-state kernels
- Every diagonal through 100 agrees with the independently implemented scalar renewal kernel; all V-ending entries agree as well
- Direct, nonmemoized enumeration of 709,506 accepted labelled path prefixes with at most seven H steps agrees state by state with the four-state kernel; 13,317 attempted V moves were rejected
- Diagonal counts for n=0,...,12 are 1, 1, 3, 15, 111, 1119, 14487, 230943, 4395855, 97608831, 2482988079, 71321533887, 2286179073663

## Definition and exact recurrence

The source is Elvey Price–Fang–Wallner, [Proposition 2.11 and Definition 2.12](https://arxiv.org/pdf/1908.11181), pp. 8–9. H steps at ordinate m have labels 1,...,m+1; paths stay at `0 <= m <= n`. H-decorated paths prohibit an HHV whose last two H labels coincide and exceed 1. Their counts agree with compacted-tree counts through the source's recurrence.

Let `F(n,m)=(Z,A,B,C)^T`, where the four states are exactly those in the proposal. The H matrix has rows

    H4_m = [[0,0,0,0],
            [1,1,1,1],
            [m,m,m-1,m-1],
            [0,0,1,1]],

and the V matrix has first row `(1,1,1,0)` and all other rows zero. Hence

    F(n,m) = H4_m F(n-1,m) + V4 F(n,m-1),
    F(0,0) = (1,0,0,0)^T,

with invalid cells zero. The entries `m-1` at m=0 multiply unreachable B,C states. For a globally entrywise-nonnegative matrix on every formal state, replace them by `max(m-1,0)`; the reachable evolution is unchanged.

The proof of the H transitions only inspects the new trailing pair. An old C prefix remains valid until V occurs; a subsequent H may replace its forbidden pair. Thus no prefix is discarded prematurely.

Writing `c=Z+A+B+C`, exact identities are

    A(n,m) = c(n-1,m),
    B(n,m)+C(n,m) = m c(n-1,m),
    C(n,m) = m c(n-2,m),
    Z(n,m) = c(n,m-1) - (m-1)c(n-2,m-1),   m>=1.

Adding gives

    c(n,m) = c(n,m-1)+(m+1)c(n-1,m)-(m-1)c(n-2,m-1).

Together with c(n,0)=1 and invalid cells zero, this proves exact equality with the specified signed recurrence. At n=m>0 no path can end H, so only Z survives and c(n,n)=Z(n,n).

## Three-state reduction and its scope

Z and A have identical outgoing transitions. Merge them to `E=Z+A`. With states `(E,B,C)` the exact matrices are

    H_m = [[1,1,1],
           [m,m-1,m-1],
           [0,1,1]],
    V   = [[1,1,0],
           [0,0,0],
           [0,0,0]].

The initial vector is e=(1,0,0)^T and output row is t=(1,1,1). Again use the restricted reachable subspace at m=0, or replace m-1 by max(m-1,0).

For a fixed m>0, this local weighted H/V representation has linear dimension three: the reachability columns `(e,H_m e,H_m^2 e)` have determinant m^2, and the observable rows `(t,tV,tVH_m)` have determinant -1. Their 3x3 Hankel product therefore has determinant -m^2. This rules out a two-state constant-at-that-altitude linear realization of the same suffix-counting problem. It does not rule out other encodings with additional coordinate dependence or nonlocal steps.

For the factorial-normalized vectors `f_N(j)=F3((N+j)/2,(N-j)/2)/((N+j)/2)!`, the positive nearest-neighbor kernel is

    f_N(j) = (2/(N+j)) H_((N-j)/2) f_(N-1)(j-1)
             + V f_(N-1)(j+1),

on valid parity/support. Summing the states instead yields the exact signed delay coefficient

    d_N(j) = ((N-j+2)/(N+j)) d_(N-1)(j-1) + d_(N-1)(j+1)
             - [2(N-j-2)/((N+j)(N+j-2))] d_(N-3)(j-1),

with the delayed term present only on valid shifted support. This independently confirms the pre-conjugation coefficient in the compacted perturbation argument.

## Exact scalar positive renewal kernel

Complete a horizontal run by a V. At altitude m its admissible decoration weight is

    w_m(0)=1,
    w_m(1)=m+1,
    w_m(k)=(m^2+m+1)(m+1)^(k-2),  k>=2.

For k>=2, among all (m+1)^k labelings, precisely m(m+1)^(k-2) have a forbidden final equal-non1 pair. Earlier pairs impose no restrictions because they are not followed by V.

Let a(n,m) count paths whose last step is V, and set a(0,0)=1. Then

    a(n,m+1) = sum_{k=0}^{n-m} w_m(k) a(n-k,m),  n>=m+1,
    a(n,n) = c(n,n).

This gives a genuinely scalar, entrywise-positive representation with no cancellation. Recover arbitrary prefixes by

    c(n,m) = sum_{k=0}^{n-m} (m+1)^k a(n-k,m),

where for m=0 only a(0,0) is nonzero. Its generating function for a completed run is

    W_m(z) = (1-m z^2)/(1-(m+1)z).

At the vertical-step clock, if h=n-m is the current distance from the diagonal, k H steps followed by V change h to h'=h+k-1. The kernel therefore allows a down-jump of at most one and arbitrarily large up-jumps. For b_m(h)=a(m+h,m)/(m+h)!, its entry from h to h'=h+k-1 is

    w_m(k) (m+h)!/(m+h+k)!,  k>=0, h'>=0.

This is a useful positive scalar alternative, but it has not converted the problem into a Jacobi/symmetric Airy operator.

## Symmetry obstructions

1. **Local H operator.** For m>0, rank(H_m)=2 and

       H_m^2 = (m+1,m^2,m)^T (1,1,1).

   Its characteristic polynomial is lambda^2(lambda-m-1), and its zero eigenspace has dimension one. Thus H_m has a nontrivial zero Jordan block. It cannot be similar to a real symmetric matrix, even by a general invertible similarity. In particular, no positive-definite common metric can make both H_m and V self-adjoint.

2. **Natural joint height/state transfer.** Its support has directed edges without reverse edges: for example B_h -> E_(h+1) has positive H coefficient, while E_(h+1) -> B_h has zero V coefficient. Positive diagonal conjugation cannot repair this. The scalar renewal kernel has the same obstruction through its jump +2 versus forbidden jump -2.

3. **Even general similarity can fail for a frozen finite-height transfer.** Freeze m=1, give H coefficient 1/2 and V coefficient 1, and truncate heights to 0,1,2,3. The resulting 12x12 nonnegative nearest-neighbor matrix has characteristic polynomial

       lambda^6 (4 lambda^6 - 12 lambda^4 + 6 lambda^2 - 1)/4.

   The cubic in u=lambda^2 has discriminant -432, giving nonreal eigenvalues; approximate examples are 0.5519686595 +/- 0.1284520399 i. This is an exact obstruction for that frozen model, not a claim that every actual time-dependent compacted kernel has nonreal spectrum.

4. **Completed-run weights are not moments of a self-adjoint H evolution with the same entrance/exit vector.** Their first Hankel minor is

       w_m(0)w_m(2)-w_m(1)^2 = -m < 0.

   Such a minor would be nonnegative for `w(k)=<v,S^k v>` with S self-adjoint. A direct symmetric moment realization is therefore impossible for m>0.

These obstructions delimit the elementary reductions only. They do not exclude a dilation, a nonlocal spectral parameter reduction, or an asymptotic effective scalar/self-adjoint model. Uniform control of the associated transformations and error terms would still be needed for any amplitude proof.

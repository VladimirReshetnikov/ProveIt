# Pooled low digits in the aligned cofinal natural compiler

The natural endpoints retain the cofinal-anchor arithmetic in
`upstream/round17/architecture/proofs/ONE_ROW_SEMANTIC_ANCHOR_PROOF.md`.
Their one-row semantic Pell anchor and their K=x amplification are inherited.
The low-digit pooling mechanism is credited to the separate incoming
`conzfc_graph_digits_2026-10-24.zip` proof, retained as
`proofs/POOLED_LOW_DIGITS_PREDECESSOR.md`. The new result is their compatible
composition with the self-sized radix and the exact emitted quartics.

All variables in this component range over N={0,1,2,...}. The principal
equation has 222 variables and 172 quadratic residuals; its sum of squares
is degree four with 9,522 terms and height 83,954,186. The two companions
have (variables,rows,terms,height) equal to (221,171,10216,2445412949744) and
(223,173,6858,83953724). The first trades much greater height for one fewer
variable. The second trades one extra variable for smaller support.

## The retained semantic data

The source has t>=12, F=t! after its factorial bootstrap, K=x,
N=B^K, H=1+sum(nine positive CRT representatives), and q=(NH)^K.
Its endpoints give x>=2+(t+1)y and x>2^32. The exact denominator groups are
q^t for the factorial binomial and row index, q^(t+1) for a,b,c,d,J,
q^(y+1) for S,Sp, and q^x for u,vq. The derived label satisfies J<=H^ell,
ell=2^22, and ell(t+1)<K. These facts and the canonical finite-refutation
witness construction are inherited from the complete source proof.

## Pool eleven low-remainder bounds into four

For each denominator D=q^k, replace the separate natural bounds

    D=r_i+s_i+1

by one row

    D=sum_i r_i+s+1.                                       (1)

Soundness is immediate: every old slack is restored by the nonnegative
polynomial s_i=s+sum_(j!=i)r_j. All numerator and quotient rows are unchanged.

For completeness use the source's canonical witnesses. Every ordinary
representative is less than H. For 0<=j<k<=K,

    binom(n,j)<=max(1,n)^j<=H^(K-1).

For J and j<=t, the bound ell*t<K gives

    binom(J,j)<=H^(ell*t)<=H^(K-1).

For the factorial upper index F^2+t, the endpoint bounds give
F^2+t<x^2+x<2^x<=N. Therefore its low coefficients are at most N^(K-1).
Put U=NH. Every low coefficient in every group is at most U^(K-1).
Each group has at most five members and U>=40. Consequently

    sum_i binom(n_i,j) <=5U^(K-1)<U^K=q,

so the integer sum is at most q-1. The sum of the canonical remainders obeys

    sum_i r_i <=(q-1)*sum_(j=0)^(k-1)q^j =D-1.

This supplies the new nonnegative shared slack in (1). The remainder values
are the exact canonical low residues furnished by the retained Pell/modular
compiler. No unproved ability to enlarge q independently is assumed.

This completeness argument deliberately starts with the inherited canonical
finite-refutation witnesses. Soundness uses only the direct polynomial
restoration of the removed slacks. There is no circular dependence on the
factorial identity in the soundness direction of pooling.

## The exact-binomial output bound is derived

The old output slack row q=B+o+1 is also removed. This requires a separate
soundness argument. The retained one-row Pell anchor first recovers all six
exact powers, independently of any modular digit bounds. In particular
V=(F^2+1)^t, N=B^K and q=(NH)^K are already known. The two raw factorial
ceiling rows give B>=1 and BF=V+s with s>=0. Thus F>=1, B>F and B>=2.
The endpoint supplies K=x>=F+1>=2. Therefore

    q=(NH)^K >=N^2 >=B^4 >B.

The removed natural slack can be restored as o=q-B-1. This precedes the
interpretation B=binom(F^2+t,t), so the reasoning is not circular.

## Exact contraction and final theorem

The normalized source has 334 natural variables and 284 quadratic rows.
Deleting seven redundant remainder slacks and the output slack gives 326
variables and 276 rows. The selected exact nonnegative contractors produce
the three endpoints listed above. Every monic substitution is certified by
an explicit rational sum of squares plus a polynomial with nonnegative
coefficients. The independent checker expands those identities and every
final coefficient; all substituted residuals remain quadratic.

The source's C222/ZF/ZFC calibration then proves in ZFC that each supplied
natural-domain polynomial has no zero if and only if Con(ZFC). The new
component supplies ordinary unbounded proofs and finite exact algebra; it
does not claim a new end-to-end proof-assistant or encoded object-ZFC proof.

The separately tested weighted pooling of q^t and q^(t+1) is not selected:
although it removes one raw slack, its quadratic bound prevents two affine
denominator eliminations. The three delivered natural profiles use only the
four unweighted groups, whose full raw mutations are checked independently.

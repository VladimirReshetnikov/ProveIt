# Proof audit

The proofs are self-contained ordinary mathematics. This document is a review
checklist, not a second claim of formal verification.

## Main inequality

Let n=|L|, m=|Jr(L)|, q the number of distinct principal Ji labels, and let a
selected fan of k upper covers have r distinct labels.

1. Every cover x<y has a representative j minimal in down(y) minus down(x).
   Such j is nonzero and join-irreducible. Transposition gives
   con(x,y)=con(j_*,j). For covers of a common u, the j's are distinct because
   a=j join u.
2. Congruences are determined by their collapsed edges, hence by their subsets
   of distinct labels. Thus |Con L| <= 2^q.
3. The k representatives use only r labels; remaining Ji elements contribute
   at most one label each. Thus q <= n-1-m-k+r.
4. Distinct fan covers meet in u. All pairwise joins are join-reducible.
5. Equal joins of incident pairs force equality of the two noncommon labels
   and inclusion into the common label. Equal joins of disjoint pairs force
   equality of all four labels. No upper interval is assumed to be a cover.
6. For r=1 at least one join-reducible exists. For r=2, k>=3 yields two covers
   with the same label and one with the other; two joins must differ. For r>=3,
   one representative per label yields choose(r,2) distinct joins. Thus m>=r.
7. Consequently q<=n-1-k and |Con L|<=2^(n-1-k).

## Classical ideal representation

The join of two congruences is the equivalence closure of their union. A walk
witnessing collapse of a prime interval can be clamped to that interval by
z -> (z join x) meet y. A changing step proves that an edge label is join-prime.
Finite joins of labels realize precisely the order ideals of the label poset.
This gives |Con L|=I(Q) without importing a representation theorem as a black box.

## Equality

- Equality in the exponent chain forces m=r, q=n-k-1 and all 2^q signatures.
- All signatures implies that Q is an antichain.
- If r=2, the three joins from two same-label covers and one other cover are
  all distinct under the antichain condition, giving m>r.
- If r>=3, the join of all selected distinct-label covers is an additional
  join-reducible, beyond the choose(r,2) pairwise joins. It cannot equal a
  pairwise join, because a third label would then be below the first two.
- Hence m=r=1. The common label alpha collapses the k+2 diamond vertices.
- Exactly half of the Boolean signatures contain alpha. The quotient
  correspondence and the general bound give |L/alpha| >= n-k-1. The known
  k+2-element block gives the opposite inequality. Thus it is the only
  nonsingleton block, and it has no additional elements.
- Convexity gives an actual M_k interval, not just an M_k sublattice.
- Uniqueness of the join-reducible element v makes every x comparable with v.
  For x<=v outside the diamond, meet with x in u alpha v forces x<=u.
  Both exterior intervals must be chains.
- The converse uses simplicity of M_k and the product rule for glued sums.

## Sharp nonextremal gap

Set N=n-k-1. If q<N, the count is at most 2^(N-1). If q=N but the maximum is
not attained, Q has a comparable pair, excluding at least one quarter of all
subsets from being ideals. Thus the count is at most 3*2^(N-2).
A one-edge subdivision T_k of M_k has a two-element chain of principal labels
and exactly three congruences. Exterior chains realize the bound at every
n>=k+3. This does NOT classify all second-level extremizers.

## Skeleton

Density>=p implies |Jr|,|Mr|<=floor(log2(1/p)) by the classical count and duality.
The proved cover theorem bounds every degree >=3 by the same floor. Degrees
<=2 need a separate maximum with 2. Counting reducibles and adjacent covers
with multiplicity gives 2*t*(max(2,t)+1). No disjointness of these sets is assumed.
No bound on the number of exterior-chain or subdividing elements is asserted.

## Executable evidence

See data/verification_summary.json. The code enumerates natural orders from
scratch, computes their meet/join tables, and verifies every selected fan.
An independent all-partition algorithm confirms the whole congruence set for
all natural lattices with <=7 elements. The equality recognizer checks the
order structure independently of the numerical count. There is no randomized
sampling in the exhaustive verification.

The supplied run uses Python assertions, so run without -O. Larger structured
checks are explicitly distinguished from exhaustive tests. The uncompleted
n=9 run is not included in the reported finite scope.

# Independent review of the quotient-radius refinement

This strengthens the squared-output construction reviewed in `REVIEW.md`.
The source body and its66 retained predicates are the same; row1176 now is

    W = 5 + sum(the34 unsigned power atoms) + sum(the9 omitted quotients squared).

The nine terminal outputs are omitted from the radius. This change preserves
ordinary degree four after summing quadratic residual squares and allows the
terminal output coordinates to be eliminated by their original monic rows.
The resulting coefficient and variable census is supplied separately.

## Magnitude bounds before any selected power interpretation

The unchanged filtered prefix proves every one of the34 unsigned atoms
nonnegative. It also proves M=raw129>=1, N=raw93>=2 and raw113>=0.
Original gates506..508 give the exact polynomial identity

    b=raw530=M*(1+N+raw113),

so1<=M<=b<W. Each omitted quotient q obeys |q|<W, because q² is a
nonnegative summand of W−5. Every actual base and exponent belongs to the
34 unsigned atoms, so n,k<=W−5. Their positive lower bounds remain
unchanged. All selected bases equal b+1>=2, which in particular implies
W>=7.

For the eight range blocks,

    m=M*L*q+r, L=r+s+1, r,s>=0,

where L is an unsigned power atom. Thus M,L,|q|<W and0<=r<L<W, giving

    |m| <= M*L*|q|+r < W³+W < W⁴.

For the extra exact-binomial block,

    m=L*(C+b*q)+r, L=r+s+1, b=C+z+1,

where C,r,s,z>=0, and L,b are unsigned power atoms. Hence0<=C<b<W,
0<=r<L<W and |q|<W, giving

    |m| <= L*(C+b*|q|)+r < W³+W²+W < W⁴.

The exact source-row identities, strict-positive divisor premises and all
nineteen division/remainder cuts were checked independently. No omitted
quotient sign or selected power meaning enters these bounds.

## Exponent slack replaces a direct output bound

The unchanged Pell bootstrap still proves A>W^W, and each selected modulus
T=2An−n²−1 satisfies T>=A. From k<=W−5 and |m|<W⁴,

    |m*n^k+1| <= (W⁴−1)*W^(W−5)+1
                <= W^(W−1) < W^W < T.

The product is nonzero because n>=2. The negative-X branch is excluded
exactly as in the signed-output lemma. For the positive branch,

    |m−n^k| < W⁴+W^(W−5) <= 2*W^(W−1) < W^W < T.

Here W>=7, so every displayed exponent comparison and the final strict
inequality is valid. Hence every selected output is exactly n^k>0.
The same source division identities then recover all nine omitted quotient
signs. No extra unknown or extra source constraint is required.

## The old proof must be reused selectively

It would be incorrect to state that all43 power atoms are less than the new
W, or that the new W is at least the old linear radius. Neither claim is
needed or proved.

The selected nine power calls have already been certified by the new lemma.
The other twelve calls retain their direct output bound m<W from the radius.
In particular the old local factorial and missing-index bootstrap uses only
calls1,5,6,0,9, all of which belong to those twelve. Their signs, magnitude
bounds, bootstrap hypotheses and original rows are unchanged. Once the nine
quotient signs are recovered, all original prefix sign premises are available.
The inherited argument may therefore be replayed for the twelve remaining
calls while the selected nine are supplied as already proved facts. This
establishes all21 power meanings without ever invoking a false global
magnitude claim.

After the powers have been interpreted, the factorial/binomial/CRT/logical
source proof no longer uses a bound m<W on a terminal selected output. The
ordinary C222 calibration proceeds unchanged.

## Ordered completeness

For either direction requiring a literal source tuple, retain the genuine
semantic prefix and compute its intended frame from those fixed coordinates.
The omitted quotients are Euclidean witnesses determined by genuine powers;
they are independent of all private Pell coordinates. Therefore calculating
W from their squares introduces no fixed-point problem.

Choose the bootstrap at this W, then the main Pell index pairs, common unit,
comparison parameters and private power quotients by the retained finite-period
construction. For the new quotient frame every base and exponent is less than
W, so its genuine n^k is less than W^W<A<=T even if it is not less than W.
This is all the power congruence construction needs. All required quotient
signs and old nonnegative source data have genuine values. Supply fresh
three-square witnesses for the66 predicates.

For reconstruction of the original75-predicate tuple use its original linear
frame instead. This restores the original exact row1176. No pointwise
identification of the private frames or Pell values is claimed.

## Verification receipt

`peer_check.py` accepts either of the two exact proposed frames and records
which one it has checked. The quotient packet passed normal and optimized
runs in `QUOTIENT_PEER_REVIEW.json` and `QUOTIENT_PEER_REVIEW_OPTIMIZED.json`.
They certify all575 literal prefix-row identities,118 complete original-row
ideals,605 independently derived prefix signs, the selected seeds, all19
range/digit cuts, the original source binding and the seven immediate
calibration file hashes. An additional1200 signed-output diagnostics test
the quotient-radius inequalities, while the unbounded proof is above.

# Independent semantic review: signed affine front and a guard-free horizon

Reviewer: pell_route, a separate AI-assisted research agent in this task.
Date: 25 October 2026.

## Verdict and exact scope

The signed-affine change in incoming_agent/new_affine/PROOF.md is sound at
the stated inherited signed-Pell and C222/refutation interfaces. I found no
remaining semantic gap in replacing q=(2z+1)^2 by q=4z+1 and the beta
multiplier (2v+1)^2 by 2v+1.

The further proposed horizon change is also sound at the same interfaces:
delete the private row t=16+h0^2, retain t as an unrestricted integer
coordinate, and replace the initial power base by
p0=2^26(2t+1), with its existing certified output F=p0^t. A complete proof
must make the new large base an actual square-frame atom, retain its exact
power request, and use the modified estimates below rather than silently
reuse every statement of the old t>=16 proof.

This verdict covers ordinary unbounded mathematics, not every coefficient,
the complete transformation lineage, or a newly compiled Lean/Rocq theorem.
The separate exact compiler and independent finite checks must bind the
final emitted objects. I did not author the reviewed signed-affine source
proof or either source transformation.

## Sources actually inspected

- incoming_agent/new_affine/PROOF.md and build_affine.py.
- Factorial_Free_Binomial_CRT incoming package:
  review/FACTORIAL_FREE_BINOMIAL_CRT.md;
  review/FACTORIAL_FREE_AUDIT.md;
  review/INDEPENDENT_REVIEW.md;
  direct/audit_power_interface.py, in full.
- Its retained parent proofs:
  proofs/NORMALIZED_REMAINDERS_PROOF.md;
  upstream/round17/direct/ORIENTATION_FIRST_PROOF.md;
  upstream/round17/direct/PROOF_315.md;
  the local-interface and majorant sections of
  upstream/round17/architecture/proofs/inherited/direct_arithmetic.tex;
  INHERITED_DERIVED_LABEL_RANGE_PROOF.md and the relevant semantic-anchor
  bounds.
- direct_agent/build_projection.py and the principal_D restoration
  certificate, for the nature of the additional algebraic projection.

The predecessor has historical obsolete factorial/signed-sign claims in
some inherited notes. Those are not interchangeable with the new proof:
the active argument uses the factorial-free CRT and the new signed digit
bootstrap, followed by the inherited local-calculus interface.

## 1. Uniform signed-power interpretation

The square frame bounds every actual base, index, and output in absolute
value. Canonical signed Pell coordinates give, for T=2An-n^2-1,
the output m congruent to n^k modulo T for k>=0, and mn^(-k) congruent
to 1 for k<0. Since T=-1 modulo n, the inverse congruence is legitimate.
For |n|>=2 the strict frame magnitude bound forces equality and excludes
negative k. This uses absolute values, and therefore remains valid for
negative n and negative A.

The power bound for a negative index is not an unbounded-exponent
assumption: the index is itself a frame atom. All actual atoms are
integers of absolute value at most W-1, so
|m n^j| <= (W-1)^(j+1) <= (W-1)^W < W^W for 1<=j<W.
The retained |T|>W^W+W is therefore sufficient.

Neither the signed anchor nor the pooled coordinate-orientation proof
uses the radix-square or beta-square rows. The proofs use their atoms
only through the complete square frame. The new initial base has
|p0|>=2^26 at every integer t; hence W>p0^2>=2^52. This replaces the
old use of t>=16 to obtain W>=258, and more than suffices for all
pair-count and |A-1|>4W^3 comparisons.

## 2. Why the affine radix and multiplier are admissible

The affine residue q=4z+1 excludes q=-2,-1,0. The only unit value is
q=1, and every other possible q has |q|>=3 and |q+1|>=2. Thus the
requests at q+1 force the actual CRT representatives to be nonnegative
regardless of the initial sign of q. Consequently H=2+sum representatives
is at least two. The raw index row
B h_B=C0+F^2+1 excludes B=0.

When q=1, the self-radix power request forces x=0. If t>=1 and
|y|>=F>1, the last beta endpoint would say that
1+(t+1)y divides -1, whereas its absolute value is greater than one.
This excludes q=1 without using positivity of y.

For |q|>=3 the denominator power request at exponent y+1 forces
y>=-1. Since y=F(2v+1), F>1, and |y|>=F, it follows that y>=F>0.
This is the necessary sign recovery; treating the new multiplier as
positive immediately would be incorrect.

The denominator ratio q^(t+1) v=q^x implies x>=t+1 even when q<0:
otherwise |v| would lie strictly between zero and one. With t>=1,
the first and last beta endpoints now give
x>=F+1 and x>=2+(t+1)y.

## 3. Signed normalization and the negative-radix binomial digit

The common norm
M^2=1+4 sum rho_i^2+a^2+b^2+c(c+1)
forces M nonzero, because its right side is at least one. It also gives
|rho_i|<|M|/2. If D v=M and v U=M Q+rho, then D and v are nonzero,
v divides rho, and r=rho/v is an integer satisfying U=DQ+r and
|r|<|D|/2. No sign of either denominator is needed.

For a negative proposed radix q, the correct low expression is the signed
polynomial
r0=sum_(j<t) binom(F^2+t,j) q^j.
It need not be a nonnegative ordinary remainder. The coefficient bound
and Q=|q|>=2^x give |r0|<Q^t/32. The normalized digit gives an integral
r congruent to r0 modulo q^t, with |r|<Q^t/2. Their difference is a
multiple of q^t of magnitude below Q^t, so r=r0. Only after this step
may the digit quotient be reduced modulo q.

The output B and the positive binomial C=binom(F^2+t,t) satisfy
B=C modulo q, |B|<Q/2 and 0<C<Q/32. Therefore B=C>0. Then
q=(BH)^x>0. This argument excludes the negative-radix branch without
presuming a positive-radix expansion. The remaining range digits are
subsequently interpreted with positive radix as in the predecessor.

## 4. The guard-free horizon and all small cases

Set p0=2^26(2t+1). It is nonzero with absolute value at least 2^26
for every integer t. Its signed power request therefore forces t>=0
and F=p0^t. If t=0, then F=1 and y is odd. The two beta endpoints are
x=2+(y+1)u0 and x=1+(y+1)ut.
Subtracting them gives (y+1)(ut-u0)=1. The left side is even because
y is odd. Thus t=0 is impossible, without needing a sign for x,y,q.

Every full zero consequently has
t>=1,
p0>=3*2^26,
F>=3*2^26,
F>(t+1)^t>t!,
v2(F)>=26t.

After the signed-affine bootstrap this gives
y>=F,
x>=2+(t+1)y>=2+2F>2^28.

The case t=1 must not be excluded by the old index-representative
argument: B=F^2+1, so C0=0 is compatible with the raw index congruence.
This is harmless. All ordinary binomial upper arguments may equal zero,
and H=2+sum representatives is still at least two. In particular
max(1,n)+1<=H remains true without C0>=1.

The local majorant can no longer be cited as less than 2x before the
late exclusion of y=F. Use instead Rmaj=2+t+x+y+F<3x:
2x-(2+t+y+F)>=2+t(2F-1)>0.

For E=2^23 and x>=2^28, choose n>=28 with 2^n<=x<2^(n+1).
Then
E log2(3x)<E(n+3)<2^n<=x.
The middle inequality holds at n=28 because 31*2^23<2^28,
and persists by induction. Hence (3x)^E<2^x.

The derived-label exponent ell=2^22 also remains covered:
x>=2+(t+1)F>ell(t+1), since F>=3*2^26>ell.
All denominator indices t,t+1,y+1,x are positive and at most x.
The binomial coefficient bound
(F^2+t)^t <= (F^2+F)^t <= 2^(t(F-1))
is valid because t<=F and F>=7. These inequalities recover every
quantitative hypothesis used by the active digit and CRT arguments.

## 5. CRT and label decoding need only t>=1

The generalized binomial CRT theorem itself is valid for t>=1.
Its radius condition holds because F>t! and R=F^2.
Every row has a full prime-power separator exceeding t, and every
prime power in B has a compatible row for completeness. The
precision-2x construction loses fewer than x factors of each prime
when dividing by any range factorial, since each lower index is <=x.
No factorial authenticity is reintroduced.

The literal local majorant and positive-constructor ledger require
nonnegative bounded local data and a bounding base at least two;
they do not require the obsolete cutoff t>=16. The new bound
Rmaj^E<2^x therefore suffices. The changed proof continues to handle
zero upper representatives using max(1,a), not an invalid 0^k bound.

The late y=F boundary argument remains valid when t=1: the first
beta remainder is zero, the last is one, and the positive Horn weights
propagate zero forward. Thus y>F after all rows have been decoded.
The product-polynomial multiplicity argument uses only
F>(t+1)^t and t>=1, both now established. It yields the same finite
C222 refutation and the same inherited syntactic ZFC calibration.

## 6. Completeness

Completeness may still choose an arbitrarily large horizon t>=16
dominating the finite proof and its labels; the new source merely
permits more horizons. For the changed growth law, v2(F)>=26t exceeds
v2(t!), so a positive odd multiplier can make y an even multiple of t!
and as large as required. The beta CRT moduli are odd, allowing an even
code x. Since v2(F^2)>log2(t), the binomial B is odd. The arithmetic CRT
moduli are then odd, allowing the same representative parities,
dominant representative, and even semantic anchor.

Choose x even and H odd exactly as in the predecessor. Then q=(BH)^x
is an odd square and is 1 modulo 8, hence it satisfies q=4z+1 for an
integer z. The new beta multiplier has the form 2v+1 by construction.
All old private Pell and normalized-remainder witnesses are constructed
fresh at the resulting semantic values. Every active hypothesis of the
inherited simultaneous-power and anchor completeness constructions is
therefore retained.

No claim is needed that a new zero lifts to the old square-constrained
or cofinal-horizon source. The semantic changes preserve existence via
the proved refutation interpretation. The later affine and monic
coordinate eliminations preserve zero sets by integral inverse maps.

## Remaining binding requirements

Before claiming any final numerical endpoint, independently verify:

1. The exact new base is the atom in the initial power request, square
   frame, base modulus, and all restored final residuals.
2. The horizon root is absent from every remaining residual after its
   sole row is deleted; no unconstrained variable is advertised.
3. The two affine row changes commute correctly with the inherited
   factorization, monic projections, translations, and residual changes.
4. Any additional quadratic-preserving projection has exact reversible
   residual operations and an explicit integral restoration map.
5. The final quartic is recollected from the actual complete residual
   list, with exact degree, support, height, and liveness.

These are finite artifact obligations, separate from this semantic review.


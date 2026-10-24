# Shared taps after positive-gap substitution

## Status and coherent source

This is a supporting composition, not a new universal-polynomial theorem and
not an optimality claim. The primary source is gapN86. It combines the exact
source65 target vector with round9's positive-gap coordinate bijection.
All 31 source coordinates are strictly positive integers. The four fixed
ports are inherited **together**, in order beta,K0,MC,MF, from the original31
wang943-mixed-121x8801 tuple. The supplied gzipped files are unsigned
little-endian integers, not symbolic coefficient recipes. K0 uses K.bin.gz;
MF uses MF_source.bin.gz. Their raw and compressed hashes are in the binding
file. This does not rebind the smaller coefficient tuple from another source.
The underlying source-to-Con(ZFC) theorem is the inherited mathematical
calibration theorem, not a new Lean/Rocq certificate.

First apply the invertible row operations rho14=r14+r2 and rho15=r15+r3 to
the pinned original source. With q=1+beta J, k=eta+zeta and Y=a-E, the original
positive roots satisfy Y=sN>0, E=XY>0, c-eta=kY>0, P-k=E(c-eta)>0.
Thus old P=new P+eta+zeta is a bijection of positive zero sets. Rows1,2 give
old N=q^3>=8, so old N=new N+1 is another positive-zero-set bijection.
These are exactly the substitutions in gapN86_source.json. Ports do not
change. The variable spelled P in that JSON is the new gap coordinate.

## Exact shared-tap lemma

Write each transformed residual as a sum of coefficient polynomials in the
four ports times monomials in the 31 variables. Let w be the 31 distinct
positive weights and q_j the 22 distinct target positions. A term a x^alpha
of degree d requires a kernel record at e=q_j-alpha dot w. Its coefficient
is 2a unless it is a quadratic cross term, in which case it is a. At a shared
position in the same degree layer, keep one record, NOT a sum, only if the
complete coefficient polynomials agree. Equality of one numeric evaluation
or equality of just a scalar part is insufficient.

The certificate's real obligation is the full polynomial identity

[T^q_j](D2(T) U(T,x)^2+D1(T) U(T,x)+D0(T)) = 2 rho_j(x),
U(T,x)=sum_i x_i T^w_i.

The independent serialized-artifact auditor enumerates all monomials of
U^0,U^1,U^2, including absent monomials, and compares all port coefficients.
Consequently this identity has no probabilistic or bounded-test assumption.
It checks 22 identities for each of five sources and rejects coefficient
mutations. The primary source has 86 records, 81 unique kernel positions,
W=116, Q=1841, and layer degrees (1384,1732,1641). Thus H=1873. Source65
had 89 records and 84 positions at the same H. GapNq85 fails this same
layout; its separately verified H1948 alternative must not be conflated
with the primary source.

## Positivity and sparse-carry bounds

Every actual kernel coefficient has absolute value <M=2^2134927, checked
against the materialized native tuple. The maximum observed bit length is
2134926. Let B>=4096 M b^2 for a positive integer b; U=sum_i B^w_i+g with
g positive. Leading D2 coefficient is +1; its degree is1641. Its negative
tail has magnitude at most M B^1641/(B-1), so D2(B)>B^1641/2.
The linear leading coefficient is +2, but positivity does not rely on it:
with U>=B^116, the entire possible negative D1 contribution, relative to
B^1641 U^2, is at most 2M/B^25. The D0 contribution is at most 2M/B^489.
Their sum is less than1/4, proving G=D2(B)U^2+D1(B)U+D0(B)>0 for every
positive b,g, before digit recovery.

On 0<g<4bB^116, U<6bB^116. Geometric bounds yield
2G/B^(H+1)<86 M b^2/(B-1)<1/32. Put ell=sum_i B^w_i,
N0=B^117, Z=B^1874, A_targets=sum_j B^q_j,
Mask=N0-1-(b-1)ell,
Scode=g+N0(2G+A_targets), Tcode=Mask+N0(B-2)A_targets.
Since H-Q=32, A_targets and (B-2)A_targets are each <Z/64.
Also g<N0 and 0<=Mask<N0, hence Scode+Tcode<N0 Z=B^1991.

For power-of-two b, the low mask recovers g=sum_i z_i B^w_i with
0<=z_i<b, hence source coordinates x_i=z_i+1 are positive. Each convolution
coefficient has absolute value <993 M b^2<B/4. The inherited signed-borrow
lemma then makes the binary disjointness test equivalent to all target
coefficients vanishing. Shared requirements do not add multiplicities to a
kernel coefficient; the same coefficient bound applies to the union of taps.
Conversely each positive source root fits for all sufficiently large b.
The all-one tuple is not a source root (row5 equals1), so canonical g>0.
Because every weight is positive, canonical g is divisible by B, and hence
by b^2. This stronger congruence is preserved, not merely b divisibility.

## Exact integer-finalizer interface

Use the inherited integer carrier b=6f+4, g=b g0, B=2^2134940 b^2.
The domain of f,g0 in the final equation is unrestricted integers; the
finalizer must recover positivity before invoking the preceding bounds.
Set Tminus=Tcode-2, Nblock=B^1991 and
X=Nblock(Scode+Tminus+1)-Scode-1,
Y=2^(16*2134940-23) b B^2114,
cap=bB^116.
These are ordinary integer polynomials. On the intended positive range,
Tminus clears an unused low bit, because the least source weight is1.
The identities X odd, X=0 modulo3, b divides X+1, and b divides Y hold in
the carrier. Canonical roots have b^2 dividing g. All unchanged central
binomial/Pell/finalizer implications are inherited from the corresponding
integer interface; this note changes only the source polynomial and checks
the bounds needed by that interface. Exact final degree and gate counts belong to the composed finalizer DAG, not
to this supporting kernel certificate.

# Independent mathematical review of the smaller coefficient tuple

The reviewer read the complete proposed `PROOF.md` and literal `build.py`,
compared the relevant source geometry and blank-rank arguments, and wrote
`audit_external_review.py` without importing either supplied construction
script. The new tuple has a complete argument for the claimed native/Pell
interface transfer. No gap was found in the changes reviewed below.

This is an ordinary mathematical review plus finite exact checks. It is not
a proof-assistant certificate of the inherited compiler or machine endpoint.

## Geometry and payloads

The independent audit reads the four compressed delivered integers, verifies
their hashes, and recovers DC and DR by dividing K at the specified bit d.
It compares the recovered radix-2^125 digits with an independently assembled
literal recipe. Thus the support identities are checked against the actual
integer payload, not merely against the constructor's internal dictionary.

All 69,230 basis identities pass. In particular:

* The reflected bands cannot contaminate edge targets. The sole exceptional
  difference to inspect is 3341-2225=1116, absent from E-E.
* The cross-band difference is 1118, also absent from E-E.
* The anchor difference is 1114 and occurs only as 2225-1111.
* Length 8101 exceeds twice the native support span, excluding circular
  copies of these differences.
* Every product lies at exponent at most 6684, so the 860 added field
  tests at 6685 through 7544 are identically zero on intended words.

The carry bound uses exactly the same number and total mass of clause
coefficients as the source construction, plus four bare DC shifts, one DR
shift, and the temporal native term. The value 4*mass+8 is strictly below
2^125, including before the selector count is reduced to zero or one.
This establishes the needed separation between the global radix carry
argument and the later radix-4 clause decoder.

The independently rebuilt masks equal the delivered masks. Their populations
are 989 and d-989; their low congruences are unchanged. The exact ordered
tile list equals the pinned source list. The bundled JSON has one extra
final newline, so its byte hash differs; the parsed content is unchanged.
No tile-language change has been introduced by the coefficient optimization.

## Composite-modulus Boolean lemma

The important new obligation is that d is not a power of five. The proposed
proof handles it correctly.

Let N=5^n be sufficiently large, M=125*8101*N, and T=N/5. The elementary
5-adic calculation gives v5(B^4-1)=4, so B^4 has order T modulo 125*N.
Separately, B^4=1 modulo 8101. Chinese remaindering therefore shows that
B^4 has order T modulo M. Its powers all lie among the T residues
1+5*d*t modulo M, so they enumerate those residues exactly.

The fixed-cardinality subset construction only requires its cardinality k
to be invertible modulo T, which is a power of five. It does not require
d itself to be a power of five or k to be coprime to 8101. The optional
weight B makes the target a 5-unit; choosing k in the resulting class
modulo 5d then guarantees gcd(k,T)=1. The condition T>5d ensures that
the cyclic block of k selected indices has no repeats. This proves the
Boolean, rather than unrestricted-integer, subset assertion.

The no-wrap condition on physical cells is also sufficient: all selected
indices are at most 4N/5-4, and the chosen temporal width is less than N/5.
Both spatial and temporal destinations therefore remain below N. The
rank-difference identity applies simultaneously to the entire subset.

The audit exhaustively checks the subgroup identities for N=5 through
3125, and checks 106 target formulas at the first convenient actual-sized
choice N=5^11 satisfying T>5d. These checks support the implementation;
the uniform proof is the CRT and cyclic-cardinality argument above.

## Rank unit and completeness

Modulo both 5 and 8101, rho has square -1. Because L,N and the chosen
temporal width are all 1 modulo 4, B=q=B^width=rho in both rings. The
1118 separation makes reflected pairs cancel; the four bare shifts give
DC=1+3rho and DR=rho. Hence the actual switch factors are

    q^2-1=-2,
    1+q(DC+B DR+B^width)=-3.

They are units modulo both coprime components of dN. This is enough to tune
the actual packed rank to d*width modulo dN. No primality assertion about
8101 is used or needed. The exact payload residues reproduce these values.

The proof keeps canonical dummy adjustments inside the established free
native positions and proves that every added zero-field test remains zero.
The source positivity and carry estimates therefore survive the tuning.
All downstream polynomial constants must still be rebound as one complete
tuple; this coefficient result does not by itself alter a separate fixed
signed16 instance.

## Parity and interface checks

The proposed population calculation is algebraically consistent. With
S=(C-1)+qF and Tmask=(MC*J+1)+q*(MF_native*J-1), the shifted source port
indeed gives

    R=(q^2-S)(q^2-1)+Tmask
     =(q^2-1-S)q^2+(S+Tmask).

Canonical disjointness prevents low-block carries. Thus pc(R)=3dN+2.
The low congruences S=0 modulo 4 and Tmask=3 modulo 4 imply R=3 modulo 4.
Since dN is odd, R-dN is even, so the recovered scale 2^(R-dN) is a square.
The source valuation v2(Y)=pc(R)-2 gives the required odd s. The remaining
normalized-multiplier parity is the unchanged source Pell argument at an
even parameter and the same odd rank choice.

## Recommendation

The smaller tuple may be presented as a proved coefficient-height improvement
under the same explicitly stated inherited compiler and endpoint dependencies.
The four delivered payloads and their single binding should travel together.
No claim of global coefficient optimality, fresh formal verification, or
proof of Con(ZFC) is warranted.

# Complemented whole-label clauses: a smaller fixed compiler

## Statement and imported interface

The reviewed source is ProveIt commit
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`, package `36-small-tuple`.
Its native compiler has 943 selectors, 38 copied label bits, two dummy
positions, and three anchors. This supplement retains the tile language,
native support, transport geometry, and two tested anchors. It changes the
clause encoding, radix, padding, and explicit actual-rank controller.

The new base and radix are

    rho = 2^77, L = 8807, d = 77*8807 = 678139, B = rho^L.

All four coefficient ports together occupy 339,476 raw bytes, compared with
506,664 for package 36; the maximum port length is 681,374 bits, compared
with 1,016,946. These are native-port sizes, not the sizes of coefficients
after expanding an arbitrary final polynomial.

The new result is a local, exact compiler substitution. The imported
blank-Wang language theorem, native decoding and carry theorem, helical
padding theorem, Pell arithmetic, and K215 calibration remain dependencies.
Reference copies are in `source_proofs/`; their immutable digests and notices
are retained. No new end-to-end Lean or Rocq proof is claimed.

## 1. The local arithmetic idea

Let an l-bit source label x satisfy 0 <= x < 2^(l-1), and put

    code(x) = 2^l - 1 - x.

This is injective and its highest bit is one. Let v be the integer formed
by the l copied bits in a native cell. Use tile coefficient x+1 and copied
coefficient v in a field of width l+1. Test exactly its lowest l bits.

If no selector is occupied, the field contains v in [0,2^l-1], and its
tested bits vanish exactly when v=0. If exactly one selector is occupied,
the field is x+1+v. It lies strictly between 0 and 2^(l+1), so its tested
bits vanish exactly when x+1+v=2^l, equivalently v=code(x).

Thus an entire label uses l tested bits and one guard bit. The earlier
encoding required l separate two-bit fields. The four labels use
10+11+10+11=42 payload bits instead of 2*(9+10+9+10)=76. The three two-bit
anchor fields remain. Their placement before the label fields further
reduces the conservative pre-decoding carry bound because their tile
contribution is constant.

No carry-free premise is made before selector extraction: all non-selector
terms are divisible by 1024, while there are at most 943 selected tiles.
The bottom ten bits are their exact number n. The selector mask 1022 forces
n=0 or n=1. Only then is the preceding field argument applied. This order
excludes any circular assumption about one-hot selection.

## 2. Exact integer recipe

The ordered tile list is unchanged, with SHA-256
`66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f`.
The slot order is west, north, east, south. Define

| Slot | Native offset o | Width l | Clause bit offset p |
|---|---:|---:|---:|
| West | 1023 | 9 | 16 |
| North | 1013 | 10 | 47 |
| East | 1003 | 9 | 37 |
| South | 983 | 10 | 26 |

The physical clause field order is three anchors, west, south, east, north.
Use anchor native positions (1095,2195,3296) and their clause bit offsets
(10,12,14). The support is

    E = {0,...,942}
        union {o_s+j : 0<=j<l_s, s=west,north,east,south}
        union {1063,1064,1095,2195,3296}.

It has 986 members. For tile i with original labels x_(i,s), set

    c_i = 1 + sum_s (x_(i,s)+1) 2^p_s + 2^10+2^12+2^14.
    c_(o_s+j) = 2^(p_s+j).
    c_1095=2^10, c_2195=2^12, c_3296=2^14.
    c_1063=c_1064=0.

The clause mask is

    mu = 1022 + 2^10+2^12+2^14 + sum_s (2^l_s-1)2^p_s.

It has 57 bits and population 50. In the radix rho define

    Z = (2^75-1) sum_(e=8792)^8802 rho^e + (2^39-1)rho^8803,
    DC = rho^30+rho^62+rho^1100+rho^2201
         + sum_(e in E)c_e(rho^(4393-e)+rho^(5495-e)),
    DR = rho^42,
    MC = B-1-sum_(e in E\{1})rho^e-2rho^1063,
    MF_native = 4 + mu(rho^4393+rho^5495)
                +sum_(j=0)^9 rho^(1013+j)
                +sum_(j=0)^8 rho^(1065+j)
                +rho^2195+rho^3296+Z.

The fixed ports are exactly

    beta = B-1, K = DC+B DR, MC, MF_source = MF_native+B-1.

These are fixed finite integers. The fourth port is shifted; inserting
MF_native at a skeleton's MF port would define a different construction.
Every use must bind all four ports together.

## 3. Native matching and synchronization

The complete tested native coefficient identities are unchanged:

| Target | DC source | DR source | Temporal source |
|---|---|---|---|
| 1013+j (0<=j<10) | 983+j | none | 1013+j |
| 1065+j (0<=j<9) | 1003+j | 1023+j | none |
| 2195 | 1095 | none | 2195 |
| 3296 | 1095 | none | 3296 |

At each clause target T in {4393,5495}, the coefficient of rho^(T-e)
in DC is c_e for every e in E, with no spatial contribution. The auditor
checks all 66,062 scalar native-basis identities, including absent
contributions; linearity covers arbitrary native assignments.

All label encodings retain a highest occupied bit equal to one and are
injective. The old propagation argument therefore applies verbatim: an
occupied cell's matching high bit forces the adjacent cell occupied, and
the remaining matched bits recover equality of original edge labels.

The two clean-band and anchor intersections are

    ((4393-E) mod L) intersect ((5495-E) mod L) = empty,
    ((2195-E) mod L) intersect ((3296-E) mod L) = {0}.

The support has not changed. Since L>2*3296, the old difference argument
has no new circular cases: 1102 is absent from E-E; the tested-anchor
difference 1101 occurs only as 3296-2195. A marked Start supplies the
initial occupied selector, hence the source anchor, then both distinct
tested anchors. The source binary-rotation argument excludes every
nonzero binary remainder, and the second intersection excludes every
nonzero whole-radix shift within a native cell. Global occupancy is used
only after alignment has been established.

## 4. Carry, padding, and exact mask balance

The inherited uniform pre-decoding bound is

    M = (986+2)(2 sum_(e in E)c_e + 6).

Here M has 75 bits and 4M+8 has 77 bits. The builder and independent
materialized-port audit check the strict inequality

    max(4M+8, 2mu+4, 2(2^75-1)+4, 16) < 2^77 = rho.

Thus the same no-carry and nonaligned-rotation lemmas apply. This is a
strict integer inequality, not merely a comparison of bit-length labels.

The largest unshifted current exponent remains 5495+3296=8791. Spatial
and temporal terms stop earlier, at 3338 and 3296. Consequently all
padded bits at 8792,...,8803 are identically zero on intended aligned
cells, including the safe dummy changes used by the rank controller.
The padding lies strictly below L=8807 and contributes
11*75+39=864 mask bits. The original tests contribute
2*50+10+9+2+1=122. Therefore

    popcount(MF_native)=986,
    popcount(MC)=d-986,
    MC=2 mod4, MF_native=4 mod8,
    0<MC,MF_native<B-1.

These exact identities, including the population sum d, are checked on
the materialized integers. They preserve the arithmetic input interface.

## 5. Explicit rank controller for the new base

Set lambda=56611 and k=lambda-1=56610. The finite certificate proves
that 7,11,8807,lambda are prime, d=7*11*8807, and

| Modulus | 7 | 11 | 8807 | lambda |
|---|---:|---:|---:|---:|
| Order of B | 3 | 10 | 629 | 6290 |
| B mod modulus | 2 | 6 | 173 | 22472 |
| B^2-1 mod modulus | 3 | 2 | 3507 | 20663 |
| 1+B DC+B^2(DR+1) mod modulus | 6 | 1 | 3377 | 14311 |

The order modulo d is 18870 and divides k. Also

    B^k mod lambda^2 = 1810929280 != 1,
    B^k mod lambda = 1.

Thus v_lambda(B^k-1)=1. Canonical halting rectangles may have independently
large width w and height h that are powers of lambda, by the imported
rectangular padding theorem. Put N=wh=lambda^n, q=B^N, T=N/lambda,
C0=d lambda, and require N>d lambda^2 and h>lambda. The orders divide
lambda-1, so q and B^w are both B modulo d lambda.

The inherited exact change in actual packed rank at dummy cell j is

    delta R = -Gamma B^j,
    Gamma = rho^1063(q^2-1)[1+q(DC+B DR+B^w)].

The unit table gives gcd(Gamma,dN)=1. The valuation certificate and
binomial lifting give order T for B^k modulo lambda^n. It is one modulo
d and lambda, so its first T powers are precisely the T residues
1+C0 z modulo C0 T.

Every residue modulo dN is a Boolean subset sum of

    {B^(2+kj):0<=j<T} union {B^3}.

For completeness, normalize a target by B^-2. Choose epsilon in {0,1}
so that subtracting epsilon B makes it nonzero modulo lambda. Its least
residue a modulo C0 has 1<=a<C0<T and gcd(a,T)=1. Write the target as
a+C0 u modulo C0T and solve

    a z0 + a(a-1)/2 = u mod T.

Select the a distinct orbit residues with additive coordinates
z0,z0+1,...,z0+a-1 modulo T, and include B^3 precisely when epsilon=1.
Their sum is the target. This proof works without requiring all subset
sums, or assuming a power-of-five geometry.

The largest selected position is at most
N-N/lambda-lambda+3. Since h>lambda, w<N/lambda; all selected positions
and their required translates by one and w remain below N and avoid the
origin. The separate position3 is distinct because k>1. Thus the source
no-wrap dummy argument remains valid. Select the target
(R0-dw)Gamma^-1 modulo dN, where R0 is the original canonical rank.
The changed actual rank then satisfies R=dw modulo dN, precisely the
helical calibration required by the native compiler.

## 6. Canonical parity and composition

The unchanged low mask congruences give canonical R=3 mod4. Both d and N
are odd, so the canonical dyadic scale w_arith=2^(R-dN) is a square.
The canonical Pell base is even; c=psi_A(R) is odd. Choosing strong
index m=cR gives an odd positive normalized multiplier, and its ordinary
Delta-scaled version is odd because Delta is odd. The unchanged
half-binomial population identity gives v2(Y)=popcount(R)-2=3 log2(q),
so the scale in Y=s q^3 is odd. These are the same simultaneous parity
promises as package36, useful for signed and square-scale adapters.

Soundness uses arbitrary solutions, not the special prime-power choices
made in completeness. Native decoding recovers the unchanged marked
Wang language, hence a blank K215 halt, hence a finite ZFC refutation.
Completeness starts from such a finite halt, pads it as above, tunes the
actual rank, and applies the imported arithmetic witness construction.
Thus a compatible skeleton rebound to this entire tuple has a solution
exactly when ZFC has a finite refutation; negation gives the requested
unsolvability/Con(ZFC) equivalence, formalizable in ZFC.

Rebinding changes no variable count, degree, or evaluation gates of a
port-parametric arithmetic skeleton. A Jones-compressed equation must
recompute every derived coefficient/index from the new source tuple;
an index from another tuple must never be retained silently.

## Verification and attribution

Run `python3 build_complemented.py` and `python3 audit_complemented.py`.
The first reconstructs the literal tile language from the 430 machine
actions, checks the new decoder over all 1,157,632 local label cases,
checks the complete native interface, and materializes the four ports.
The second does not import the builder; it independently reconstructs
the full four integers, checks the native-basis identities from decoded
digits, and checks the exact controller with the actual integer ports.
Both use only the Python standard library.

These finite checks supplement the ordinary universal arguments above;
they neither prove Con(ZFC) nor replace a proof-assistant formalization.
The predecessor geometry and rank-controller method are credited to
package36. The new contribution is the complemented whole-label field
lemma, its explicit application with reordered fields, and the fully
recomputed compatible coefficient tuple and controller.

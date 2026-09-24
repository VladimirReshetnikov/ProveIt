# Supplying the width product gives a 91-operation tag certificate

Supply the positive product Z=AH and the transport multiplier D as
coordinates, and recover the integer width A from the retained geometry
equations. This saves one multiplication from the
[compiled initial-bound certificate](EXPLORATION_COMPILED_INITIAL_TAG_BOUND.md).
The complete new source has **91 operations: 50 multiplications and
41 additions/subtractions**, with **29 positive unknowns and 18 equations**.
All nine masks and both transports remain. The packing and Pell index are
unchanged under the exact witness maps.

The theorem assumes beta>=2 and appendant length a>=2. Its admitted input
domain is K^2 Li<C. Soundness proves actual eventual halting on this
domain; completeness has the previous first-zero, positive-startup and
single-zero terminal promises. Neary's normalized encoded instances
satisfy these restrictions. This does not change the established bound
for a fixed universal system taking ordinary numerical input.

Author and two independent complete proof/source reviews and fresh
verification runs pass. The
[checker](../verification/explore_product_coordinate_tag.py) and
[receipt](../verification/explore_product_coordinate_tag.json) record the
complete sources and their exact arithmetic evidence.

## 1. Source equations and exact saving

Use the fixed constants

    K=3^beta, k=K/3, B=3^(a-1), U=value(appendant),
    epsilon=U mod3, Ut=(U-epsilon)/3, cc=(k-1)/2,
    C>max(K^3,3K*3^a,2KU+3), j=(C-C/K)/2,

where C is a fixed power of three. Valid inputs have Li=3^ell,
ell>=beta, Boolean Ni with 0<=Ni<Li/2, and K^2 Li<C.

Remove the supplied coordinate A. Supply two positive coordinates
D and Z, named transport_scale and AH in the checker. Retain the
other positive coordinates and compute

    M1=2Q+S1,
    N=3T+S1        if epsilon=0,
    N=3T-2Q        if epsilon=1.

The eight outer equations are

    kD=R,
    D(T-E+Ut*M1)=N-Ni,
    D[L+(B-1)M1]=L-Li+3q,
    RH=H+q-1, RH=CZ, Rv=q,
    2r+1=q^9+2P, r+betaP=q^9.                       (1)

The nine conceptual fields are

    S0=H-S1, S1, Q, G=Q+Z,
    M0=L-M1, M1, Ebar=ccH-E, E, GN=N+jZ.

Their factored packing is

    TE=ccH+(q-1)E,
    Rest=L+(q-1)M1+q^2[TE+q^2 GN],
    P=H+(q-1)S1+q^2[Q+q(Q+Z)]+q^4 Rest.            (2)

The sixteen positive kernel auxiliaries and ten fixed-plus43 kernel
equations are unchanged. The norm-source correction is at zero-based
comparison16, with the same computed u as in the predecessor.

Previously the geometry and product used four multiplications:

    D=(C/k)A; kD; AH=A*H; H(R-1).

They now use three:

    kD; RH; CZ.

The subtraction R-1 is replaced by the addition H+(q-1), using the
already computed q-1. Thus the total changes from 51M+41A to 50M+41A.
Replacing A by D,Z adds one positive coordinate; the extra product
identity adds one equation. The checker verifies both complete sources,
all eighteen comparisons, and the unchanged packing under Z=AH.

## 2. Integer width recovery before the kernel

Since beta>=2, the fixed integer k=3^(beta-1) is divisible by3.
The retained integer equations kD=R and Rv=q therefore imply

    R=0 mod3, q=0 mod3.

Reduce RH=H+q-1 modulo3. Its left side is zero, so H=1 modulo3.
Hence H is relatively prime to the fixed power C. The equation CZ=RH,
with Z an integer, consequently forces C to divide R. This argument
uses only the four integer geometry equations: no power conclusion,
field typing, content bound, or kernel premise is needed.

Define

    A=R/C.

It is a strictly positive integer because R is positive and C divides R.
The two product equations give exactly

    D=(C/k)A, Z=AH.                                 (3)

At this stage A need not yet be a power of three. That is a later
consequence of the full predecessor, which initially needs only a
positive integer coordinate A. In particular the argument already gives
R>=C, with no separate lower-bound equation or numerical computation.

## 3. Complete same-index map and soundness

Every equation of the 92-operation predecessor follows, including its
head equation H(R-1)=q-1. Every conceptual field, every computed packing
value, the index r and all sixteen supplied Pell auxiliaries are identical.
This is a full positive same-index witness map to that predecessor,
not just a correspondence between transport equations.

Its direct soundness theorem on K^2 Li<C therefore proves that the
specified actual input halts. It supplies the preliminary kernel bounds,
power and field decoding, the A=1 exclusion using positive Q, and the
causal length and signed-content inductions. The integer map in Section2
precedes all these consequences, so it is valid on the predecessor's full
domain a>=2 in both leading branches.

## 4. Complete positive converse

On the stated completeness domain, the predecessor constructs a complete
positive witness, choosing sufficiently large A and an even index using
its wrapped zero-edge padding. Define D=(C/k)A and Z=AH. They are positive
integers. Replace the coordinate A by D,Z, and retain every other coordinate.
Equations (1) follow immediately. The fields (2), P and r are unchanged,
so the very same sixteen positive Pell auxiliaries work.

This proves both directions without a new parity choice, input recoding,
or cost for constructing fixed numerals. Neary's designated input has
Li=3^(a-beta+1), so K^2 Li=3K*3^a<C. Its beta=10p and a=beta*s satisfy
beta>=2,a>=2, while the startup and terminal promises are established in
the [positive-startup proof](EXPLORATION_POSITIVE_STARTUP_TAG.md) and
[terminal normalization](EXPLORATION_ZERO_TERMINAL_TAG_PARITY.md).
The encoded-instance boundary is the same as for those results.

## 5. Evidence boundary

The checker verifies every source polynomial for both fixed leading
branches, counts the full DAG, and verifies the forward witness identity
against every predecessor comparison. Exact integer geometry checks
include nonpower R and q and reject fractional Z when C does not divide R;
they establish the intended dependency order without a power premise.
These geometry tuples are not claimed to be full source solutions.
Separate power-geometry checks also verify the eventual recovery of A.

Fresh finite histories check all eight new outer comparisons, all seven
inverse predecessor comparisons, all nine individual masks, positivity,
and the unchanged exact index valuations on both canonical and padded
tuples. The established kernel converse supplies the large positive
auxiliaries; these are not materialized. The regression programs are
ordinary finite examples, not materialized Neary simulators.

Fresh verification runs check both 91-operation sources and all 36
symbolic comparisons. It covers 252 integer-geometry cases and 192
power-geometry cases with 132 integral product coordinates. The main history regression covers
32 genuine traces and 272 source rows, yielding 64 complete outer tuples.
Both leading branches occur (22 and 10 histories); 12 histories have odd
beta. The canonical indices split 18 even and 14 odd, so 14 selected
witnesses use padding. One simulation cutoff remains unclassified.
Four further traces cover both leading branches at a=2 and a=3, with
eight complete canonical/padded outer tuples and their exact inverse maps.

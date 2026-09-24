# Exact counterexamples to deleting or replacing history-mask planes

The round40 moving-frame component system tests the six Boolean fields
B,D,X,E,Z,B+H. The two deletions below have smaller exact arithmetic
schedules but do not retain its finite-history meaning over unrestricted
positive row parameters I,F. These counterexamples do not refute a
different construction that strengthens the initial-row guard.
Section 4 separately treats further local deletions after that repair,
and Section 5 refutes replacing the row-start test by a shifted source
plane even with the repaired guard.

`../verification/explore_dropped_history_planes.py` verifies every source
residual for both edited schedules, checks the complete outer tuples
below, and checks their exact special-mask popcounts. The companion JSON
keeps the arithmetic pass separate from the semantic counterexamples.

## 1. Removing the independent Boolean B test: 84 operations

Delete the final multiply/add pair of the six-field Horner expression,
and name the preceding D-containing register `packed`. The resulting word
is

    P=D+Q*(X+Q*(E+Q*(Z+Q*(B+H)))).

All other round40 instructions and equations remain unchanged. This gives
84 operations: 45 multiplications and 39 additions, still with 31 positive
unknowns and 21 equations. The only changed source residual is the
polynomial definition of r through this new P.

The following positive tuple satisfies every outer equation:

| Quantity | Value | Quantity | Value |
|---|---:|---|---:|
| width m | 5 | height t | 2 |
| W | 1024 | Q | 1048576 |
| v | 32 | q | 1024 |
| quot | 32 | H | 1025 |
| B | 85328 | C | 21332 |
| D | 20560 | X | 65540 |
| E | 16448 | Z | 328976 |
| Y | 69652 | B+H | 86353 |
| I | 852 | F | 68 |
| alpha | 600604 | alphaI | 172 |

In particular B=4C, q=v*quot, Q-1=H*(W-1),

    B+C=X+2D, 4B+D=Z+2E, Y+E=X+D,
    4B+B+C+alpha=Q, I+alphaI=W,
    I+WY=C+QF.

The five retained fields D,X,E,Z,B+H are positive Boolean base-four
words below Q, but B is not Boolean. Thus the alleged independent-B
redundancy fails even with all positive domains and temporal alignment.
Here I is nonBoolean: its highest digit is three. This detail matters.
The example violates both strengthened guards 4I<W and I<v (here
852>32), and is not evidence against either later guarded variant.
It only refutes the displayed
unguarded 84-operation edit.

## 2. Removing the row-start plane B+H: 83 operations

Instead keep P=B+Q*(D+Q*(X+Q*(E+Q*Z))). Delete the Bh addition and
the highest Horner multiply/add pair, replacing the next top operand
by Z. This is 83 operations: 45 multiplications and 38 additions, with
the same 31 unknowns and 21 equations.

There is a smaller all-positive counterexample:

| Quantity | Value | Quantity | Value |
|---|---:|---|---:|
| width m | 2 | height t | 3 |
| W | 16 | Q | 4096 |
| v | 4 | q | 64 |
| quot | 16 | H | 273 |
| B | 340 | C | 85 |
| D | 84 | X | 257 |
| E | 80 | Z | 1284 |
| Y | 261 | B+H | 613 |
| I | 5 | F | 1 |
| alpha | 2311 | alphaI | 11 |

Again every displayed outer equation holds. The retained five fields
B,D,X,E,Z are Boolean, but B has nonzero row-start digits and B+H
is not Boolean. The removed first-column predicate therefore does not
follow from B=4C, the shared numerical bound, and moving alignment.
Unlike the first example, both row parameters in this example are
Boolean. A Boolean input alone cannot repair this different deletion.

## 3. Complete positive Pell extension of both tuples

These are more than loose local-plane assignments. In each case all
five retained fields are between zero and Q, so the corresponding P
satisfies 0<P<Q^5<Q^6. Q is a power of four. Set

    L=Q^8, n0=Q^6, lambda=(L-1)/3,
    r=(L-P)*(L-1)+2*lambda.

The exact special-mask lemma proves that n0^2=Q^12 divides binom(2r,r).
The least retained field is D=20560 in the first case and B=340 in the
second, each divisible by four. Thus P and r are even. The same
pre-power bounds give n0^2<r<Q^16<n0^3 and n0>=64.

Consequently the complete positive necessity construction of
`BASE_TWO_PELL_90_PROOF.md`, Section 6, applies to the retained
43-operation kernel. More explicitly, choose J=2r+1, U=2^J,
Ypell=floor((U+1)^(2r)/U^r), and w=U/n0^2, s=Ypell/n0^2.
Power-of-two and binomial divisibility make both quotients positive
integers. Put a=Ypell*(U+1), A=a+2,
c=psi_A(J), d=chi_A(J), k=psi_(2U*Ypell^2+1)(r+1).
The strict ratio bounds give positive eta=c-Ypell*k and zeta=k-eta;
the odd-parameter norm and index congruence give positive tau and h;
the first exponent congruence gives a positive integral gamma.
Finally `HALF_PARAMETER_PELL_92_PROOF.md` gives the positive relaxed
and half-parameter variables i,f,j,o,y_aux because r is even.

Therefore each tuple extends to a full positive solution of its edited
21-equation component system, including the retained Pell equations.
The exact finite checker does not materialize those astronomical Pell
integers; it checks every finite premise for that general construction.
The first example has r of bit length 320 and popcount 240; the second
has bit length 192 and popcount 144. These equal exactly the logarithms
of their respective Q^12 divisibility scales.

No universal counterexample is being inferred from the omitted input
and halt interfaces. The precise conclusion is that these two
unguarded edits do not imply the Boolean finite-history semantics
proved for round40. A strengthened initial bound can change that
conclusion and must be analyzed as a separate system.

## 4. A further local plane cannot simply be dropped after the input repair

The guarded five-plane construction replaces the input bound by
I+alphaI=v, which legitimately repairs the first deletion above.
Nevertheless each of its four local Boolean fields D,X,E,Z still
carries independent content. The following height-one tuples satisfy
that stronger bound, have Boolean I, and have every retained field
Boolean while the individually omitted field is nonBoolean:

| Omitted test | m | B | C=I | X | D | E | Z | Y=F | alpha | alphaI |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| D | 3 | 4 | 1 | 1 | 2 | 1 | 16 | 2 | 43 | 7 |
| X | 5 | 84 | 21 | 73 | 16 | 16 | 320 | 73 | 583 | 11 |
| E | 5 | 84 | 21 | 65 | 20 | 50 | 256 | 35 | 583 | 11 |
| Z | 5 | 84 | 21 | 65 | 20 | 1 | 354 | 84 | 583 | 11 |

In each row Q=W=4^m, v=q=2^m, quot=H=1, and T=B+H is Boolean.
The local and temporal equations hold exactly; all supplied values
are positive, 4Y<Q, and I+alphaI=v. Deleting one of four Boolean
local fields would shorten the Horner packing by two more operations,
but these tuples disprove its intended truth-table interpretation.

They also extend through the same positive Pell construction. Place
Z first when omitting D, and D first in the other three cases; these
lowest fields are even. The four retained fields lie below Q, their
P is Boolean and even, and the exact mask again gives the required
central-binomial divisibility and even r. The companion checker
verifies all four tuples and those numerical premises. It does not
claim a full new 82-instruction source checker, since the immediate
semantic obstruction already rules out the simple deletion proposal.

## 5. Replacing B+H by C=B/4 does not save an addition soundly

The proved direct-length system in
`EXPLORATION_DIRECT_HISTORY_LENGTH.md` has 81 operations. A tempting
edit keeps all five mask fields but replaces B+H with the already
supplied C. Since B=4C, Boolean C would imply Boolean B without
requiring a separately computed sum. Delete the Bh=B+H addition and
replace its use in the top field by C. The resulting packing is

    P=D+qX+q^2E+q^3Z+q^7C, Q=q,
    L=q^8, n0=q^6, D0=q^12.

All other primitives and all 20 equations remain unchanged. This
edited schedule has exactly 80 operations, 44 multiplications and
36 additions/subtractions, with the same 30 positive unknowns. The
checker verifies all 20 symbolic source residuals, including the
existing auxiliary correction. Thus its arithmetic reduction is
real, but its endpoint interpretation is false.

Here is a complete positive outer tuple for the edited system:

| Quantity | Value | Quantity | Value |
|---|---:|---|---:|
| width m | 3 | height t | 3 |
| W | 64 | Q=q | 262144 |
| v | 8 | quot | 32768 |
| H | 4161 | alphaI | 3 |
| B | 87316 | C | 21829 |
| D | 21764 | X | 65617 |
| E | 21504 | Z | 328020 |
| Y | 65877 | I | 5 |
| F | 16 | | |

The geometry, strengthened input bound, local equations, and temporal
equation all hold exactly:

    W=v^2, q=v*quot=W^3, q-1=H(W-1),
    I+alphaI=v,
    B=4C, B+C=X+2D, 4B+D=Z+2E, Y+E=X+D,
    I+WY=C+qF.

Every retained mask field C,D,X,E,Z is Boolean in base four. The
first four are below q; Z is between q and 2q. Its additional top
digit is legitimate in the gapped packing: it occupies a vacant
position above q^3Z, well below the field q^7C. In particular, the
counterexample does not rely on hiding a nonBoolean digit in a carry
between two packed fields. Both row parameters I,F are Boolean, and
the strong bound I<v holds.

The lost condition is exactly the row boundary. The three row-start
digits of B are 0,0,1, and B+H is not Boolean. Testing C instead
correctly proves that B is Boolean, but it does not force those row
starts to vanish.

The advertised finite endpoint is false, not merely represented with
an incorrect rectangle. Under the infinite zero-exterior moving
update b -> 4*Rule110(b), the rightmost-one position increases by
exactly one at every step. Since I=5 has rightmost base-four position
one and F=16 has position two, any genuine trajectory from 4I to 4F
would have to have height one. However, the actual one-step raw
successor of 4I=20 is 21, so the one-step physical successor is 84,
not 4F=64. No permitted height produces this endpoint pair.

### The full positive Pell extension still applies

Let R=D+qX+q^2E+q^3Z. The exact tuple satisfies

    0<R<q^7,
    P=q^7C+R<q^8=L.

It also satisfies P Boolean, with even lowest field D. Set

    lambda=(L-1)/3,
    r=(L-P)(L-1)+2lambda.

The checker verifies all of the following integer premises:

    P and r are even,
    n0>=64, n0^2<r<q^16<n0^3,
    popcount(r)=216=log2(q^12).

Here r has bit length 288. Thus the special-mask theorem gives
D0=q^12 dividing binom(2r,r), with precisely the scale and parity
required by the unchanged 43-operation positive Pell construction.
Use the construction detailed in Section 3 with this n0,r: choose
J=2r+1, U=2^J, Ypell=floor((U+1)^(2r)/U^r), positive integer
w=U/D0 and s=Ypell/D0, then construct a,c,d,k,tau,h,eta,zeta,
gamma and the relaxed half-parameter auxiliaries. Every hypothesis
is supplied by the displayed inequalities and divisibility; the
missing B+H mask is not an input to that construction.

Consequently the tuple extends to a full positive solution of the
edited 80-operation, 20-equation system. The finite regression
verifies the complete outer tuple, source algebra, packed bounds,
Booleanity, parity, exact popcount, and false endpoint. The enormous
Pell coordinates are supplied by the general construction and are
not materialized by that regression.

This rules out the specified C-for-B+H replacement. It does not rule
out a different field choice accompanied by a new boundary argument,
and it makes no assertion about the published universal system.

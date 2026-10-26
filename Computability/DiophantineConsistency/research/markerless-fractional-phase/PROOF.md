# A local fractional-phase lemma using the forced Start South bits

This ordinary lemma replaces the *fractional-phase* use of the separate
marker, under explicit preliminary-count and carry-reset hypotheses. It
does not remove the marker's separate whole-field-alignment obligation.
It is not a complete new native encoding or consistency equation.

The ordinary-proof author is `/root/controller_certificate`. The local
idea was also independently identified by `/root/circuit_reduction`, who
authored the separately frozen finite challenge and its note. The accepted
length2011 proof and equation remain unchanged.

## 1. Exact hypotheses and local equation

Let

    rho = 2^47, M = 2^45, mask = M-4,
    U = 253 + 2^8*76 + 2^17*252 + 2^25*510,
    c0 = 2 + 2^11*(2^34-U).

Thus U=17145810173 and c0=69752854530. The packed complemented
Start colors are (253,76,252,510). Suppose a prospective encoding has
already established the following, without assuming fractional phase zero:

1. Every selector is Boolean and every cell has at most one selector.
   The origin mask forces selector0, so the origin's selected tile is Start.
2. The physical copied labels form an arbitrary integer W in [0,2^34).
   In particular, no equality W=U is assumed.
3. The origin's actual clause digit is the residue modulo rho of

       c0 + 2^11*W + k + u + v + 2^b*epsilon,

   where 0<=k<=57, u,v,epsilon are Boolean and 0<=b<=46. A missing unit
   can be represented by zero. This digit avoids the mask M-4.
4. Each of the nine copied-South bit tests has zero incoming carry.
   Its non-temporal odd part is precisely the corresponding current
   physical South bit; every other non-temporal contribution is even.
   Its temporal contribution is 2^b times a Boolean value.

These hypotheses are local interfaces. In any application, preliminary
one-hotness and the zero incoming carries must be proved first. In the
accepted2011 argument the padding staircase supplies preliminary
one-hotness. A changed layout must separately verify that argument and
the complete reflected envelopes; this lemma does not assert them by fiat.

## 2. What the accepted clause actually implies

The mask M-4 tests precisely bits2..44. Avoiding it means the raw value
is 0,1,2 or3 modulo M. Taking a rho-residue makes no difference because
M divides rho.

For b<=10, let t=2+k+u+v+2^b*epsilon. Then

    2 <= t <= 2+57+1+1+1024 = 1085 < 2048.

The tests at bits2..10 force t into {2,3}; hence t creates no carry into
bit11. The remaining tests imply W-U=0 modulo2^34. Both W and U belong
to [0,2^34), so

    W=U, b<=10.                                           (1)

For b>=11, let t=2+k+u+v, again in [2,61]. The same low tests force
t into {2,3}. The high part then gives

    W = U-2^(b-11)*epsilon modulo2^34, b>=11,               (2)

where W is the unique representative in [0,2^34). Neither conclusion
assumes the ordinary full-label recovery lemma, whose Boolean temporal
premise is not yet available.

## 3. The current South block cannot vanish

Let S=floor(W/2^25), the unsigned nine-bit South component.
Equation(1) gives S=510. In(2), epsilon=0 also gives510. If epsilon=1:

- For 11<=b<=35, the subtracted power is at most2^24. It can borrow at
  most one unit from the South block, so S is509 or510.
- For 36<=b<=44, S=510-2^(b-36). Since the largest subtracted power is
  256, this is at least254 and is nonzero.
- For b=45 or46, the subtracted power is divisible by2^34, so S=510.

In the first two cases U exceeds the subtracted power, so there is no
unmentioned wrap at bit34. Every possible accepted local clause therefore
has S>0, for every phase and all allowed carries and unit contributions.

Suppose b>0. At any one of the nine copied-South tests, the temporal
contribution and every reflected background term are even. The incoming
carry is zero. Reduction modulo the even radix preserves parity, so its
bit0 test forces the current South bit to be zero. All nine tests force
S=0, contradicting the preceding paragraph. Thus

    b=0.

This proves the stated local lemma. It uses all nine South-copy tests,
rather than assuming in advance which of them are nonzero. Once b=0,
the ordinary complete clause lemma may recover all labels in every cell.

## 4. Exact scope of the finite challenge

The independently authored170-line audit reads literal JSON coefficient
data, not parent executable modules. Its frozen bindings are:

| File | SHA256 |
| --- | --- |
| audit.py | 6d1d54e7de77789c9cc4c59968663a798df6d2fedee1635204e6aedd23c57183 |
| RESULTS.json | edb2f070526844ee4a83f023e8d81454b09e69006ccd6e5062fcd4dc0a8259c6 |
| NOTE.md | 6d3e789869cbaedb742fcefa1dd8f0c49f2a3045c34a992f111b5afc9962cca9 |

For all47 phases, all58 carries, both independent units and both temporal
values, it solves the actual mask congruence for every accepted residue.
Divisibility by2048 and the complete range W<2^34 establish exhaustiveness;
every solution is substituted back into the actual mask. A second interval
route demands W<2^25 directly and obtains no solution, independently of
using(1)..(2) as premises.

The geometry portion actually deletes the old marker at1004 and its bare
term while retaining C1005. Under the explicitly conditional one-hot
premise, it checks all969 reflected envelopes through field968 and every
South-copy odd part. This supplies that layout's conditional local reset
facts, not a complete markerless soundness/completeness theorem. An
incoming-carry1 negative control correctly invalidates the parity lemma.

The present proof author read all170 audit lines and its full note before
running normal and optimized read-only reproduction. Both passed without
changing any frozen finite artifact. The audit predates this ordinary
proof and does not cryptographically bind it; the file roles remain distinct.

## 5. Whole-field obstruction and the fixed-marker lower bound

Deleting the marker leaves genuinely unresolved field offsets. At offset18,
all nine targets960..968 have temporal sources942..950, the South family
itself. The copied-color relation becomes S_i=S_theta(i). Constant510
passes this relation, so the fractional lemma cannot exclude that offset.
Offset1 also has all eight nonzero Start South-bit sources physically
available. These are failures of the existing alignment argument, not
constructed complete spurious native solutions.

With physical marker1004 and bare monomial rho^1004 retained, their
positive formal product has degree2008. If a construction retains one
whole zero field above every formal product and an odd cell length, then
L-2>=2008, so L>=2011. This lower bound is scoped to those retained
structural conditions; it is not a global minimum for Diophantine equations.
Lowering the clause alone cannot beat the accepted2011 raw length.

## 6. A prospective smaller-marker use, with a rejected calibration

A moved marker at996 has odd non-temporal part selector0 plus East bit0.
The decoded Start East color252 has bit0 zero. After fractional phase is
excluded by this lemma, Start therefore still forces an odd temporal
marker source. At offset18 the marker equation would read

    e_theta(i) = e_i xor delta_Start(i),

where e is decoded East bit0. A Start has e=0 and maps to e=1. At any
state with e=1, delta_Start=0, so the sequence remains1 forever. No finite
permutation cycle can contain a Start. This argument does not require
every other tile's East bit0 to be1. It is a promising additional offset
exclusion, subject to complete new count, carry and canonical checks.

The first suggested center997 failed such a check. The present author
mistakenly reused a pre-sorting tile1 calibration when claiming that the
extra selector1 plus East bit1 was at most1. The actual sorted tile1 is
(0,433,0,438), with complemented East255 and bit1 equal to1. Its canonical
occupied clause is M+2+1+1=M+4, which fails bit2. The finite author caught
this error before any complete candidate or proof was asserted. The failed
center997 tuple remains a concrete obstruction; its working modular
controller would not repair the failed native completeness.

A separate center995 proposal puts the marker above the clause and leaves
only the Boolean dummy at977 as the extra clause input. It is being checked
in another namespace. No result about that full tuple is inferred here.

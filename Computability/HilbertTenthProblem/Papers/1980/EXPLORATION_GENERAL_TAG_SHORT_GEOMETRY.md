# General short-geometry tag certificates describe a first-step halt

Review status: author and two independent complete proof/source reviews and
fresh verification runs passed without findings. The added enlarged-constant
nonpower family also passed both independent focused reviews and fresh runs.
The proof and arithmetic are frozen.

This is a scoped soundness and completeness theorem for the weakened104
tag source. Enlarge the fixed power-of-three compiler constant freely to

    C>max(K^2,3^a,2U+3), K=3^beta, a>=2.

For this choice, every complete positive source solution satisfying

    R>=K^2 H

has an input that halts after its **first actual tag step**. Conversely,
every input that halts after its first step has a complete positive
witness satisfying this condition, with H=1 and R=q.

The condition R>=K^2 H is a theorem hypothesis. It is not an uncharged
comparison added to the104 schedule. The result does not prove soundness
outside this range or an unrestricted104 halting certificate. Neither
R being a power of three nor H being Boolean is assumed in the forward
direction. The sharper separate beta2 theorem with R>=28H is unchanged.

## 1. Retained source and the fixed-constant change

Use the source in `EXPLORATION_TAG_RADIX_DIVISIBILITY_OMISSION.md`, with
the same encoded input and either fixed-leading-symbol schedule. Put

    k=Kh=K/3, B=3^(a-1), cc=(k-1)/2,
    Li=3^ell, ell>=beta, Ni=value(input),
    C=3^c>K^2, R=CA, A>Li,
    H(R-1)=q-1, 0<Lf<K.

The other fixed requirements C>3^a and C>2U+3 are retained. Increasing
this fixed numeral changes no arithmetic instruction count. C/k is
still a fixed positive integer, and the shared scaled transport remains

    D=(C/k)A=R/k,
    D O=L-Li+qLf, O=L+(B-1)M1.

The existing signed-content bootstrap, scalar bounds and q-block
recovery work without the omitted q=Rv equation, as identified in
`EXPLORATION_TAG_TERMINAL_RESTRICTIONS.md`. They give q a power of three,
and all ten separate Boolean words, with the fixed Gstar unit1. The
recovered scalar equations include

    L=M0+M1=2(N+Nbar)+H,
    M1=2Q+S1, S0+S1=H, Gstar=Q+AH+S0,
    R(N-3E-S1+UM1)=K(N-Ni+qNf).

No subsequent row interpretation at radix R is imported. The
unconditional parts of `EXPLORATION_NONPOWER_TAG_FIRST_SYMBOL.md` give

    v3(L)=ell, digit_ell(L)=1,
    no M0 or M1 bit occurs below ell,
    S1 mod3=Ni mod3, and 3|A.                         (1)

These parts do not assume H Boolean. Let m=v3(R) and h=3^m. Since
c>=2beta+1 and 3|A, m>=2beta+2; in particular h>K^2.

## 2. The two length expressions coincide exactly

Geometry and positivity give q>=R and q=(R-1)H+1<=RH. Also R=CA>K^3.
The length source gives

    (R-k)L<kKq,
    L<kKq/(R-k)<(kK+1)H.                              (2)

For the second strict inequality use q<=RH and
R>K^3>k(kK+1). All these are scalar inequalities, not statements about
digits of R or H.

Define the integer

    Delta=O-kLfH.

An exact consequence of transport and geometry is

    R Delta=k[L-Li-Lf(H-1)].                          (3)

The integer D=R/k is divisible by K because C>K^2. Both Li and q are
also divisible by K. Thus the scaled length source forces K|L. Adding
the Boolean words M0 and M1 produces digits at most2 and no carries,
so K|M0 and K|M1 separately. Therefore K|O and k|Delta.

Under R>=K^2 H, equations(2)--(3) yield

    Delta/k<L/R<(kK+1)/K^2=1/3+1/K^2<1,
    Delta/k>-Li/R-KH/R>-1/C-1/K>-1.

Hence the integer Delta/k is zero. We have proved

    O=kLfH, L=Li+Lf(H-1).                             (4)

This argument also applies when beta=1; no terminal parity fact is
needed for the collapse.

## 3. The terminal length is a genuine marker

Geometry implies H=1 modulo3. Write s=v3(Lf), so 0<=s<=beta-1. By(1),
both M0 and M1 are divisible by Li, and therefore so is O. Equation(4)
then gives

    ell<=v3(O)=beta-1+s<=2beta-2<m.                   (5)

For beta=1 this contradicts ell>=1, so no solution exists. Assume
beta>=2 from now on.

Modulo h, geometry gives H=1. Equations(4)--(5) imply

    L mod h=Li, O mod h=kLf,
    0<Li<h, 0<kLf<K^2<h.                             (6)

The sum M0+M1 is carry-free. Its only occupied low-h digit is therefore
the unit marker Li, in exactly one channel.

If M0 contains it, then M0 mod h=Li and M1 mod h=0, so O mod h=Li.
Consequently

    kLf=Li.                                           (7a)

If M1 contains it, O mod h=B Li modulo h. Both B and Li are powers of
three. If B Li>=h this residue is zero, contradicting(6). Thus B Li<h
and

    kLf=B Li.                                         (7b)

Either case proves that Lf itself is a power of three. In particular
its exponent s is the actual candidate successor length, not an
untyped integer endpoint.

## 4. The marker channel matches the actual input symbol

Because H=1 modulo h and S0,S1 are Boolean, there are no nonunit S1
bits below m. If S1 has unit0, the equation 2Q+S1=M1 cannot start a
carry below m. A first nonzero Q digit would emit the forbidden digit2.
Hence Q mod h=M1 mod h=0. Thus a low M1 marker requires S1 unit1.

It remains to exclude a low M0 marker when S1 has unit1. In that case
M1 mod h=0 and(7a) holds. Subtracting the two expressions in(4) gives

    (B-1)M1=(k-1)Lf(H-1).                             (8)

If H=1, equation(8) gives M1=0, which immediately excludes S1 unit1.
Suppose H>1. Then q>R, and the exact identity

    (R-1)(H-1)=q-R

shows v3(H-1)=m and (H-1)/h=R/h modulo3. Write dR=(R/h) mod3, a
nonzero trit. Since Lf=3^s, B-1 and k-1 are both -1 modulo3, and the
right side of(8) is positive, it follows that

    v3(M1)=m+s,
    leading_trit(M1)=dR.

Booleanity of M1 forces dR=1. This local leading-trit fact is derived
from the marker relation; it does not assume H Boolean.

Let j0=v3(A)=m-c. By(1), j0>=1, and j0<m. The first nonzero trit of
AH is consequently1 at j0. If S1 unit1 and M1 mod h=0, the equation
2Q+S1=M1 forces Q to have trit1 at every position0 through m-1.
Also S0 has no trits below m. In Gstar=Q+AH+S0 there is no incoming
carry before j0; its digit at j0 is exactly2. This contradicts its
Boolean mask.

Therefore the two channels in(7a)--(7b) agree with S1 mod3. Equation(1)
identifies that selector with the actual first input symbol.

## 5. Actual halting after the first step

The given input has ell>=beta, so its first actual step is defined.
If its first symbol is zero, the rule appends one zero symbol. Its
successor length is ell+1-beta, which equals s by(7a).
If its first symbol is one, the rule appends the fixed a-symbol word.
Its successor length is ell+a-beta, which equals s by(7b).

In both cases 0<=s<beta because 0<Lf<K. Thus the actual first step
halts. Recovering its numerical successor content from a later encoded
block is unnecessary for this conclusion: the actual read symbol,
initial length and fixed production already determine its length.

This distinction avoids assuming a history shift by nonpower R.

## 6. Complete positive witnesses for every first-step halt

Conversely, suppose a valid input halts after its first step. Choose
a power of three A>Li, put R=CA, q=R and H=1, and let

    z=Ni mod3, d=Ni modK, ns=(Li-1)/2,
    Q=z ns, S1=z, S0=1-z,
    M1=z Li, M0=(1-z)Li, L=Li,
    N=Ni, Nbar=ns-Ni, Nsum=ns,
    E=(d-z)/3, Ebar=cc-E, Gstar=Q+A+S0.

Use the actual final word for Nf,Lf. For the fixed epsilon branch take
T=(Ni-z)/3 when epsilon=0, and T=(Ni+2Q)/3 when epsilon=1. These are
nonnegative integers, and reconstruct N exactly.

All ten words are Boolean. Their low/high supports in Gstar are
disjoint because A>Li, and its unit trit is1 in either selector case.
The actual scalar tag step gives both transports, and H=1 gives the
retained geometry. All zero raw coordinates receive the usual positive
adapters. The boundary slacks A-Li and K-Lf are positive. Since C>K^2,
R>=K^2 H also holds.

Pack the unchanged ten fields into P, set D0=q^10,
r=P+(D0-1)/2 and betaP=D0-r. All original mask/index inequalities hold,
and the generic44 positive converse supplies the seventeen positive
Pell auxiliaries at either parity of r. Thus these are complete positive
witnesses of the unchanged104 source, not just local transition tuples.

## 7. Explicit nonpower witnesses with the enlarged constant

The range contains genuine nonpower witnesses, not only the H=1 converse.
Use the fixed program beta=3, u=010 and input0001 from the complete
nonpower family in `EXPLORATION_TAG_RADIX_DIVISIBILITY_OMISSION.md`.
It halts after one step at the word10. Enlarge the fixed constant to
C=2187>K^2=729. For every integer k>=8 put

    h=3^k, q=h^4, R=h^3-h^2+h, H=1+h, A=R/2187.

Retain every raw field of that family except recompute

    AH=3^(4k-7)+3^(k-7),
    Gstar=1+4h+AH.

The five occupied trits of Gstar are distinct when k>=8, and its unit
trit remains1. All other masks are unchanged. The scaled transport
register D=(C/9)A is still R/9; both exact transports and all other
outer equations remain valid after changing the input slack to A-81.
This slack is positive. Also R>h^3/2 and H<2h, so
R/H>h^2/4>729, placing these witnesses in the theorem's stated range.

The new P and r are formed from the recomputed Gstar and differ from
the original family's values. Their Boolean/unit conditions give exact
valuation40k and all positive44 hypotheses, so fresh positive Pell
witnesses exist at these new indices. No old auxiliary tuple is reused.
The radix remains nonpower and R does not divide q.

The focused check evaluates k=8,9,12,16. All nine actual outer comparisons,
ten masks, positive nonkernel coordinates and the range inequality pass;
the exact valuations are320,360,480,640. Thus the scoped soundness theorem
does not obtain its result by silently forcing R to be a power.

## 8. Verification and scope

The companion `explore_general_tag_short_geometry.py` checks both unchanged
104 schedules, all40 source comparisons, and the new polynomial identities.
Its exact rational checks cover the collapse including R=K^2 H. Separate
finite valuation and marker-channel checks allow both possible leading
units of H-1; they are structural tests rather than claimed full tuples.
The converse regression builds complete nine-outer-equation witnesses
with the enlarged C, all ten masks and the exact kernel valuation for
actual first-step halts. Positive Pell existence is supplied by the
general theorem; the enormous auxiliary tuples are not materialized.

The author fresh run passed 108 rational cases, including 12 exact-boundary
cases; 23,328 structural marker trials with 49 admitted tuples; 48 exact
leading-two rejections; and 1,008 low-Q words with 132 forced local guard
rejections. The complete converse check covers 2,136 one-step inputs at
84 fixed programs and two widths each, giving 4,272 full outer tuples.
There are 3,920 zero-selector and 352 one-selector tuples, equally split
between the two fixed appendant-leading branches. The packed indices
have both parities: 1,568 even and 2,704 odd.

No positive solution with R<K^2 H has been classified here. The new fixed
constant has no arithmetic cost, but the external range hypothesis is
not silently added to the operation ledger. The unrestricted104 semantic
question remains open.

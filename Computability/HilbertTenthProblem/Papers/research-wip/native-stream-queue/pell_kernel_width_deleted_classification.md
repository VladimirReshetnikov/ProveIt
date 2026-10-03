# Exact strata after deleting the FIFO width bound

Delete only `I+beta=W` and its instruction and positive coordinate from
the [63-operation source](native_dualrail_fifo63.md). Keep `I=6x`,
`D=I+WA`, `q=WL`, and `A+D+alpha=q`, with all remaining supplied
coordinates positive. The resulting arithmetic relation is not the stated
FIFO relation: it admits both too-small widths and negative append values.
This note classifies its entire post-kernel projection, including width1.
It does not claim universality or a general decidability theorem.

## 1. Exact classification

Write `P=F0+qF1+q^2F2+q^3F3`, `A=F0+F1-q+1` and
`D=F2+F3-q+1`. The weakened source has positive witnesses exactly when
the following conditions hold:

- `q=3^t`, `W=3^m`, with integers `t>=2` and `0<=m<=t`;
- `D=6x+WA`, `A+D<q`, and `P` is even;
- the supplied fields are the literal first three base-q chunks and
  the remaining top chunk of `P`, with one of the four patterns below.

Put `N=4t`, and number ternary positions from zero, low first.

| Stratum | Ternary digits of P | Consequence |
| --- | --- | --- |
| Short | Exactly N digits; units2, all others1 or2 | A>=1, all four fields native |
| Long1 | Exactly N+1 digits; top1, units2; unique zero at t-1; next digit2; all other digits1 or2 | A<0 and D>=q |
| Long2 | Same, with unique zero at 2t-1 | A<0 and D>=q+1 |
| Long3 | Same, with unique zero at 3t-1 | A>=1; possible only when W=1 |

The consequences use the retained transport and joint bound, as well as
the listed digit pattern. In every admitted case **A is nonzero**.
Moreover **A<0 implies q<=D<6x**, so a negative-append witness bounds q
strictly in terms of the ordinary input. When W>=3, every positive-append
witness is in the short native stratum. The width1 exception cannot be
dropped from that last assertion. It nevertheless has `q<18x`, so every
nonnative case bounds q in terms of the ordinary input.

## 2. Kernel recovery and the endpoint t=1

The joint equation gives `sum Fi<=3q-3`, hence q>=3. This alone implies

    q^3+q^2+q+1 <= P < 3q^4,
    q^4 < P^2,  q^8>P+1,
    q^4(q^4+1)>12P,  6P/[q^4(q^4+1)]<1/2.

These are precisely the enlarged-range kernel bounds used in63. None
uses `I<W`. Thus the same rank, ratio, exponent and signed positive-branch
arguments give `q=3^t`, `q^4 | binom(2P,P)` and even P. Positive L gives
`W=3^m`, `0<=m<=t`; W=1 is now allowed.

At q=3, positivity of each field gives A,D>=0. Transport would then give
D>=6, contradicting A+D<3. Therefore t>=2 even without the width bound.
This also ensures that the final position of a q-block is distinct from
its units position in the arguments below.

## 3. Normalization and all four digit strata

Normalize with nonnegative carries:

    F0=U0+q*c0,
    F1=U1-c0+q*c1,
    F2=U2-c1+q*c2,
    F3=U3-c2,

where `0<=Ui<q` for i<3 and `U3=floor(P/q^3)`. With
`sigma=sum Ui`,

    sum Fi=sigma+(q-1)(c0+c1+c2).                       (1)

If P<q^4, the required N doubling carries force the short pattern.
Its minimum sigma is `4H+1`, where `H=(q-1)/2`. Any positive ci in(1)
would give `sum Fi>=6H+1`, contradicting `sum Fi<=6H`. Thus the supplied
fields are already the four normalized native chunks.

If `q^4<=P<3q^4`, there are N+1 ternary digits. The all-carry minimum
has sigma `3q-1`, already exceeding `3q-3`. Hence exactly one digit
position misses its doubling carry. The missed position is below N.
Except at units, its digit must be0 and its successor2. Relative to
the all-carry minimum, this moves one unit of positional weight from
that position to its successor. Within a q-block, and between the last
ordinary digit and the extra top digit, this increases sigma. A miss at
units also increases sigma. The only possible decreases occur at
`t-1`, `2t-1` or `3t-1`.

Even there `sigma>=3q-q/3`. Adding q-1 exceeds the joint field sum bound,
so (1) again forces every ci to vanish. Raising the top digit from1 to2
would raise sigma by q and likewise violate the bound. This proves
exactly the three long patterns in the table, with literal supplied
chunks and no remaining normalization carries.

For Long1, the read chunks satisfy `F2>=H,F3>=q+H`, hence D>=q.
For Long2 their bounds are `F2>=H+1,F3>=q+H`, hence D>=q+1.
The joint inequality then forces A<0 in both cases. Transport gives
`6x=D-WA>D>=q`, independently of W.

In Long3 the append chunks have not been altered: `F0>=H+1,F1>=H`,
so A>=1. The units digit of F3 is2, and the units digit of F2 is1 or2.
Since `q-1=2 mod3`, this gives `D=1 or2 mod3`. If W>=3, transport instead
gives `D=6x=0 mod3`, a contradiction. For W=1 there is no such
contradiction, and Long3 genuinely occurs. This proves every sign and
endpoint assertion.

For that width1 exception, Long3 also gives `D>=q-q/3+1`. Now `I=D-A`
and `A+D<q` imply

    I>2D-q>=q/3+2,

so `q<3I=18x`. Together with `q<I` for negative A, this makes every
nonnative stratum a finite search for each fixed positive x. This is
only a bound on those exceptional strata, not on native witnesses.

## 4. Positive converse and concrete witnesses

Conversely, take positive parameters satisfying the classification.
Every listed pattern has exactly N ternary doubling carries, so its
central binomial coefficient is divisible by q^4. The enlarged bounds
in Section2 hold, and even P gives `J=2P+1=1 mod4`.

Apply the full seventeen-coordinate positive map in
[Section5 of the selector proof](native_controller_three_selector_53.md)
with `D0=q^4,r=P`: `X=3^J`,
`Y=floor((X+1)^(2P)/X^P)`, `w=X/D0`, `s=Y/D0`, and the stated Pell
recurrences, quotient coordinates and half-parameter witnesses. The
power and binomial divisibilities make w,s integral and positive. The
same canonical ratio interval, congruences and growth bounds make all
remaining coordinates integral and strictly positive. That map uses
the kernel bounds and parity, not the assumption `P<D0`; here they hold
throughout `P<3D0`. Set `alpha=q-A-D` and `L=q/W`. Both are positive,
and all retained equations follow. No beta coordinate remains.

Three small full weakened-source examples are:

| q | W | x | Fields | P | A | D | Stratum |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 9 | 9 | 3 | (2,5,4,13) | 9848 | -1 | 9 | Long1 |
| 9 | 1 | 1 | (5,4,1,14) | 10328 | 1 | 7 | Long3 |
| 27 | 3 | 1 | (14,13,22,13) | 272282 | 1 | 9 | Short |

The first belongs to a parametric negative-append family: for any t>=2,
put `q=3^t,W=9,H=(q-1)/2` and

    F=(H+1-q/3,H+1,H,q+H),
    x=2q/3-3, A=2-q/3, D=q, alpha=q/3-2.

All supplied values are positive, the packing is even, and it has its
sole missed carry at t-1. The map above supplies the full kernel.

## 5. Evidence

The [checker](pell_kernel_width_deleted_classification.py) compares the
four explicit digit strata with an independent factorial-valuation
calculation on every joint-bounded positive field tuple through q=27,
then checks all power widths and positive inputs in those tuples. It
also checks the displayed examples and eleven members of the parametric
family. The full positive kernel extension is a proof, not a numerical
construction of its astronomical coordinates. Default execution checks
the [receipt](pell_kernel_width_deleted_classification.json).
Independent full proof/source/default review passed, including every
carry-break stratum, the width1 exception and the enlarged positive
converse. No Lean formalization is claimed.

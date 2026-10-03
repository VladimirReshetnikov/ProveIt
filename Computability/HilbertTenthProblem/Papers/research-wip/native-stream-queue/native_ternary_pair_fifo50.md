# A paired ternary FIFO in 50 operations with an exact delayed loader

The [43-operation power-of-three geometry](pell_kernel_power_three43.md)
gives an ordinary-input paired ternary FIFO in **50=28M+22A**. Its initial
coordinates are **(x,0)**, its final coordinates are(0,0), and its alphabet
is all nine ordered pairs of trits. A fixed finite prefix converts its raw
input to the existing handoff machine's delimited input, without another
arithmetic initialization equation.

The prefix still belongs to the **unpaid finite controller**. This note
does not encode its table arithmetically or supply universal acceptance.
The complete universal bound remains76; there are25 operations available
below that bound for the missing controller and any further constraints.

## 1. Exact source and paired queue projection

Take positive parameters `x,W,q,D0,D1,A0,A1`, using executable names
`read0,read1,append0,append1` for the streams. Retain all seventeen positive
power43 coordinates. Supply positive `L,beta,alpha0,alpha1` and impose

    x+beta=W, q=WL,
    D0=x+W*A0, D1=W*A1,
    D0+alpha0=q, D1+alpha1=q.                            (1)

Beyond43 these require three multiplications and four additions, giving
50=28M+22A. There are17 equations,21 auxiliaries beyond the seven parameters,
or27 positive existential coordinates besides x. Every supplied coordinate
appears in the independent source polynomials.

The exact projection is: `q=3^t,W=3^m`, `t>=m+1,m>=1`, `0<x<W`; the
length-t native ternary expansions of the four positive stream integers
give a synchronized paired queue run, with both append streams nonzero,
initial coordinates(x,0) and final coordinates(0,0). Each coordinate obeys

    d_j=N_j mod3,
    N_(j+1)=floor(N_j/3)+(W/3)*a_j,
    0<=N_j<W.                                          (2)

For soundness, power43 gives q=3^t, and q=WL makes W a power3. The input
bound implies W>x>=1, hence W>=3. Both read bounds are paid. Transport
then implies `0<Ai<q`. Every bounded integer has its ordinary length-t
ternary expansion; no Boolean filtering or radix conversion is involved.
Since A1>0, D1>=W; D1<q forces t>=m+1. Successive reduction of each
transport identity modulo3 proves(2) and its zero endpoint. Both streams
use the same width and length, so the runs are synchronized.

Conversely, any stated paired run gives both transport identities by
telescoping. Set `beta=W-x,L=q/W,alpha_i=q-Di`. These are positive.
Power43 supplies its positive kernel independently of the streams, proving
the converse. In particular the zero initial second coordinate is a fixed
numeral, while its supplied read and append streams remain positive.

The bare component admits every positive input. Choose the least power
W of3 greater than x, put q=3W, and append(1,1) once followed by zeros.
After reading the m initial positions, both queues equal1; one more step
reads(1,1) and appends zero. The stream integers are

    A0=A1=1, D0=x+W, D1=W,

all positive and below q.

## 2. Same-cost joint-bound variant

Replace the two read slack equations in(1) by

    D0+D1+alpha=q, alpha>0.                             (3)

This still costs two additions, so the total remains50=28M+22A. It has16
equations and26 positive existential coordinates besides x. Its exact
projection adds the joint bound D0+D1<q. The separate-bound version above
keeps all runs satisfying the initial and terminal geometry; the joint
version is a stricter interface.

Both the bare witnesses just described and every genuine accepting
handoff computation after the prefix below obey(3). For the latter, the
last removed pair is the delimiter#=(0,1). Its digit sum is1, while every
earlier pair has digit sum at most4. Consequently

    D0+D1 <= 3^(t-1)+4*(3^(t-1)-1)/2 = q-2.

No extra accepting padding step is needed for that bound.

## 3. A finite delayed prefix supplies the old delimiter

Initially every second-coordinate trit is zero. Write the raw queue as

    (d0,0),(d1,0),...,(d_(m-1),0),

where the d_j are exactly the m trits of ordinary x. Let a plain symbol be
`plain(d)=(d,0)` and the delimiter be `#=(0,1)`. Add four live control
states: init, pending0, pending1, pending2. Their nonreject transitions are

| State | Read | Append | Next |
| --- | --- | --- | --- |
| init | plain(d) | # | pending d |
| pending v | plain(d) | plain(v) | pending d |
| pending0 | # | # | old initial control |

All other reads reject. There are thirteen nonreject rows: three in the
first family, nine in the second, and one in the last. This is a semantic
finite table, **not a thirteen-operation arithmetic encoding**.

The first step stores d0 and appends#. Every subsequent plain step emits
the previous stored digit and saves the current one. No other delimiter
is initially present or emitted during this scan. After exactly m steps,
the queue is

    #,plain(d0),...,plain(d_(m-2)),

and the stored digit is d_(m-1). The next transition is permitted exactly
when that digit is0, equivalently `x<W/3`. It removes# and appends#,
leaving precisely

    plain(d0),...,plain(d_(m-2)),#.

This is the original handoff machine's initial queue with its high marker
coordinate `W/3`, ordinary input x and physical width W. The old finite
normalizer and simulator can begin unchanged. No supplied marker coordinate
or equation `W=3K` is needed in the arithmetic source.

For every positive x, choose a power W with x<W/3. The prefix succeeds
in m+1 steps. Conversely, because(1) already guarantees x<W, its success
forces exactly the claimed input inequality and preserves every digit of
x. The paid input bound is substantive: without it, high digits beyond
the physical queue could affect the transport and this proof would fail.

The prefix already appends a nonzero second-coordinate digit. Since x>0
and its highest raw digit is zero on success, at least one lower digit is
nonzero and is emitted as a plain symbol. Thus both append streams are
positive; the corresponding read streams are positive too. The existing
handoff controller eventually erases every queue symbol in accepting
control and reads# last. Its positive stream and joint-bound contract
therefore survives adding this prefix.

This establishes a precise machine interface for the original universal
queue construction. Certifying these transitions and the old controller
at the same native time positions remains the arithmetic bottleneck.

## 4. A general affine carry schedule and its scope

For fixed integer weights c0,c1,c2,c3, offset h and endpoints cs,cf, the
native relation

    3k_(j+1)=k_j+h+c0*d0_j+c1*d1_j+c2*a0_j+c3*a1_j

telescopes to

    2 sum_i ci*Stream_i + (h-2cf)q = h-2cs.             (4)

Conversely, the global identity reconstructs every integral carry by
successive reduction modulo3, with the specified final endpoint. The
factor2 is absorbed into fixed coefficient numerals; no division or extra
variable operation is used. Four weighted stream products, their three
summation additions, one q product and one final addition cost9=5M+4A.
The combined source therefore costs **59=33M+26A**, with one additional
equation and no additional supplied positive coordinate.

Equation(4) describes the entire unfiltered affine graph on all four trits.
It does not certify the delayed prefix or any chosen finite transducer.
For an absorbing zero-label endpoint `h=2cf`, its q term vanishes. After
transport substitution the remaining condition is

    (Wc0+c2)A0+(Wc1+c3)A1+c0*x+cs-cf=0.

Together with positive append integers, W>x and W a power3, this is a
one-parameter Presburger condition. Sufficiently large q supplies the
read bounds, including the joint bound. The reviewed effective elimination
and power-orbit argument therefore decides this unrestricted absorbing
subfamily. A universal implementation needs additional certified structure
or a different controller; the nine-operation schedule alone is not one.

## 5. Evidence

The [source](native_ternary_pair_fifo50.py) audits both complete50 schedules,
all residuals and the inherited auxiliary norm correction, and both59
carry extensions with disjoint register names. It compares arbitrary
positive bounded stream tuples against direct paired FIFO execution,
checks bare witnesses for the first200 inputs, and exhausts the delayed
prefix on every positive raw word through physical width3^6.

The full kernel extension is the positive power43 theorem; the prefix
is a finite machine proof and checker, not an arithmetic controller.
Default execution compares the [receipt](native_ternary_pair_fifo50.json).
Independent full proof/source/default review passed, including both bound
variants, the exact delayed prefix, positive stream interface and full
affine carry schedule. No Lean formalization or complete universal bound
below76 is claimed.

# A complete uniform selected affine-pair history

For every fixed nonempty table

\[
 (U,V)\longmapsto(a_iU+c_i,b_iV+d_i),\qquad 0\le i<s,
\]

with positive integer slopes and nonnegative integer offsets, this packet
gives a complete arithmetic certificate for a **nonempty** common tile word
taking `(1,Vinitial)` to `(Ufinal,Vfinal)`. All three parameters and all
supplied witnesses are strictly positive. There is no supplied duration,
power relation, digit predicate, selector predicate, or multiplication of
selected cells left outside the certificate.

The [source](pcp_uniform_affine_pair_history.py) has two fully paid layouts
and chooses the shorter actual circuit. Both use **19 comparisons** and
**3s+26 positive witnesses**. If the certificate has `C=M+A` operations,
its literal sum-of-squares polynomial has `C+56`, comprising `M+19`
multiplications and `A+37` additions/subtractions. For the illustrative
three-tile table `(4,1,2,1),(2,0,4,2),(8,3,2,0)`, the selected interleaved
layout costs **161=77M+84A**, or **217=96M+121A** after polynomial
compilation, with 35 witnesses and degree 400. The contiguous alternative
costs 163/219 and has the lower degree 328.

This is a fixed-table theorem, not an instantiated numerical universal
PCP alphabet or an improvement to the established 75/88 bounds. It closes
the history interface required by the separately proved
[ordinary-input GPCP boundary](gpcp_fixed_program_input_bridge.md).

## 1. The scalar source and its positive domain

Let `K` be the least power of two at least

    max(8, s+4, 1+max_i(a_i+c_i,b_i+d_i)).                 (1)

This is a fixed compiler numeral. Its multiplication is paid. Supply

    height_slack, H_U, H_V, global_bound,
    Shat_i, ZUhat_i, ZVhat_i  (0<=i<s),
    the 22 disjoint auxiliaries of prescribed AND64.

Write `rho=height_slack`, `beta=global_bound`, and use decoded names
`S_i=Shat_i-1`, `ZU_i=ZUhat_i-1`, `ZV_i=ZVhat_i-1` in the proof. The
source usually computes their packed or weighted sums directly, without
paying for every individual subtraction. Compute

    D=Vinitial+Ufinal+Vfinal+rho;
    B=K*D;
    J=sum_i Shat_i-s;
    P=(B-1)*J+1.                                         (2)

These cost `s+7` operations before structural sharing. In particular `P`
and `J` are computed, not existential coordinates. Retain the one global
comparison

    H_U+H_V+sum_i ZUhat_i+sum_i ZVhat_i+beta=P.            (3)

The two transport comparisons are

    B*sum_i(a_i*ZU_i+c_i*S_i)+1=H_U+P*Ufinal;
    B*sum_i(b_i*ZV_i+d_i*S_i)+Vinitial=H_V+P*Vfinal.       (4)

For example the first weighted sum is literally evaluated as

    sum_i(a_i*ZUhat_i+c_i*Shat_i)-sum_i(a_i+c_i).

The last sum is a fixed numeral. Each nontrivial fixed-numeral
multiplication is charged. Zero terms and multiplication by one are
aliases; equal literal subexpressions may share a register.

The word-to-map helper uses fixed-width digit encodings. A nonempty word
`w` of width `k` appends by `z -> 2^(k*len(w))*z+value_k(w)`.
`maps_from_tiles` checks every digit and requires both words in every
tile to be nonempty. Its output has the dyadic slopes needed for PCP.
The arithmetic-history proof also permits arbitrary positive integral
slopes, and the receipt includes a nondyadic table.

## 2. One binary AND joins every typing obligation

Write `R_l(z)=1+z+...+z^(l-1)`. Every power and repunit below is computed
by the paid acyclic source. There is no varying-exponent instruction.

The **contiguous** layout sets

    R=R_s(P);
    S=sum_i S_i*P^i;       Mc=J*R;
    Hb=(H_U+P^s*H_V)*R;
    Mb=(B-1)*(1+P^s)*S;
    Zb=sum_i ZU_i*P^i+sum_i ZV_i*P^(s+i);
    ec=2s; er=3s; et=3s+2; N=3s+4.                      (5)

The **interleaved** layout instead sets

    R=R_s(P^2);
    S=sum_i S_i*P^(2i);    Mc=J*R;
    Hb=(H_U+P*H_V)*R;
    Mb=(B-1)*(1+P)*S;
    Zb=sum_i (ZU_i+P*ZV_i)*P^(2i);
    ec=2s; er=4s; et=4s+2; N=4s+4.                      (6)

The unused odd controller lanes in (6) are zero. This avoids a second
controller pack while retaining the same physical selection stream.
Neither layout pads the fixed tile count to a power of two.

In both layouts compute

    T=H_U+P*H_V;
    RM=(D-1)*J*(1+P);
    H=Hb+P^ec*S+P^er*T+P^et*B;
    M=Mb+P^ec*Mc+P^er*RM+P^et*(B-1);
    Z=Zb+P^ec*S+P^er*T;
    Scale=P^N.                                          (7)

`P^ec*S+P^er*T` is literally shared between `H` and `Z`.
Apply the complete [prescribed AND64](native_binary_masked_selection63.md)
to `(Scale,H+1,M+1,Z+1)`. The three conceptual `+1` wrappers are inlined:

    q_native=16*Scale;
    padded_A=16H+12;
    padded_B=16M+10;
    F3=16Z+8.                                            (8)

This is exactly the original 64-gate source after substitution, including
all 16 comparisons and all 22 positive auxiliaries. Its exact projection
is `Scale` a power of two, `0<=H,M<Scale`, and `H AND M=Z`. The low
four-bit padding provides all four strictly positive truth classes even
when some original words are zero. Its full positive Pell extension is
the one proved in the linked parent; finite trace fixtures are not a
replacement for that extension.

## 3. Soundness, with geometry established before digit semantics

Before using any comparison, positivity gives `D>=4`, `B>=32`,
`S_i,ZU_i,ZV_i>=0`, `J>=0`, and `P>=1`. All the packed expressions in
(5)--(7) are nonnegative: each hatted Horner pack minus its repunit is
exactly the pack of nonnegative decoded integers. Thus the conceptual
arguments `H+1,M+1,Z+1` and the computed `F3` in (8) are positive before
the native theorem is invoked.

At a zero of (3), `P>=2s+3>1`, so (2) gives `J>0` and `B<=P`.
Also each history and each decoded selected word is less than `P`.
The checksum definition gives `0<=S_i<=J`, whence

    (B-1)*S_i <= (B-1)*J = P-1.                         (9)

These are algebraic bounds before selector typing. Consequently the
physical regions `Hb,Mb,Zb` fit within `2s` base-`P` lanes. The controller
region has width `s` in (5), or `2s` in (6), and `0<=S<=Mc` lies strictly
below the corresponding power of `P`. Both `T` and `RM` are below `P^2`:
for `RM` use `(D-1)J<(B-1)J<P`. Finally `B<=P<P^2` and `B-1<P^2`.
Thus all regions in (7) are disjoint and fit below `Scale`. Two top
lanes are reserved deliberately: at duration one it is possible that
`B=P`, which would not fit into a single lane.

The native theorem first gives `P^N` dyadic, hence `P` dyadic. Binary
AND now splits across the disjoint base-`P` regions. In particular

    Hb AND Mb=Zb;   S AND Mc=S;
    T AND RM=T;     B AND (B-1)=0.                      (10)

The last identity and `B>0` imply that `B` is a power of two. Since
`B=KD` and fixed `K` is dyadic, `D` is a positive power of two as well.
The computed repunit relation in (2) now implies

    P=B^t,    J=1+B+...+B^(t-1),    t>=1.               (11)

For completeness of this elementary implication, write `B=2^b,P=2^p`.
The divisibility `2^b-1 | 2^p-1` implies `b|p` by division of exponents
and reduction modulo `2^b-1`; hence `t=p/b` is a positive integer.

The controller equation in (10) says separately that `S_i AND J=S_i`.
Each selector therefore has only 0/1 base-`B` digits at the `t`
positions. Since `sum S_i=J` and `s<B`, adding these digits cannot carry;
there is exactly one selected tile at every position. This argument
uses only the checksum, not any transport comparison.

The range equation in (10) gives each history digit in `[0,D-1]`:
`D-1` consists of its low bits and the successive copies in `(D-1)J`
occupy disjoint base-`B` cells. The physical equation then gives exactly
the chosen-cell products `ZU_i(j)=S_i(j)U(j)` and
`ZV_i(j)=S_i(j)V(j)`. The earlier strict bound on every selected word
prevents output-lane carries.

For `0<=u<D`, every candidate next state satisfies

    0<=a_i*u+c_i <= a_i*(D-1)+c_i < (a_i+c_i)*D < K*D=B, (12)

and similarly for the other coordinate. All four boundary digits
`1,Vinitial,Ufinal,Vfinal` are less than `D`. Both sides of each
transport (4) are therefore canonical base-`B` expansions. Equality
forces the initial digits, every selected affine update, and the final
digits. Starting at positive `(1,Vinitial)`, positive slopes and
nonnegative offsets ensure that all recovered states are positive.
This proves the required common nonempty tile word.

## 4. Strictly positive completeness

Given such a word of length `t>=1`, its two state sequences are
nondecreasing. Choose a dyadic `D>Vinitial+Ufinal+Vfinal`; this also
exceeds every state. Set `rho=D-Vinitial-Ufinal-Vfinal>0`, `B=KD`,
and use (11). Supply the histories of the `t` pre-update states,
the hatted Boolean selectors, and the hatted selected products.
Both histories are positive; every hat is at least one even for an
unused tile. All comparisons in (4) hold by telescoping digit positions.

Let `Hsum=H_U+H_V`. One-hot selection gives

    sum_i(ZU_i+ZV_i)=Hsum,
    beta=P-2*Hsum-2s.

As `Hsum<=2(D-1)J`,

    beta >= ((K-4)D+3)J+1-2s > 0.                     (13)

The strict inequality follows from `K>=s+4`, `D>=4`, and `J>=1`;
indeed the displayed lower bound is at least `2s+4`. This includes
duration one. All joined regions satisfy (10), and `Scale` is dyadic.
The full prescribed AND64 converse supplies the remaining 22 strictly
positive native witnesses. No shared native witness is reused from a
different scale or a different program.

The relation deliberately excludes the empty tile word. A nonempty
fixed table containing an identity tile can model an empty effect if
an application wants that different relation. The GPCP boundary used
here already excludes the empty common word. An empty fixed table is
rejected by the builder rather than silently supplied an identity tile.

## 5. Literal costs, exact degree, and replay

`build(maps,layout=...)` emits one named acyclic schedule. Its only
constant folds are arithmetic between fixed numerals, zero terms, and
identity operations; all other fixed-numeral operations are counted.
Binary exponentiation and recursive doubling compute the fixed powers
and repunits, and exact repeated instructions share registers. Each
comparison is a register pair, not an uncharged computed residual.
`polynomial_source` pays one subtraction and one square per comparison
and adds the 19 squares using 18 additions.

The exact table-dependent ledger is `64 + len(wrapper_source)`; both
M/A histograms and the literal DAG are in the
[receipt](pcp_uniform_affine_pair_history.json). `layout='auto'` compares
both emitted schedules, then breaks operation ties by the smaller scale
exponent and then by fewer multiplications. This claims the better of
these two implementations, not a global circuit optimum. The receipt
contains both alternatives for seven tables, including identity maps,
zero offsets, an eight-tile table, and nondyadic positive slopes.

For degree, give every supplied parameter and witness degree one. Then

    D*=Vinitial+Ufinal+Vfinal+rho;
    J*=sum_i Shat_i;
    P*=K*D*J*;             deg(P)=2;
    q_native*=16*(P*)^N;   deg(q_native)=2N.             (14)

The joined `H,M` have degree `2N-3`, with their nonzero highest term
from the top radix region. The joined `Z` has degree `2N-5`, from its
range region. All three nonnative residuals have degree at most three.
In the native source, the packed-index comparison has degree `8N-5`;
the first Pell residual uniquely has degree `12N+8`, with highest form

    w_native^2 * s_native^4 * k_native^2 * q_native*^6.  (15)

The other residual degrees are bounded respectively by
`2N,1,2N+1,2N+2,1,4N+3,4N+2,2N+1,4,6,10,2,2N-3,2N-3`
in their source order after omitting the packed-index and first-Pell
positions. These bounds use supplied independent native `a,c,r,...`;
no zero-set substitution propagates a comparison into a degree claim.
Since `N>=7`, (15) strictly dominates. The SOS therefore has exact degree

    24N+16,

with highest form `w_native^4*s_native^8*k_native^4*q_native*^12`.
All supplied variables retain degree one even when a fixed coefficient
is large.

The author writer checked 896 complete arbitrary-assignment residual
and polynomial identities (672 positive and 224 signed), against a
separately assembled wrapper and the original hatted AND source. It
also checked 448 independently built genuine outer traces, including
duration one and unused tiles, and six exact weighted residual-degree
audits. The scalar outer fixtures instantiate the binary truth fields
but leave the large Pell core as placeholders; their scope is explicitly
not full numerical Pell zeros. The full native extension and the
arbitrary-duration equivalence are proved above.

Independent final proof/source/default reviews by `reduce_complete75`
and `substrates` both passed without findings. The former additionally
checked 480 signed complete-output identities and 240 genuine outer
histories on separate tables. The latter checked 128 independently
generated outer traces and 2,048 canonical-digit transport cases,
rejecting every altered bad history. Both reviews include the full
positive extension and the duration-one region bounds; their additional
finite fixtures are expressly outer checks, not numerical Pell zeros.

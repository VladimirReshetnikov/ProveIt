# A fixed-width recoder with two paid width operations

For every fixed integer k>=3, the complete positive relation
`z=spread_k(x)` with an existential dyadic input duration has a
**192=94M+98A polynomial**, **40 positive existential coordinates**,
and degree **at most303**. Its certificate has **148=79M+69A operations
and15 comparisons**. The operation count and this conservative degree
bound are independent of k. The fixed numerals still depend on k, and
every use of them is charged.

Two gates replace the binary multiplication chain for q^k:

    Q=q+power_gap,    R=(2^k-1)*J,

where `power_gap` is a new positive witness. The existing population
geometry now receives scale Q and index R. The repunit equations then
force Q=q^k; this is proved below, not assumed from a supplied exponent.
The [source](native_binary_population_width_recoder.py) and
[receipt](native_binary_population_width_recoder.json) contain the raw,
native-unit and normalized-strong forms. No new universal tag composition
or universal arithmetic bound is claimed in this packet.

## 1. The exact relation and literal change

The positive parameters are x,z. Every full positive zero has an integer
n satisfying

\[
\begin{gathered}
 n\ge2,\quad n\text{ is a power of two},\quad 0<x<2^n,\\
 z=\operatorname{spread}_k(x)
   =\sum_{j<n}\operatorname{bit}_j(x)2^{kj},\\
 q=2^n,\quad Q=2^{kn}=q^k,\quad B=2^{k-1}Q,\\
 P=B^n,\qquad J=\sum_{j<n}B^j,\qquad
 K=\sum_{j<n}(2B)^j,\qquad \mathrm{duration}=n.       \tag{1}
\end{gathered}
\]

Conversely, every x,n satisfying the first line has a full positive
extension with exactly these outer values and output. Thus this is the
same ordinary-input graph and dyadic-duration relation as the
[previous recoder](native_binary_dyadic_duration_recoder.md), including
its public Q and Q-1 interface.

Start with that literal raw source at k>=3. Delete its private q^k
multiplication chain and compute

\[
 Q=q+g,\quad R=(2^k-1)J,\qquad g>0.                 \tag{2}
\]

Keep `B=2^(k-1)*Q` and all outer, selected-AND, extraction and output
operations. Only the geometry consumers change: its old scale q becomes
Q and its old index J becomes R. In particular its paid bounds become

    R+geo_bound_beta=geo_w*Q,    B+geo_index_beta=R.  (3)

The source checks every old scale/index consumer and the private power
registers before this substitution. It updates the geometry comparison
as well as its source operands. The outer J is retained in all repunits,
input copies and duration equations. This is not an off-zero identity
with the old source, nor an assertion that its old geometry witnesses
can be kept.

The raw positive witnesses are the old52 coordinates and g. Write
`ell=duration`, `v=duration_quotient`, `h=duration_slack`, and put
`S=qP`, `H=xJ`, `A=Ahat-1`. The five old outer comparisons and two
extraction comparisons remain exactly

\[
\begin{aligned}
 (B-1)J+1&=P,&(2B-1)K+1&=qP,\\
 x+\mathrm{input\_slack}&=q,&
 Ahat+Q&=(Q-1)\mathrm{quotient\_hat}+z+2,\\
 z+\mathrm{output\_slack}&=Q,\\
 (B-1)v+\ell&=J,&\ell+h&=B-1.                     \tag{4}
\end{aligned}
\]

Both ratio slacks, the strong auxiliary norm and the auxiliary
congruences of the geometry kernel remain present.

## 2. Positive bootstrap and the two native kernels

At a raw positive zero, the input bound gives q>=2. Equation (2) gives
Q>q and the fixed radix multiplication gives

\[
 B=2^{k-1}Q\ge12,\qquad R>B>Q,\qquad R\ge13.       \tag{5}
\]

The strict R bound is the paid second equation in (3). The
[raw geometry theorem at index at least9](native_binary_input_dilation129.md#2-the-raw-geometry-theorem-at-j9-and-jq)
applies with its scale parameter equal to Q, index equal to R and shared
bound equal to B. Its exact hypotheses are R>B, R>=9 and R>Q, all supplied
by (5). It yields

\[
 R\text{ odd},\qquad Q=2^{\operatorname{popcount}(R)}.              \tag{6}
\]

This is the direct raw47 theorem, with its full positive converse. No
transport to a domain B>=8Q^2, unsigned norm assumption, or prior typing
of the AND operands is used. In particular Q and hence B are dyadic.

Independently, the unchanged prescribed-scale AND receives

\[
 (BH+\ell)\mathbin{\mathrm{AND}}(BK+\ell-1)=BA
 \quad\text{at scale }BS=BqP.                      \tag{7}
\]

Its conceptual positive hats are
`BH+ell+1`, `BK+ell` and `B*(Ahat-1)+1`.
They are positive on every positive supplied tuple, before any
comparison holds. The fused source still computes
`F3=16B*(Ahat-1)+8>=8`; the other restored hats and prescribed scale
are likewise positive. The complete AND theorem therefore applies
without circular range assumptions. It gives (7), the corresponding
strict range bounds, and dyadic BS. Since q and P are positive integer
factors of BS, they are dyadic too. No untyped product has been split
into dyadic factors before this theorem supplies that conclusion.

## 3. Population determines the width; the second repunit determines time

Write B=2^b. The first comparison in (4) says
`2^b-1` divides `P-1`, where P is dyadic and P>=B. The elementary
identity

    2^a-1 divides 2^c-1  iff  a divides c

therefore gives an integer n>=1 with

\[
 P=B^n,\qquad J=1+B+\cdots+B^{n-1}.                 \tag{8}
\]

Because Q>=3 and k>=3, B>2^k. Hence the multiplier `2^k-1` in
R=(2^k-1)J occupies k one bits in each of n disjoint b-bit cells.
There are no carries or overlaps. Consequently

\[
 \operatorname{popcount}(R)=kn,\quad
 Q=2^{kn},\quad b=kn+k-1>n.                         \tag{9}
\]

If n=1, then R=2^k-1<B, contradicting (5). Thus n>=2. This excludes
the one-cell repunit without an additional comparison.

It remains to synchronize the still independent dyadic q with n. Write
q=2^e. Since q>=2 and q<Q<B, we have `0<e<b`. The second comparison
in (4) gives an integer m>=1 with

\[
 qP=(2B)^m,\qquad e=(b+1)m-bn.                     \tag{10}
\]

If m<=n-1, the latter expression is at most `n-b-1<0`. If m>=n+1,
it is at least `b+n+1>b`. Both contradict `0<e<b`. Therefore m=n,
e=n, and

\[
 q=2^n,\qquad Q=q^k,\qquad
 K=1+2B+\cdots+(2B)^{n-1}.                         \tag{11}
\]

This argument is why the positive gap in (2) is retained. Typing two
independent powers of two would not by itself synchronize the repunits.

Finally, (8) gives J=n modulo B-1. The last comparison in (4) places
ell in `[1,B-2]`, and (9) implies `2<=n<B-1`. The other extraction
comparison therefore forces ell=n. The quotient `(J-n)/(B-1)` is
strictly positive since n>=2 and the term B-1 already occurs in J-n.

## 4. Dyadic duration, dilation and unique output

Now B is dyadic and `1<=ell<B-1`. The exact block identity is

\[
 (BH+\ell)\mathbin{\mathrm{AND}}(BK+\ell-1)
 =B(H\mathbin{\mathrm{AND}}K)
   +(\ell\mathbin{\mathrm{AND}}(\ell-1)).             \tag{12}
\]

The final summand lies between0 and B-1. Comparing (12) with (7), whose
right side is divisible by B, makes that summand zero. Hence ell=n is
a power of two and `A=H AND K`. This does not assume an output-lane
bound in advance; the native range bound also gives A<S afterwards.

By the paid input bound, `x=sum_(j<n)x_j 2^j`. Its copies in H=xJ
begin at positions bi and cannot overlap because b>n. The selected
positions of K are `(b+1)j=bj+j`, so they select exactly bit j of copy j:

\[
 A=\sum_{j<n}x_j2^{(b+1)j}
   =\sum_{j<n}x_j2^{k(n+1)j}.                       \tag{13}
\]

Modulo Q-1=2^(kn)-1, this has residue

\[
 Z=\sum_{j<n}x_j2^{kj},\qquad
 0<Z\le\frac{Q-1}{2^k-1}<Q-1.                      \tag{14}
\]

The penultimate outer comparison in (4) is exactly
`A=(Q-1)*(quotient_hat-1)+z`; the output bound places z in `[1,Q-1]`.
The nonzero residue (14) is unique there. Thus z=Z and the entire
soundness contract (1) follows.

## 5. Full positive converse and unit projections

Fix dyadic n>=2 and positive x<2^n. Define q,Q,B,P,J,K by (1), R by
(2), and A,z by (13)–(14). Choose

\[
\begin{aligned}
 g&=Q-q,\quad Ahat=A+1,\\
 \mathrm{input\_slack}&=q-x,\quad
 \mathrm{output\_slack}=Q-z,\\
 \mathrm{quotient\_hat}&=(A-z)/(Q-1)+1,\\
 \ell&=n,\quad v=(J-n)/(B-1),\quad h=B-1-n.           \tag{15}
\end{aligned}
\]

These are all positive integers. The shifted quotient remains necessary
when x=1, for which its unshifted value is zero. Its integrality follows
from (14), and A>=z follows term by term. The inequalities for v,h
were proved above; g>0 follows from k>=3 and n>0.

The new geometry index R is odd, exceeds B>Q, and has population kn.
Thus (6) holds at the **new scale Q and new index R**, so the full raw47
converse supplies all19 positive geometry auxiliaries. In particular
its index slack is R-B>0. This reconstructs its ratio, Pell and strong
auxiliary coordinates; it does not reuse the old geometry at scale q
and index J.

All joined-AND inputs are the same genuine outer integers as in the
previous recoder at this duration. We have H<S and K<S, ell<B, and
`0<=BH+ell<BS`, `0<=BK+ell-1<BS`. Equation (12), with dyadic ell,
gives the required output BA. The prescribed dyadic scale BS and the
complete AND converse supply all22 positive AND auxiliaries. The two
native sets are disjoint, so their positive extensions coexist. Together
with (15) this supplies every raw witness.

The optional [native-unit rewrites](native_binary_dyadic_duration_units.md)
apply to the literal changed source. Their seven-factor product contains
six norm factors which exclude minus one unconditionally, and the single
unrestricted AND checksum. Product one forces every factor to one before
any native typing theorem is invoked. The retained outer residuals are
handled by the same safe product finalizer. No second unchecked checksum
or signed native norm is silently added.

Their coordinate projections remain positive: the restored q is
`x+input_slack>=2`, Q adds the positive gap, B>1, and the restored
P=(B-1)J+1 is positive before typing. R is a positive fixed multiple of
J. The fused AND F3 and its packed native index retain the same positive
expressions. All remaining positive definitions and odd-root-gap
restorations use the unchanged literal kernel identities. There are13
fewer supplied coordinates, hence40 rather than53.

The normalized option additionally uses the two proved strong factors
`f^2-Delta*(i*c^2)^2`. Each also excludes minus one on every integer
tuple. Its zero restores the old strong relation by `i_old=Delta*i`.
The positive converse reconstructs only f,i,j,o,y in each core at its
own actual odd native index, exactly as in the parent normalization.
The source's dependency audit checks that those ten coordinates touch
no gap, repunit, joined port, duration, output or checksum. All these
restoration arguments precede the new raw synchronization proof.
They preserve the positive zero projection; normalization is not claimed
to be an arbitrary off-zero polynomial identity with the raw source.

## 6. Paid ledgers, conservative degrees and evidence

For k>=3 the old raw certificate cost `136+mu(k)`, with mu(k) paid
multiplications for q^k. The new definition adds one multiplication and
one addition, giving138. It adds exactly one positive witness and no
comparison. The fixed coefficient in R is `2^k-1`; the already retained
radix coefficient is `2^(k-1)`. Neither multiplication is free.

|Form|Certificate M+A|Certificate total|Comparisons|Positive witnesses|Polynomial M+A|Polynomial total|Degree bound|
|---|---:|---:|---:|---:|---:|---:|---:|
|Raw SOS|69M+69A|138|36|53|105M+140A|245|52|
|Native units|75M+69A|144|17|40|92M+102A|194|195|
|Normalized strong units|79M+69A|148|15|40|94M+98A|192|303|

The former normalized recoder had `190+mu(k)` operations and39
positive witnesses. The new192 count trades one extra positive witness
for removal of the width-dependent chain. At k=3 or4 the costs tie; the
saving is `mu(k)-2` for other widths. The width2 recoder is unchanged
and outside this packet's contract.

The degree column comes from direct propagation through the entire
actual polynomial DAG: degree adds at multiplication and is bounded by
the maximum at addition or subtraction. No cancellation is used, and
none of these numbers is claimed exact. The two fixed width numerals
have degree zero, so the bounds are independent of k. A future larger
composition needs its own source, positive-interface and degree audit.

The public `rewrite(old,repeated_mask)` checks all old power and
geometry consumers. The mask must mean exactly `2^width-1`; a caller
using a formal fixed-numeral atom must preserve that definition. The
metadata records zero power-chain gates and two width-constraint gates.
No source evaluator treats the fixed mask as another program coordinate.

Author checks include384 independent raw residual/SOS identities and256
complete unit-correction/output audits,320 of these on signed tuples;
205 genuine outer fixtures, including65 dyadic and140 non-dyadic cases;
and325 independently enumerated repunit candidates. Eighteen literal
ledgers cover six widths and all three forms. Non-dyadic fixtures test
that precisely the low-bit predicate rejects that duration. These are
outer and polynomial checks, not materialized full Pell zeros.

The independent prototype audit reconstructed every raw residual and
SOS on320 assignments across widths3,4,7,16,64, and checked320 complete
unit corrections across both options. It separately verified320 exact
population/outer families, including the excluded n=1 boundary, and
41,360 second-repunit exponent candidates. The final source is audited
against that same two-gate construction. Full positive native extensions
are established by the parametric theorem and converse above.

Author writer and fresh replay passed. Root and native-controller final
proof/source/fresh-default reviews passed without findings. The latter
added 192 complete nine-factor/residual/output identities, including 96
signed cases at widths 3,5,9,17,65,257, and 21 fixed-source-shape and
uniform-degree checks. Root separately checked six weighted polynomial
specializations below the stated conservative degree bounds.

```sh
python3 native_binary_population_width_recoder.py
```

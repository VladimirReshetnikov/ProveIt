# Parity-aligned raw counter histories in 76, 77, and 78 operations

The zero-target interface permits complete time frames to be derived from
the decoded counter parities. Removing the redundant frame equation then
exposes a common factor in the time equation. The resulting complete
bounded components have:

| Registers | Operations | Multiplications | Additions/subtractions | Positive unknowns | Equations |
|---|---:|---:|---:|---:|---:|
| One | 76 | 37 | 39 | 31 | 21 |
| Two | 77 | 38 | 39 | 32 | 22 |
| Three | 78 | 39 | 39 | 32 | 22 |

The input is [2x,0,...,0] for a positive raw parameter x, with x+x charged.
Every counter moves by +/-1 at each time step, stays nonnegative, and ends
at zero. The first register's first step is plus. These are counted history
components, not universal program certificates. All positive x admit some
such unrestricted histories; machine control and zero-branch routing are
still separate obligations.

The exact source, primitive schedules, and receipts are
`../verification/explore_parity_aligned_raw_counters.py/.json`.
The single-register 77 predecessor and the frame-guarded two/three-register
80/81 predecessors remain frozen in `EXPLORATION_RAW_TERNARY_ZERO_TARGET.md`
and `EXPLORATION_SIMULTANEOUS_RAW_TERNARY_COUNTERS.md`.

## 1. Exact source changes

For a fixed register count k>=2, start with the frame-guarded system and
remove the positive unknown Htime and its equation

    Htime(W-1)=2J.

Retain all the other equations, in particular

    q=2J+1, q=Wv, W=R^k, H(R-1)=2J,
    2x+alphaI=R.

For k=1 use the original single-register system with R understood as W;
there is no new R unknown, W=R equation, or extra power computation.
The head geometry still is H(W-1)=2J in this case.

In every case put A=F0+F1-2J, delta=FKplus-FKminus and I=2x. Replace
the evaluated time expression by its exact factorization

    W(A+delta)=A-I.                              (1)

Its residual is identically the old one:

    W(A+delta)-(A-I)=I+(W-1)A+W delta.

No witness change or divisibility assumption is used for this identity.
The computed sides may be signed before decoding; all supplied unknowns
remain positive. The six masked fields remain

    FKplus,G0,F0,G1,F1,FKminus,

with their same equations

    FKplus+FKminus=2J+H, 3T=2J+H,
    F0+F1+alpha=q+J, G0=F0+T, G1=F1+T.

The direct mask still has r=P, D0=q^6 and the same fixed plus-sign
43-operation kernel. All retained source equations and the sole acyclic
relaxed-norm correction are unchanged. The checker compares every fresh
polynomial source with the full new instruction list.

## 2. Preliminary range survives removal of Htime

The paid input equation 2x+alphaI=R gives R>=3. For k=1 the same assertion
holds for W. Thus H(R-1)=2J gives 0<H<=J without using Htime. The two
positive pair sums give every base and control field less than 3J;
0<T<=J and the two guards are less than 4J. Hence the same pre-mask bound
holds:

    q^5<P<3(q^6-1)/2.

All general-scale kernel hypotheses D0>=81,r>=27,r<2D0,D0<r^2 follow
exactly as in the predecessors. The fixed plus-sign kernel's soundness
does not require even r. It first recovers q as a power of three, and
the direct unit-two mask then recovers all six native fields. The first
control field decodes before the adjacent guard/base pairs, so no
unproved frame or field typing was used in this argument.

Since R^k=W divides q for k>=2, R=3^m for m>=1. H(R-1)=q-1 then implies
q=R^u for a positive integer u. At this stage u is only the number of
counter blocks. There is no claim yet that it is a multiple of k. The
equation q=Wv=R^k v gives u>=k, which ensures every register has at least
one stored source block. For k=1 the same statements follow directly
from the retained single-register geometry.

Native flags decode to complementary Boolean head words Kplus+Kminus=H.
Also T=(R/3)H, and the native guards force each of the two numerical tracks
to have a zero highest digit in every R-block. Therefore

    A=sum_(b=0)^(u-1) a_b R^b,
    delta=sum_(b=0)^(u-1) epsilon_b R^b,
    0<=a_b<R/3, epsilon_b in {-1,+1}.             (2)

This is an interpretation of u blocks, even if u would end in a partial
time frame. Eliminating that possibility is the next step, not a premise
of (2).

## 3. All k residue chains, including a possible partial last frame

Expand the residual of (1) in base R using W=R^k. Its first k coefficients
are

    I-a_0, -a_1, ..., -a_(k-1).

The paid bound 0<I<R and (2) make their absolute values less than R.
Reduction modulo R, followed by division and another reduction, proves
that they are all zero. Thus the initial values are [2x,0,...,0].

For k<=b<u, the coefficient at R^b is

    a_(b-k)+epsilon_(b-k)-a_b.                   (3)

Its absolute value is at most R/3<R. Continuing the same induction proves
every ordinary update in each residue class b modulo k. This statement
does not need u divisible by k.

There are exactly k final coefficient positions u<=b<u+k. Because u>=k,
each has a source a_(b-k) and control epsilon_(b-k); there is no remaining
-a_b term. Its coefficient is

    a_(b-k)+epsilon_(b-k).                       (4)

It lies in [-1,R/3], so its absolute value is less than R as well. The
same coefficient induction makes all k values in (4) exactly zero. These
are the final values of all k residue chains, one each. Their order may
be cyclically rotated relative to the initial counter order if u is not
a multiple of k, but all are zero, so no endpoint or partial-output term
has been discarded. Nonnegative source values and these zero endpoints
also exclude a decrement of zero anywhere in a chain.

Write u=kt+s with 0<=s<k. The chain for counter i has length

    ell_i=t+1 if i<s, and ell_i=t if i>=s.

All ell_i are positive because u>=k. Each chain starts at an even integer
and ends at zero through ell_i changes by +/-1. Therefore every ell_i is
even. If 0<s<k, both consecutive lengths t and t+1 occur, and cannot
both be even. Hence s=0, k divides u, and the common height t is even.
For k=1 this says the sole height u is even, with no divisibility issue.

This proves q=W^t and constructs the removed positive witness

    Htime=(q-1)/(W-1)=1+W+...+W^(t-1).

Consequently every accepting solution of the new system extends to the
frame-guarded predecessor. Conversely, deleting Htime from any predecessor
solution is valid. The two systems define the same complete history
relation; Htime's deletion has now been justified mathematically rather
than only by its absence from the output.

## 4. Positive witnesses and the fixed-sign parity requirement

Take any simultaneous nonnegative history from [2x,0,...,0] to all zero,
with every counter moving by +/-1 at each time and with the required first
plus sign. Choose a sufficiently large power R=3^m, form W=R^k and q=W^t,
split every ordinary ternary block value into two Boolean tracks, and
construct the native fields, top guards, and complementary signs as in the
predecessor. The same bounds give positive alpha and alphaI. Delete Htime;
the factored time equation holds identically.

Each true history has even t, so the number of counter heads u=kt is even.
The six-field parity identity is

    P=FKplus+FKminus+G0+F0+G1+F1
      =2J+H+2(F0+F1)+2T=H=u modulo 2.

Thus r=P is even. Its native unit-two mask gives D0-divisibility, and all
general-scale bounds hold. The fixed plus-sign kernel's positive converse
supplies the remaining Pell witnesses. Soundness in Section 2 did not
assume this parity before decoding; only the converse uses it after an
actual history has been constructed. The argument remains noncircular.

## 5. Why the even initial values and zero target cannot be dropped

Both conditions are substantive. The checker records two explicit full
outer examples with k=3 and u=4, so q=R^4 is not a power of W=R^3.
Both have native six-field masks with an even packed index, satisfy every
general-scale inequality, and therefore have all positive Pell auxiliaries
by the fixed plus-sign converse. They are counterexamples to the indicated
relaxations, not to the system just proved.

First let R=9, W=R^3, q=R^4 and weaken the input bound from I<R to I<W.
Take raw input I=R+R^2=90=2x, and the four source blocks and signs

    a=[0,1,1,1], epsilon=[+1,-1,-1,-1].

The initial vector is [0,1,1], whose higher counter values are odd, even
though the aggregate input integer is even. The residue chains have
lengths [2,1,1] and all end at zero. Writing A=R+R^2+R^3 and
delta=1-R-R^2-R^3 gives

    I+(W-1)A+W delta=0.

The input bound I<W has a positive slack. All source block values are
below R/3, so their track and guard fields are native. Yet Htime cannot
be an integer: W-1 does not divide q-1. Thus an arbitrary even *packed*
input is insufficient; the original bound loading exactly [2x,0,...,0]
is what supplies evenness in every register.

Second keep the original initial vector [2,0,0], but permit a nonzero
output word. Let R=27, W=R^3, q=R^4 and take

    a=[2,0,0,3], epsilon=[+1,+1,+1,-1].

The counter-final values are [2,1,1]. The top coefficients begin at the
partial-frame boundary, so the encoded output word is the rotated word
F=1+R+2R^2. Direct substitution gives

    2+(W-1)A+W delta=qF.

All source values are below R/3 and the original block input bound holds,
but the chain lengths are still [2,1,1] and the frame is partial. Thus
zero target is essential to the equality-of-parities argument. A generic
output word cannot be read as a complete unrotated frame after omitting
Htime. Both examples retain u even, so their positive Pell extensions do
not rely on changing the fixed-sign kernel.

## 6. Exact cost and the k=1 boundary

For k>=2, after removal of Htime the old W-1 register is used only in the
unfactored time expression. That expression costs five operations:

    W-1, (W-1)A, W delta, I+(W-1)A, I+(W-1)A+W delta.

Equation (1) costs three:

    A+delta, W(A+delta), A-I.

This saves one product and one subtraction/addition. Removing the Htime
product saves another product. Relative to safe80/81, the totals become
77 for two registers and 78 for three. W=R^2 and W=R^3 are still charged
by their explicit one- and two-product chains.

For k=1, the original head geometry still needs W-1. It must be retained.
Only the other four time operations are replaced by the three operations
in (1), saving one product from the single77 predecessor and giving
76=37M+39A. No fictitious R or equality W=R is introduced.

The uniform formula is 76+ell(k) for a supplied multiplication chain of
length ell(k) computing R^k, with ell(1)=0 and the one-register alias just
specified. It is a count for that chain, not a claim of optimal addition
chains for arbitrary k. All fixed numerals and equality comparisons remain
free; signed intermediates remain permitted.

The exact checker verifies every primitive and all source residuals for
the three explicit variants. It also checks the chain-length parity
identity for 2,134 pairs (k,u), k=2,...,12 and k<=u<=200, rejecting all
1,716 nonmultiple partial-length patterns. Its complete canonical samples
include fifteen single-register cleanup families, twenty-two joint
two-register histories and 104 joint three-register histories. The two
relaxed-interface counterexamples are checked through every outer equality,
full native mask, exact valuation and positive-kernel hypothesis. Large
Pell coordinates are not materialized; their existence follows from the
same general converse.

The construction leaves program lookup, branch tests and halting outside
the theorem. In particular the 78-operation three-register component is
an input/control interface on which to build; it is not a complete
universal representation.

# Exact obstructions for the nonabsorbing binary carry family

The paid [binary63 interface](native_binary_three_row_fifo58.md#7-a-paid-nonabsorbing63-interface-remains-separate)
has fixed signed integer coefficients a,b,c,g and the additional equation

    a A+b D+c q=g.                                      (1)

Here A=F1 is the append word, D=F2 is the read word, q=2^t,
W=2^m, I=2x, and x is the ordinary positive input. The underlying58
component imposes

    0<I<W, D=I+WA, A>0, D AND A=0,
    D<q, A<q, D even, A even.                          (2)

The disjointness and evenness in(2) are the physical prohibition of11 and
the compulsory first00 row. Set F0=q-1-D-A. Then F0>0, all three row
fields are positive, and the full positive58 converse supplies its26
existential coordinates. No additional sign-free state witnesses are
being treated as positive coordinates.

This note proves two parametric results. First, a coefficient cone is
necessary for unbounded input in the general63 family. Second, **every
specialization a=0 is decidable**, even when c is nonzero. The latter
statement retains the no11 guard and uses a proved width and duration
cutoff; it does not use free zero padding. No general classification for
a!=0 inside the cone is claimed. The separate
[fixed-idle57 theorem](binary_fixed_idle_controller.md) classifies the
boundary a=b!=0,c=-b.

## 1. An endpoint cone and a finite-width obstruction

The exact carry form of(1) is

    2k_(j+1)=k_j+a e_j+b d_j,
    k_0=-g, k_t=-c,                                    (3)

where d_j,e_j are read and append bits and d_j e_j=0.
Let K=max(abs(g),abs(a),abs(b)). Convexity of(3) gives abs(k_j)<=K.
The queue value N_j lies in[0,W), and

    2N_(j+1)=N_j-d_j+W e_j.

Combining these relations gives the useful invariant

    z_j=k_j+bN_j,
    2z_(j+1)=z_j+(a+bW)e_j.                            (4)

Ending with queue zero forces the last m appended bits to be0: they are
exactly the m bits still present at time t. Since A>0, necessarily t>m.
On these last m steps, equation(4) divides z by2, so

    -cW=z_(t-m)=k_(t-m)+bN_(t-m).                     (5)

Put J=[min(0,b),max(0,b)] and let delta be the distance from -c to this
closed interval. Since bN/W lies in J, equation(5) implies

    delta W<=K.                                       (6)

For fixed integer coefficients, delta is a nonnegative integer. Whenever
delta>0, every witness therefore has W<=floor(K/delta), and every input
has2x<W<=floor(K/delta). This is an effective finite-input obstruction.
For b=0 and c!=0 it applies with delta=abs(c).

There is also an effective decision procedure for each of these finitely
many inputs. At each allowed width, search the finite directed graph of
states (N,k,mask), with0<=N<W, -K<=k<=K, and an eight-valued mask recording
which rows have occurred. Require the first row00 and then search from
that forced first successor. Accept exactly when N=0, k=-c, mask=7.
The graph has at most8W(2K+1) states. A shortest accepting history has
at most that many steps, counting the forced first step. This graph
search is an exact decision, not a duration-limited experiment.

For b>0, the only cone not excluded is -b<=c<=0; for b<0 it is
0<=c<=-b. These are necessary, not sufficient, conditions. If a is odd,
a+bW is odd and(4) forces e_j=z_j modulo2. That deterministic scalar
orbit still has to pass the queue's no11 guard; this observation alone
does not decide the remaining family.

## 2. The read-only controller and its exact word criterion

Set a=0. Removing its zero multiplication and the redundant addition
specializes the extra schedule to two multiplications and one addition:

    bD+cq=g.                                          (7)

Thus this subfamily has a literal61=32M+29A schedule,18 equations and
the same26 positive existential coordinates. Fixed coefficients remain
program numerals. The decidability result does not add operations or
change those coordinates.

For a candidate pair m,t with t>m>=bit_length(I), equation(7) determines

    D=(g-c*2^t)/b                                      (8)

when b!=0. It gives a witness exactly when D is an integer and

    0<D<2^t, D modulo2^m=I,
    A=floor(D/2^m)>0, A even, D AND A=0.                (9)

These tests keep every physical restriction. In particular the first
read bit is0 because I=2x, and A even supplies the first append0.
Equations(8)--(9) provide all positive outer fields and the58 positive
converse then supplies the full arithmetic extension.

If b=0 and c!=0, the cone theorem already decides the language; directly,
q=g/c would also fix the only possible duration. If b=c=0, all positive
inputs are represented when g=0, and none when g!=0, by the bare58
coverage theorem. Hence it remains to decide b!=0.

## 3. A unique eventually periodic low read stream

Write b=2^nu B, where nu>=0 and B is odd, possibly negative. Durations
t<nu are finite cases. At every duration t>=nu, equation(7) requires
2^nu to divide g. If it does not, the finite short cases decide the
whole language. Otherwise put G=g/2^nu and T=t-nu, and split the read
word as

    D=U_T+2^T h, 0<=U_T<2^T, 0<=h<2^nu.

Equation(7) becomes

    B U_T+(c+B h)*2^T=G.                              (10)

Because B is odd, the low T bits U_T are the unique first T bits of
one infinite binary stream u. Construct it without any search:

    k_0=-G, u_j=k_j modulo2 in{0,1},
    k_(j+1)=(k_j+B u_j)/2.                            (11)

The integer carries lie in[-K',K'], K'=max(abs(G),abs(B)), so this
deterministic orbit has an effectively computable preperiod mu and
period p>=1, with mu+p<=2K'+1. Both its states and bits are periodic
after mu. Telescoping(11) shows

    B U_T=G+2^T k_T.

Thus the high-tail choice h is legal exactly when

    k_T=-(c+B h).                                     (12)

This gives a finite collection of ultimately periodic read-prefix
families followed by fixed nu-bit tails. It does not remove the
disjointness test in(9).

## 4. A proved width cutoff, including the eventually zero exception

Let ell=bit_length(I), and define

    M=max(ell,mu)+p+nu.                               (13)

If any history satisfies(7)--(9), one does with m<=M.
Short cases t<nu already have m<nu<=M. For a long history, suppose
m>M and put T=t-nu. Since t>m,

    T>m-nu>max(ell,mu)+p.

The low m bits of D equal I. Hence all u_j between ell and
min(m,T)-1 are0. This interval contains an entire period after mu and
all intervening preperiod bits. The stream u must therefore be0 at
every index j>=ell, and its infinite integer value is exactly I.
Equations(11) then give G=BI and eventual carry0.

Since m>ell, positivity of A now requires h>0; equation(12) gives
c=-Bh. Necessarily nu>0, because h<2^nu. The following explicit
replacement has the same ordinary input and coefficients:

    m0=ell+nu+1, T0=m0+ell, t0=T0+nu,
    W0=2^m0, D0=I+h*2^T0, A0=h*2^ell.                (14)

Here m0<=M because p>=1 and max(ell,mu)>=ell. Also
0<A0<2^(ell+nu)<W0; its bits lie strictly above those of I and strictly
below the high block h*2^T0. Therefore D0 AND A0=0. Its first read and
append bits are0, and(7) holds because g=bI and c=-Bh. All positive
conditions hold. This proves the width cutoff, including the case that
could otherwise permit arbitrarily long zero stretches in the low stream.

For odd b, nu=0, the exceptional h>0 case is impossible: every witness
itself already has m<=max(ell,mu)+p.

## 5. A proved duration cutoff with the no11 test retained

Fix any m. There is a witness at that width if and only if one exists
with

    m<t<=m+mu+2p+nu.                                  (15)

Finite cases t<nu satisfy this bound. For a long case write t=T+nu and
keep its fixed high tail h. If T<m+mu+p, the bound is already true.
Otherwise replace T by the unique T' in

    m+mu+p <= T' < m+mu+2p

with T'=T modulo p. This shortens T or leaves it unchanged.
Both T,T' exceed m and mu, so the initial I and first append bit u_m
are unchanged, and endpoint condition(12) is unchanged.

The guard D AND(D>>m)=0 says that no two1 bits of D occur at distance m.
It splits into three exact kinds of pair:

* Both bits are in U_T. For their lower index j, the pair is
  (u_j,u_(j+m)), over0<=j<T-m. After j>=mu this pair is periodic with
  period p. Both T and T' include the full preperiod and at least one
  complete period of these comparisons, so their truth values agree.
* The upper bit is the high-tail bit h_r and the lower bit is in U_T.
  This is the pair (u_(T+r-m),h_r) for0<=r<min(m,nu).
  Its lower index is at least mu; shifting T by a multiple of p
  preserves it exactly.
* Both bits are in h. Their disjointness is the fixed condition that
  h contains no two1 bits at distance m, independent of T.

These cases exhaust every prohibited11 pair. If h>0, A remains
positive. If h=0, the interval from m to T' already contains every
remaining transient bit and a full periodic block; it contains a1
whenever the corresponding longer interval did. Thus A remains positive
in that case too. All tests(9) are preserved, proving(15).

Combining(13) and(15) gives a terminating decider: test the finitely
many m with ell<=m<=M, and for each the finitely many t in(15), using
the exact integer conditions(8)--(9). When 2^nu does not divide g,
test only t<nu instead. These are proofs of finite search bounds,
not empirical claims about bounded experiments. No padding of an
already accepting physical history is used.

## 6. Evidence and remaining scope

The [checker](binary_nonabsorbing_cone_and_read_only.py) independently
implements the full finite queue/carry graph and the bounded read-only
word decider. It compares them at concrete widths, checks the coefficient
cone beyond its permitted width, and exercises high-tail and eventually
zero cases. Every reported accepting word is checked against the exact
positive FIFO projection and the global controller equation. The full
Pell witnesses are supplied by the58 converse, not materialized here.

The saved default run contains22,213 endpoint comparisons and5,116
comparisons of the full bounded decider. A separate set of240 histories
is generated as legal physical runs before choosing their coefficients;
their full graphs contain49,629 states in total. All240 receive valid
bounded replacements, including18 strictly shorter histories. Explicit
regressions cover a rational read word rejected solely by the no11 guard,
an eventually zero low stream with a nonzero high tail, a valid duration
shorter than nu, and the failure of free zero padding at a nonzero endpoint.

Independent full proof, source and default-replay review passed without
findings. It checked the endpoint cone, high-tail decomposition, exceptional
width replacement, all three guard-pair classes, preservation of positive
append streams, short durations, and the graph's compulsory first00.

The entire read-only family a=0 is therefore decidable and cannot represent
every recursively enumerable set by varying its fixed program numerals.
The general a!=0 family inside the cone is not decided here; its separately
classified fixed-idle boundary is linked above.
The complete universal bound remains75; the61 and63 schedules are local
arithmetic components, not new universal certificates.

# Sparse prime-payload universality with a paid power prefix

> Successor: [factored prime/action selections](residue_affine_sparse_factored.md)
> give551=193M+358A operations,67 witnesses and degree at most10052 with
> the same actual U21, fixed program recipe and paid ordinary-input prefix.
> This674-operation parent remains unchanged.

The [literal compiler](residue_affine_sparse_universal.py) completes the
prime-coded counter route with **674=249M+425A** polynomial operations,
**81 positive witnesses**, one positive program parameter and ordinary
positive input x. It has651 certificate operations, eight comparisons and
a conservative product-degree bound **10416**. The raw SOS alternative
costs705 with88 witnesses and degree at most1564. The
[receipt](residue_affine_sparse_universal.json) contains the complete
674-operation schedule and the actual fixed transition data.

The main gain is an explicit sparse implementation and a cheap *counting
relation within an already paid history*, not a new best universal bound.
Only36 branches and23 selected quotient classes are used. Expanding the
same deterministic body as a residue table would give223,092,870 rows.
The ordinary-input power is formed by an explicitly counted prefix of the
same chronology; there is no free exponentiation certificate or encoded
input parameter. This remains larger than the separate U9, Korec411 and
established75/87 constructions.

The deterministic body is a total residue-affine map. Its loader is a
separately paid branching prefix, whose length the input constraint fixes
uniquely. The final target is the body's fixed halting **control class**,
with its payload a positive existential coordinate. No claim is made that
the whole prefix is itself a deterministic residue map, that the endpoint
is a single cleaned integer, or that Collatz is universal.

## 1. Fixed universal body and its exact numerical map

Use the literal21-instruction, eight-register table in the
[reviewed Korec U21 compiler](korec_packed_counter_units.md), without
changing any target. Its instruction types are increment I, conditional
decrement D and pure positive test T. The primary source is
[Korec, *Small universal register machines*](https://www.cs.cmu.edu/~cdm/resources/Korec1996-small-universal-RM.pdf),
TCS168(1996),267–301: Main Theorem(a3), the strong input convention on
printed267–268 and Definition2.3, and the Section7 contraction of Figure1.
The retained table has8 I,12 D and1 T instructions. The existing table
proof records the original q27 zero target q29 rather than the conflicting
later transcription. This packet imports that frozen literal table and
stores it in its receipt.

Assign register primes

    (p0,p1,p2,p3,p4,p5,p6,p7)=(5,3,2,7,11,13,17,19).

For counters c_i define the positive payload v=product p_i^c_i. At a
body state, an increment multiplies v by its prime; a positive decrement
divides v by it; a zero branch requires nondivisibility and leaves v fixed.
A pure test has the same guards but leaves v fixed on both branches.
These rules are defined for every positive payload, not just prime-supported
ones. On prime-supported values they exactly simulate the counter vector.

The source numbers body states1 through21, with halt22. Choose the fixed
control modulus K=23 and encode a body configuration by

    n=K(v−1)+j,             1<=j<=K, v>=1.                (1)

For the halting and unused labels22 and23, define the total map's further
update as v→2v at the same label. These extra updates are not accepting
transitions of the compiler: acceptance asks whether22 is reached, and
the compiled body has no outgoing edge from22.

The map on all positive n is residue-affine of modulus

    M=K*product p_i=223092870.                            (2)

Indeed a residue modulo M fixes j and every divisibility guard on v.
Adding M to n adds product p_i to v. On each fixed branch the payload
slope is p_i,1/p_i or1, so its numerical slope per M-step is an integer.
For the positive residue convention1<=s<=M the exact table is

    f(Mq+s)=a_s q+d_s,
    a_s=M*(payload slope),       d_s=f(s)>0.              (3)

`residue_row(table, primes, s)` supplies any such row directly, without constructing the
other M−1 rows. The source uses the36 sparse branch records below instead
of these rows. It never assumes that a general residue map can be given
this sparse structure for free.

For a program index e supplied by Korec's strong-universality theorem,
fix the **positive program parameter E=3^e**. The ordinary input x will
be loaded as the exponent of2. This program recipe is a fixed computable
constant for each represented set; it does not change with x. The actual
initial counter vector after loading is exactly(0,e,x,0,...,0).

## 2. A three-gate count relation pays a variable power inside a history

Prepend a new control state0 and two increment-by2 payload edges:

    0→0: v→2v,              0→1: v→2v.                  (4)

No body edge targets0. The history starts at state0 with payload E and
must finish at body halt22. Exact chronological control therefore gives
one nonempty contiguous prefix of ell doubling steps, ending in the
unique exit0→1, followed by the deterministic body. The payload on entry
to the body is E*2^ell.

Let B be the common time radix, and let L be the sum of the two loader
selector words. Once the selectors have been typed, L is
1+B+...+B^(ell−1). Supply positive d_hat and impose

    L=(B−1)(d_hat−1)+x.                                  (5)

With the already paid B−1, this costs one subtraction, one multiplication
and one addition, plus one comparison. At ell=1 the correct quotient
is zero, represented by d_hat=1, so no input is lost.

A congruence alone would allow ell=x modulo B−1. The paid height includes
E,x and the final payload, making0<x<B−1. The chronological range proof
below makes every row's current and next payload strictly below B. In
particular the first body payload satisfies

    E*2^ell<B,    E>=1,   hence ell<B−1.                  (6)

Reducing L modulo B−1 in(5) gives ell=x exactly. Neither strict bound
is a guessed restriction on a valid run. They follow respectively from
the positive height definition and the already typed sparse history.
Conversely for any x>=1 the actual x-step prefix has
(L−x)/(B−1)>=0, so d_hat=1+(L−x)/(B−1) is positive.

This is a general growth/count lemma: the same proof works for a fixed
prefix multiplier a>=2 whenever its current/next values are below B.
It does not claim a standalone three-operation exponential predicate.
The two loader edges, their selector hats, the extra height summand x,
control chronology, ranges and the shared native core are all paid in
674. Only the additional count equation has the local three-gate cost.

## 3. Sparse local divisibility without a residue-table expansion

Write each branch as a pair of affine payload digits in a common
nonnegative quotient w. A zero branch has a remainder r in[1,p−1];
put rho=r−1 and sigma=p−1−r. On other branches put rho=sigma=0.
The branch rows are

|Kind|Current payload|Next payload|Remainder condition|
|---|---|---|---|
|I at prime p|w+1|p(w+1)|rho+sigma=0|
|positive D|p(w+1)|w+1|rho+sigma=0|
|positive T|p(w+1)|p(w+1)|rho+sigma=0|
|zero D or T|pw+1+rho|pw+1+rho|rho+sigma=p−2|

All w,rho,sigma are nonnegative, so these are exact local graphs. In
particular a positive decrement really has a divisible positive input;
a zero branch has residue1+rho strictly between0 and p. Primality is
used only for the connection to counter exponents; the emitted tests
are ordinary integer equations and bounded digits. The two prefix edges
are I branches at p=2.

Each row has a fixed coefficient pair(c_e,n_e) on w and positive
constant offsets(u_e,v_e), with rho added to both payloads. There are
24 distinct coefficient pairs in the default: (1,p),(p,1),(p,p) for each
of the eight primes. Choose one occurring baseline(c0,n0), and let g
count the remaining pairs. The default g is23. One selected quotient
word Z_a per exceptional class suffices for both payload forms; there
is no separate product for every edge.

Let E_e be nonnegative selector words, J=sum E_e, W the quotient word,
and R,S the rho/sigma words. With class selector G_a=sum_(e in class a)E_e,
define

    C=c0 W+sum_a(c_a−c0)Z_a+sum_e u_e E_e+R,
    N=n0 W+sum_a(n_a−n0)Z_a+sum_e v_e E_e+R.              (7)

Differences of coefficients may be negative; the pretyping proof does
not assume C or N nonnegative. After selection is typed, these words
have exactly the local digits in the table.

The remainder equation is

    R+S=sum_(zero branches e)(p_e−2)E_e.                  (8)

It is not merely a global remainder-sum test: three range lanes and the
one-hot selector proof make every term carry-free in the common radix.
Thus(8) holds separately in every chronological row, including p=2,
where the only nonzero residue is1 and both rho and sigma are zero.

## 4. Complete source, pretyping and chronology

There is a positive hat for every E_e,W,R,S,Z_a. Subtract1 to obtain
the displayed nonnegative words. Supply positive final payload F and
slacks eta,beta. Choose the fixed dyadic integer C_B at least

    max(4, number_of_edges+1, number_of_body_states+2, 1+max p_i).

The default C_B is64. The paid definitions are

    h=E+x+F+eta, B=C_B*h,
    J=sum E_e, P=(B−1)J+1, range_mask=(h−1)J.             (9)

Besides(5),(8), impose the global bound, payload transport and control
transport

    J+W_hat+R_hat+S_hat+sum Zhat_a+beta=P,
    B*N+E=C+P*F,
    B*following_control=current_control+(m+1)P.         (10)

Here m is the number of nonhalting body states. Current and following
control words are the exact fixed source/target-code sums;0 is the loader,
1..m are body states, and m+1 is halt. All coefficient multiplications,
including the endpoint factor(m+1)P, are paid.

One complete prescribed native AND joins these lanes in base P:

    (E_e,J,E_e)                 for every edge,
    (W,(B−1)G_a,Z_a)            for each exceptional class,
    (W,range_mask,W), (R,range_mask,R), (S,range_mask,S).   (11)

With b edges there are b+g+3 lanes,62 in the default. If H,M0,A are the
packed integers and a is the least power of two at least this lane count,
the prescribed scale is Q=B*P^a. The usual folded native ports are
q=16Q,16H+12,16M0+10,16A+8; all are positive before equations.

The global bound excludes J=0, since it would give P=1 while at least
four positive hats/slacks remain. Thus J>=1 and P>=B. It also gives
W,R,S,Z_a,J<P. Each E_e and G_a is at most J. Hence

    (B−1)G_a<=P−1,        (h−1)J<P,
    0<=H,M0,A<P^(b+g+3)<=P^a<Q.                         (12)

These inequalities are proved before any dyadic or digit conclusion.
The complete native theorem now yields dyadic Q and H AND M0=A.
Since B,P are positive factors of Q, they are dyadic; C_B is fixed dyadic,
so h is dyadic as well. From B−1 dividing P−1 and J>=1, write

    P=B^T, J=1+B+...+B^(T−1), T>=1.                     (13)

For completeness, if B=2^b0 and P=2^p0, reduce p0 modulo b0; the
remainder gives an integer2^r−1 between0 and B−2 divisible by B−1,
so r=0. There is no unproved power relation in(13).

The selector lanes make every E_e a bitwise subset of J. Since the
number of edges is below B, reducing sum E_e=J modulo B and iterating
forces exactly one selected edge at each time, with no carry. The three
range lanes give w_t,rho_t,sigma_t in[0,h−1]. Class lanes select exactly
the w_t digits belonging to each exceptional coefficient pair. Consequently
(7) gives the intended digit formulas.

The left side of(8) has digits at most2h−2<B. Its right side has digits
at most max p_i−2<B, by one-hot selection. Therefore every row satisfies
the stated complementary remainder condition. Its current/next payload
is positive and at most p_max*h<B. Both endpoints E,F are below h.
All source and target control codes are in[0,m+1] below B. Canonical
base-B comparison in(10) now proves every payload adjacency and every
control adjacency, the prescribed initial configuration and final halt.
There is no source edge from halt and no body target0, so an early halt
or re-entry into the loader cannot occur. This proves the contiguous
prefix hypotheses needed for(6), and(5) then proves that its length is x.

The native positive-scale, six-computed-field, normalized-strong and
coupled-index rewrites are the frozen complete helpers used by the
[134-operation residue-affine history](residue_affine_packed_history.md).
Their guarded dependencies do not involve an outer word or parameter.
The coupled form can normalize private native fields and the strong form
can reconstruct five private auxiliaries; these are accepted-outer
projection theorems, not all-coordinate positive bijections. The five
outer comparisons in(5),(8),(10) remain literal, paid comparisons in
every form. No new sign relaxation is needed for this sparse compiler.

## 5. Full positive converse and universal scope

Take any actual finite body run that halts after initialization with
payload E*2^x, and prepend exactly x doubling steps. Each branch has the
unique nonnegative quotient/remainders in Section3. Choose dyadic h
strictly greater than E+x+F and every occurring w,rho,sigma. Define B,P,J
by(9),(13) and pack the actual selectors and digits. Then eta>0 and all
supplied hats are positive, even if an entire quotient, remainder or
selected-product word is zero.

The exceptional classes are disjoint, so sum Z_a<=W. Moreover
W<=(h−1)J and R+S<= (p_max−2)J. The remaining global slack is

    beta=P−J−W−R−S−sum Z_a−g−3
        >=(B−2h−p_max+2)J−g−3>0.                      (14)

For the last inequality, C_B>p_max, C_B>b and g<=b−1 imply
p_max<=C_B−1 and g<=C_B−2, while h>=4 and J>=1. Its lower bound is
at least2C_B−6>0. Equation(5) supplies the positive quotient hat already
given in Section2. All outer equations and joined AND lanes hold. The
complete native theorem gives positive native witnesses, with fresh
canonical normalized witnesses as required. Thus every real halting run
has a positive solution of the emitted polynomial.

Conversely Section4 gives an actual prefix/body run from every positive
zero, and Section2 forces the prefix to be precisely x doublings. On a
valid program slice E=3^e the body therefore starts with prime exponents
(0,e,x,0,...,0), and prime multiplication/divisibility exactly simulates
the primary U21 table. Strong universality gives, for each recursively
enumerable set S of positive integers, a fixed E such that the default
polynomial has positive witnesses exactly for x in S.

No power condition is imposed on E for arbitrary parameter values; such
values still have the proved numerical payload semantics. The universal
claim only requires the explicit valid recipes E=3^e. There is no variable
input recoding hidden in that fixed recipe. The body's single-number
initial value is K(E*2^x−1)+1, and its acceptance target is n=K(F−1)+22
for some positive F. Formula(1) is used to interpret the computation,
not emitted as an unpaid initial-input equality.

## 6. Literal sharing, counts and comparison to residue enumeration

The builder accepts a fixed I/D/T table and fixed distinct primes, with
program prime3 and input prime2. It tests all occurring baseline pairs
and chooses by actual gate count, then multiplication count and pair.
Fixed linear forms share equal coefficients and may use an exact suffix
schedule instead of direct multiplication. A bounded cutoff keeps this
choice from iterating over the numerical size of a coefficient. No optimal
circuit claim is made.

The joined packing is also shared. In particular the selector prefix is
used in both H and A; the repeated W and J blocks use paid geometric
sums; and a single multiplication by B−1 scales the complete packed class
selector word. The three range masks share a paid1+P+P^2 factor. Powers
and geometric sums are emitted by recursion, and unused temporary outputs
are removed before the schedule is finalized. Every retained gate reaches
the actual final polynomial. Compared with the unshared packed expression,
this saves175 operations on the default. Complete signed identities check
that sharing changes neither a residual nor the full polynomial value.

The literal ledgers are:

|Form|Certificate|Comparisons|Witnesses|Polynomial|Degree bound|
|---|---:|---:|---:|---:|---:|
|raw SOS|643=234M+409A|21|88|705=255M+450A|1564|
|positive scale SOS|643=234M+409A|20|87|702=254M+448A|1564|
|six-field SOS|643=234M+409A|14|81|684=248M+436A|3600|
|normalized norm product|648=239M+409A|10|81|677=249M+428A|10926|
|coupled index product|651=241M+410A|8|81|674=249M+425A|10416|

The default seven factor bounds are1670,3864,901,129,2064,770,770,
summing10168. The largest retained residual bound is124; hence the
product bound is10168+2*124=10416. The same-cost coupled SOS form has
bound20336. The guarded exact main-norm cancellation is inherited; no
zero-set equation is used to lower the degree. These are upper bounds,
not exact-degree claims.

Arithmetic size depends on the sparse branches and coefficient classes,
not the residue modulus(2). With b branches and g exceptional pairs,
the raw witness count is b+g+29; the coupled form has b+g+22. The joined
lane count is b+g+3. The fixed linear forms and shared packs have size
O(b+g), with paid logarithmic power/geometric-sum schedules. By contrast,
the existing fully expanded residue-history builder begins with M distinct
selector unhattings and M−1 selector-sum additions:446,185,739 gates
already at that stage for(2). That is a count of the specified enumerating
builder, not a lower bound for this map or for alternative circuits. No
such giant source was materialized.

## 7. Reproducible evidence

Run `python3 residue_affine_sparse_universal.py` to compare the receipt;
`--write` regenerates it. Checks include full raw source/residual oracles,
all inherited native rewrites, complete shared/unshared polynomial
identities on signed and positive assignments, differential prime-payload
versus counter-vector runs, numerical residue-table samples, and explicit
count-congruence aliases excluded by the growth bound. Zero quotient words,
p=2 zero branches and zero selected-product classes remain in the positive
hat domain. These bounded computations audit the literal construction;
they do not materialize a full huge native Pell tuple or replace the
unbounded universality proof.

The final author writer and fresh replay both pass. The receipt records
25 literal ledgers across five fixed tables, including a table with no
exceptional coefficient class; 120 complete raw identities (60 signed);
400 complete shared/unshared identities (200 signed); and the inherited
positive-scale, computed-field, norm and index correction audits in each
context. The differential execution audit checks 169 halted histories and
700 chronological rows across 25 tables, rejecting 153 wrong input counts.
It also checks 1,600 random-access residue identities, 11,812 bounded
count-congruence cases, 150 unbounded aliases excluded by the growth
bound, and 16,432 local quotient/remainder assignments. These are finite
source, algebra and outer-history checks, without full Pell-witness
materialization.

Native's independent full proof/source/fresh-replay review passes with no
findings. Its separate executors checked 40 ledgers; 400 complete
shared/unshared outputs (200 signed, including 80 zero-class cases);
64 independently reconstructed raw SOS identities; 148 independently
simulated and packed halted histories with 567 rows and 123 wrong-input
rejections; and 216 count aliases rejected by the range. A separate
one-number interpreter checked 840 exhaustive small residue rows and
3,360 exact affine-map identities. All four local links resolve. This
evidence concerns finite algebra and outer histories, not full native
Pell zeros.

Root's independent full proof/source/dependency review and fresh replay
of the final five-fixture source and receipt also pass with no findings.
Its own counter-vector interpreter, prime-payload reconstruction, packing
and literal outer/AND executor checked 144 halted histories and 660 steps
across 41 new tables, including every branch kind, and rejected 133 wrong
input counts. It did not use the author's run, packing or outer-oracle
helpers. These are outer-history checks, with no full Pell tuple claim.
The source, receipt and proof are frozen after these reviews.

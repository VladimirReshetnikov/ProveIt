# A unified binomial, a common index cap, and a representative-dependent radix

## 0. The explicit equation and theorem

Let `R_1,...,R_189` be the 189 literal quadratic polynomials in the ordered
list `equations/principal241/natural/equation.json`, with the coordinate order
given by its 241-entry variables list. Define the ordinary integer polynomial

    P(z_0,...,z_240) = sum_(j=1)^189 R_j(z_0,...,z_240)^2.

The equivalent collected coefficient list is
`equations/principal241/natural/expanded_polynomial.json`. It has exactly
30,058 nonzero monomials, total degree four, and maximum absolute coefficient
85,187,728. All 241 variables occur. There are no variable exponents,
uninterpreted binomial functions, input programs, unspecified coefficients,
or additional parameters in this polynomial. Powers, Pell sequences and
binomials used below are proof notation for the explicitly emitted graphs.

The domain is `N={0,1,2,...}`. The mathematical theorem is

    ZFC proves [there is no z in N^241 with P(z)=0] <-> Con(ZFC),

where consistency means absence of a finite syntactic refutation. Neither
side of this equivalence is asserted. The proof uses the inherited numerical
C222-calculus calibration described in Section 11. It contains no simulation
of K215 and no specialization of Jones's universal polynomial.

The dense companion is the same uncontracted arithmetic source with another
certified natural-domain contraction: 239 natural unknowns, 187 quadratic
residuals, 387,494 monomials, coefficient height 269,805,528. It has lower
dimension but a much larger expanded support. The principal equation is
preferable when dimension, support and coefficient height are considered
together.

This report proves the new arithmetic composition in ordinary mathematics
formalizable in ZFC. It does not claim a newly completed end-to-end Lean,
Rocq or emitted object-language ZFC proof, a proof of consistency, worldwide
priority for the inherited lemmas, or global minimality.

## 1. What is combined, and what changes

The two principal parents are the supplied
`ConZFC_Shared_Binomial_Certificates_2026-10-24.zip` and
`ConZFC_Shared_Pell_Bound_261_2026-10-24.zip`. A third source,
`ConZFC_Unified_Binomial_Even_Indices_Round15_2026-10-24.zip`, already proves
the useful raw-ceiling inequality `V0<B^2`. Exact archive hashes and the
inspected repository commit are in `SOURCE_LEDGER.json`.

The first parent gives one binomial simultaneously certifying a factorial
and the reciprocal CRT product, six exact powers, eleven modular binomial
requests, a common modular root, and the complete C222 source. The second
gives a single indexed-Pell anchor, one bound for all seed ordinates, and
one sum of squared index errors. Its independent self-radix argument also
justifies amplification `K=R` at horizon 12.

The present composition makes two essential changes.

1. The single common index cap checks not only the six exact-power exponent
   indices, but also all eleven modular-binomial upper indices. The latter
   were absent from the first parent's frame. They are added to the frame
   before applying the cap theorem.
2. With `S` the sum of nine independent positive CRT representatives, use
   `q=N(S+1)^K`, with `K=R` and `t>=12`. Delete the previous aggregate bound
   on those representatives. The raw inequality `V0<B^2` justifies omitting
   `V0` from the second parent's radix base `V0+S+1`.

All logical rule constructors, the nonnegative local polynomial, factorial
ceiling, reciprocal index congruence, ten range requests and their local
degree certificates remain the inherited ones. Every new private Pell
witness is chosen after all the semantic quantities. No pointwise identity
between complete old and new witness tuples is claimed.

## 2. The semantic arithmetic source

The outer coordinates include `t0,x,y,F`, all natural. Put

    t=t0+12,       R=2+t+x+y+F,       K=R,
    rho=F^2,      V0=(F^2+1)^t,
    B=b0+2,       N=B^K.

The value `F` is initially a proposed factorial. The proposed binomial `B`
has one exact-digit graph for `binom(F^2+t,t)`. Its interpretation must not
be used prematurely. Impose the two raw natural ceiling equations

    V0+B=BF+r+1,          B=r+s+1.                      (2.1)

The eight positive CRT representatives `A_1,...,A_8` encode the local
columns `(a,b,c,d,Sold,Snew,u,v)`. The ninth representative `C` encodes the
row index. Define

    S=C+A_1+...+A_8,       U=(S+1)^K,       q=N U.

There is no equation `S+slack=9N^2`. The independent representatives can be
chosen before the radix without any upper bound.

The six exact-power requests are

    V0=(F^2+1)^t,       N=B^K,       U=(S+1)^K,
    Dt=q^t,            Dx=q^(x+1),  Dy=q^(y+1).          (2.2)

The remaining denominator `Dt1=q Dt=q^(t+1)` is an ordinary multiplication.
There are eleven modular requests: the one exact binomial, the eight column
ranges, the index range, and the derived label range. Their lower indices
belong to `{t,t+1,x+1,y+1}`. Their upper indices are `F^2+t`, the nine
positive representatives, and the positive derived label polynomial `J`.

All these abbreviations have literal quadratic arithmetic graphs in the
source. The exported semantic graph has 777 natural coordinates and 725
quadratic rows before the two exact contraction phases in Section 12.

## 3. A frame that bounds every requested index before semantics

For an exact request `(n,k,z)` include its base, exponent and output
coordinates in a finite set `T`. Also include the upper index of every
modular request. Repeated coordinates are included once. The new frame is

    W = 2 + sum_(a in T) a.                             (3.1)

The emitted set has 25 atoms. All are natural, and every independent seed
index is a distinct positive member of it. Positivity follows from raw
definitions: the exact-power exponents are `t,K,x+1,y+1`; the modular
indices are `F^2+t`, nine coordinate shifts by one, and the positive label
sum containing a constant one. There are 15 independent seeds. Thus

    1 <= k_i < W,             m=15 <= W-2.              (3.2)

This does not use any intended factorial, power, binomial or CRT meaning.
None of the private anchor, comparison or root-congruence witnesses occurs
in `T`. In particular no circular equation bounds `W` by a function of its
own future Pell witnesses.

The retained lower-scale equations, with `Z=z0+1`, are

    L^2 - ((W+1)^2-1)(W Z)^2 = 1,       A=L+sigma.       (3.3)

For an integer base `a>=2`, write

    X_0(a)=1,   Y_0(a)=0,
    X_(j+1)(a)=a X_j(a)+(a^2-1)Y_j(a),
    Y_(j+1)(a)=X_j(a)+a Y_j(a).

Natural Pell classification in (3.3) gives `L=X_e(W+1)` and
`WZ=Y_e(W+1)`. Modulo `W`, `Y_e(W+1)=e`, so `W|e`. The ordinate is
positive, hence `e>=W`. Since `X_e(a)>=a^e`,

    A >= L >= (W+1)^W,       A-1>W^3,       A>W+1.       (3.4)

For `W>=3`, the strict cubic bound follows from
`(W+1)^W-1>W^3`. The lower frame gives these bounds before any of the six
power graphs is interpreted. The freedom `A=L+sigma` is retained for the
modular-root completeness argument.

## 4. A single indexed-Pell anchor and the joint error equation

Retain one complete copy of the inherited indexed-Pell criterion at
requested index `W`. Its principal pair is denoted `(Uc,Vc)`. In proof
notation the anchor has

    Uc^2-(A^2-1)Vc^2=1,
    Hc^2-(A^2-1)Jc^2=1,
    Sc^2-(Bc^2-1)Rc^2=1,
    Bc=1+4Vc(d+1),          Jc=Vc^2(e+1),
    Bc=A+Hc f,             Sc=Uc+Hc g,
    Rc=W+4Vc h.                                       (4.1)

Every displayed auxiliary is natural. The criterion additionally requires
`W<=Vc`; this follows from (4.3) below, so there is no extra private slack.
The inherited theorem then gives

    (Uc,Vc)=(X_W(A),Y_W(A)).                            (4.2)

For each seed `k_i`, retain only its main norm and impose

    xi^2-(A^2-1)yi^2=1,
    Vc=W+1+s_cap+sum_i yi,
    sum_i(yi-ki)^2=(A-1)Q.                             (4.3)

Natural Pell classification writes `(xi,yi)=(X_ji(A),Y_ji(A))`, `ji>=0`.
The aggregate bound gives `yi<Vc`, hence `ji<W`. The recurrence modulo
`A-1` gives `X_j(A)=1` and `Y_j(A)=j` modulo `A-1`. Consequently

    A-1 divides E=sum_i(ji-ki)^2,
    0<=E<=m(W-1)^2< W^3 < A-1.

Thus every `ji=ki`. In particular all eleven modular upper-index pairs
are now identified, although those indices can be enormous. Only their
decoded indices, not their Pell ordinates, were used in the small-error
argument.

For completeness, take all canonical pairs at the given indices. Each
`Y_ki(A)-ki` is a nonnegative multiple of `A-1`, so the quotient `Q` in
(4.3) is natural. Since `ki<W`,

    sum_i Y_ki(A) <= m Y_(W-1)(A),
    Y_W(A) > (2A-1)Y_(W-1)(A).

Together with `m<=W-2` and `A>W+1`, these inequalities give
`Y_W(A)-sum_iY_ki(A)>W`; the aggregate slack is natural. The inherited
indexed-Pell completeness theorem supplies all the remaining anchor
witnesses. These are constructive witness choices, not finite tests.

## 5. The six exact powers are recovered simultaneously

For each exact request `z=n^k`, the unchanged modulus and congruence rows
are

    Tn=2An-n^2-1,
    X_k(A)+nY_k(A)=A Y_k(A)+z+Tn h_n.                  (5.1)

The nonnegative modulus excludes `n=0`. The frame gives `n,k,z<W` and
`A>W^W`; in particular both `z` and `n^k` lie in `[0,Tn)`. The Pell
recurrence gives

    X_k(A)+(n-A)Y_k(A) = n^k (mod Tn).

Since Section 4 already proved that the pair has index `k`, (5.1) implies
`z=n^k`. This interprets every power in (2.2), without appealing to any
binomial or factorial semantics.

For completeness the quotient is nonnegative. If
`p_j=X_j(A)+(n-A)Y_j(A)`, then

    p_0=1,       p_(j+1)=n p_j+Tn Y_j(A).

As `Tn>=0`, this gives `p_k>=n^k`, and the difference is divisible by
`Tn`. Thus the required natural quotient exists.

## 6. The smaller radix is justified before interpreting B

Subtract (2.1) to obtain

    V0+s=BF.                                           (6.1)

The already interpreted power gives `V0=(F^2+1)^t>=1`, so `F>=1`.
Also `V0>F^2`, whence (6.1) yields `F<B`. Consequently

    V0<=BF<B^2<=N<q.                                  (6.2)

Here `K=R>=2`, and `S>=9`, so `N=B^K` and `q=N(S+1)^K>N`. No intended
value of `B` has been used. The displayed `B>=2` shift could already give
positivity, but it does not replace this stronger bootstrap inequality.

The inherited uniform coefficient lemma is essential:

    binom(r+t,j) <= (r+1)^t     (r,t>=1, 0<=j<=t).       (6.3)

Proof: induct on `t`. The case `j=0` is immediate. For `j<t`, Pascal's
identity and induction give at most `2(r+1)^(t-1)<=(r+1)^t`. For `j=t`,
use `binom(r+t,t)=product_(i=1)^t(1+r/i)<=(r+1)^t`.
This proof does not assume `r>=t`.

Applying (6.3) to `r=F^2` shows that every lower coefficient through digit
`t` of `(q+1)^(F^2+t)` is at most `V0<q`. The one exact digit graph
therefore really returns

    B=binom(F^2+t,t).                                  (6.4)

The modular graph supplies that digit by Section 8; its index is already
certified by Section 4. There is no circular assumption that the proposed
binomial output has its intended meaning before its digit bounds hold.

## 7. The factorial fixed point and the reduced amplification budget

For positive `F` define

    H_t(F)=(F^2+1)^t/binom(F^2+t,t)
          =t! product_(i=1)^t (F^2+1)/(F^2+i).

The two natural ceiling rows are equivalent to `F=ceil(H_t(F))`.
For every `t>=6`, this holds if and only if `F=t!`.

For soundness, every factor is at most one, so the ceiling gives `F<=t!`.
If `F<t`, monotonicity in `F^2>=1` gives
`H_t(F)>=2^t/(t+1)>t>F`, contradiction. The strict inequality holds at
six and persists by induction. Thus `F>=t`. The product inequality
`product(1-a_i)>=1-sum a_i`, with `a_i=(i-1)/(F^2+i)`, gives

    H_t(F)>t! (1-t(t-1)/(2F^2))>t!/2.

If `F<t^2`, then `t!/2>t^2>F` for `t>=6`, another contradiction.
Thus `F>=t^2`, and the sharper estimate is

    H_t(F)>t! (1-1/(2F)).

If `t!>=F+1`, this is greater than or equal to `F`, contradicting
`H_t(F)<=F`. Hence `F=t!`. Conversely at `F=t!>=t^2`, the same estimate
gives `F-1/2<H_t(F)<=F`, so the ceiling and its natural witnesses exist.

The retained local majorant certificate has `E=2^23=8,388,608`; the
derived-label certificate has `ell=2^22=4,194,304`. At horizon 12,

    12!=479,001,600>2^28,
    28E=234,881,024<2^28,
    2E<=2^28,
    3 ell*13=163,577,856<2*12!=958,003,200.               (7.1)

The first three bounds and the ratio estimate

    (1+1/r)^E <= sum_(j=0)^E(E/r)^j < 2   (r>=2^28)

give `r^E<2^r` for all integer `r>=2^28` by induction. Since
`R>=F=t!>=12!`,

    R^E<2^R=2^K.                                      (7.2)

The fourth bound persists with `t`, since factorial growth dominates
`t+1`. It gives

    ell(t+1)<=2F/3<F<R=K.                              (7.3)

These are exactly the size conditions used for bounded-source decoding
and the derived-label digit. They justify the smaller amplification
`K=R` and horizon 12; no large new numerical coefficient is inserted in
the equation to replace that proof.

## 8. One common modular root gives all eleven binomial digits

Put `b=q+1` and

    M=q Dt1 Dx Dy=q^(t+x+y+4).

The exact denominators are among `Dt,Dt1,Dx,Dy`. For every such `d`,
`qd|M`. Since `N|q`, also `Nd|M`. The unchanged root equation is

    2A b=b^2+1+M h0,          h0>=0.                   (8.1)

In the quadratic Pell algebra, substituting `s=b-A` respects
`s^2=A^2-1` modulo `M`. Therefore for every natural `a`,

    R_a=X_a(A)+(b-A)Y_a(A) = b^a (mod M).              (8.2)

Also `R_a>0`: if `a>0`, `X_a(A)>(A-1)Y_a(A)`, so
`R_a>(b-1)Y_a(A)>=0`; at zero it is one.

For an exact binomial with output `B`, upper index `a`, lower index `k`
and `d=q^k`, the graph is

    X_a+bY_a=A Y_a+r+dB+qd h,
    d=r+s+1,                 q=B+o+1.                 (8.3)

For a range request it is

    X_a+bY_a=A Y_a+r+Nd h,
    d=r+s+1.                                          (8.4)

All witnesses are natural. If `binom(a,j)<q` for `j<=k`, the binomial
theorem and (8.2) show that (8.3) means exactly
`B=binom(a,k)` and (8.4) exactly `N|binom(a,k)`. The least residue
conditions follow from `0<=r<d`, `0<=B<q`, and `N|q`.
Conversely genuine low digits give natural witnesses: the residues in
(8.3) and (8.4) are the least nonnegative residues of the positive `R_a`
modulo `qd` and `Nd` respectively, so their quotient is nonnegative.

For the nine independent upper representatives, `a<=S`, and their lower
indices `k` are at most `R-1<K`. Thus

    binom(a,j)<=max(1,S^k)<(S+1)^K<q   (0<=j<=k).

The derived argument obeys the retained positive-DAG certificate
`J(A)<=(S+1)^ell`. With lower index `t+1`, (7.3) gives

    binom(J(A),j)<=max(1,J(A)^(t+1))
                 <=(S+1)^(ell(t+1))<q.

The exact factorial binomial has already been bounded in Section 6.
Consequently all eleven low-digit graphs are valid without any upper bound
on the independent representatives. This is the mathematical reason the
old aggregate equation and its slack can be removed.

## 9. Reciprocal CRT recovers every bounded source row

With `F=t!`, put `di=1+F^2/i` for `1<=i<=t`. Since `i|F`, these are
integers congruent to one modulo `F`. Every prime divisor of a `di`
exceeds `t`. Distinct `di,dj` are coprime: a common prime would divide
`i di-j dj=i-j`, impossible for a prime greater than `t`. Moreover

    product_i di=binom(F^2+t,t)=B.

For a prime `p`, the elementary range lemma is

    p^e | binom(a,k)  implies  a mod p^e < k.           (9.1)

If `a<k` this is immediate. Otherwise, if the remainder were at least
`k`, the interval `[a-k+1,a]` would contain no multiple of `p^e`.
In the factorial valuation formula for the binomial, every summand for
powers `p^j` with `j>=e` would then be zero; the remaining `e-1`
summands are each at most one. This contradicts valuation at least `e`.

For row `i-1`, choose a prime `p|di`, let `m=v_p(di)` and `e=Km`.
The retained index congruence is `B | C+F^2+1`, so `C=i-1 (mod p)`.
The range `N|binom(C,t)` gives a residue less than `t` modulo `p^e`.
Since `p>t`, that residue must be exactly `i-1`.

The eight other range conditions give residues in the required local
bounds `(t,t,t,t,y,y,x,x)`. The local polynomial `L` is nonnegative;
the source row `N|L(C,A)` and its literal majorant give

    p^e | L(i-1,locals),       0<=L(i-1,locals)<R^E<2^K<=p^e.

Hence every local row has `L=0`. The final range
`N|binom(J(A),t+1)` similarly gives `J(local)<=t`, because both its
bounded residue and the locally evaluated `J` lie below `p^e`.

Conversely, given valid bounded local rows, use CRT at the stronger
precision `di^(2K)` to choose all nine positive representatives. They may
be chosen arbitrarily large in their residue classes; no aggregate cap
is required. If `a` is congruent to a small residue `w<k` modulo
`p^(2Km)`, one factor in the falling factorial for `binom(a,k)` is
divisible by that power. Division by `k!` loses at most `k-1<K<=Km`
digits, so the resulting binomial is divisible by `p^(Km)`. If `a<k`,
the binomial is zero. This proves all range divisibilities, including
the derived `J` by polynomial congruence. The index and local evaluation
divisibilities follow from the same CRT choices.

## 10. The bounded C222 source yields a finite refutation

The unchanged numerical syntax uses the Cantor constructors

    I(a,b)=2(a+b)(a+b+1)+4b,
    Mem(a,b)=I(a,b)+1,  All(a,b)=I(a,b)+2,
    Eq(a,b)=I(a,b)+3,   Neg(a)=I(a,1).

The nine axiom conclusion polynomials and the guarded bundle are literal
in the retained `direct_calculus.py` and in the generated arithmetic.
The local rule branches have one conclusion and zero, one or two premises;
truth has label zero and falsehood has label one. Modus ponens and
generalization use their calibrated numerical C222 formulas. The bundle's
guard `(c-a)^2(c-b)^2=(d+1)^2` exactly expresses both inequalities `c!=a`
and `c!=b` over the natural domain.

The local polynomial is the product of nonnegative branch residuals plus
the two squared beta-remainder residuals. Its vanishing chooses a valid
rule and enforces

    Snew(1+F*conclusion)
        = Sold(1+F*premise1)(1+F*premise2).

Unused premises have label zero and therefore weight one. The derived
label bound places every possible rule label in `[0,t]`. The beta
equations identify adjacent states, and the endpoint equations give
initial state `1+F` and final state one. The initial state and all branch
weights are positive, so all states are positive.

The weights `1+jF`, `1<=j<=t`, are pairwise coprime. Multiplying the
local equations and cancelling the states gives exact multiplicity balance:
one net conclusion of label one, zero net balance for all other positive
labels. Suppose label one lay outside the closure of truth and the selected
axioms under the selected rules. Every rule whose conclusion lies outside
that closure has at least one premise outside it. Counting conclusions
minus premises outside the closure is consequently nonpositive, contradicting
the net one. Thus label one has a finite C222 derivation. This argument
allows cycles in the supplied rule multiset and uses the single-conclusion
property essentially.

Conversely expand a finite C222 derivation to a proof tree. Choose `t>=12`
larger than its finite size, all schema parameters and all label sums, and
pad with truth rules. Put `F=t!`. Expanding pending proof obligations gives
the positive product-accumulator path. Choose `y` sufficiently large for
all states and divisible by `t!`. The beta moduli `1+(i+1)y`, `0<=i<=t`,
are pairwise coprime; choose `x` by CRT to encode the states. This is done
after the horizon is chosen and imposes no circular requirement that the
horizon exceed the later, much larger accumulator values.

## 11. Completeness order and the logical endpoint

Start with a finite calibrated refutation. Choose in order:

1. The padded horizon and bounded source rows, then `F=t!`, `x,y`.
2. `B`, `R=K`, `N`, and the nine CRT representatives at precision `2K`.
3. Their sum `S`, the radix `q=N(S+1)^K`, all exact denominators and all
   true binomial residues.
4. The enlarged semantic frame `W`, then `L=X_W(W+1)` and
   `Z=Y_W(W+1)/W`.
5. A sufficiently large positive `A>=L` satisfying (8.1).
6. The canonical seed pairs, the one complete indexed anchor, every
   private quotient, the aggregate slack, and the error quotient.

Step 5 is always possible. The modulus `M` is a power of `q`, so
`gcd(q+1,M)=1`, and `gcd(2(q+1),M)` is one or two. In the second case
`q+1` is odd and `(q+1)^2+1` is even. The linear congruence (8.1) for
`A` therefore has a solution class with arbitrarily large positive members.
Choose one also making the root quotient natural, and set `sigma=A-L`.
The indexed-Pell completeness theorem holds at this arbitrary chosen base.
Section 4 supplies the natural aggregate/error witnesses. Sections 5 and 8
supply the remaining nonnegative quotients. Every raw residual now vanishes.

The named inherited logical interfaces are

    KEndpoint.c222_iff_zf_refutation,
    ConstructibleChoice.zf_refutation_iff_zfc_refutation.

Copies and their source identities are retained under `source/logical_interfaces`.
The first is the numerical-calculus endpoint, before any machine-specific
halting statement. The second is the constructible-model transport of
Choice. The exact indexed-Pell interface is retained under
`source/arithmetic_interfaces/PellRepresentation.lean`.

The ordinary arithmetic bridge and its finite-syntax constructions are
retained in the parent proof documents and the frozen Round14 source. All
new arguments above use finite algebra, integer induction, elementary Pell
theory, binomial identities, unique factorization and finite CRT. They are
formalizable in ZFC uniformly over its internal natural numbers. The result
is an ordinary proof with named inherited dependencies, not a claim that
the entire object-language derivation or its transitive Lean closure has
been rebuilt in this package.

## 12. Exact polynomial transformations and finite checks

The arithmetic builder first exports its 777-coordinate, 725-row semantic
graph to a 349-coordinate, 297-row quadratic system. The independent affine
checker reconstructs all 428 deleted coordinates by nonnegative affine
integer polynomials and compares every surviving row exactly.

The principal natural contraction then eliminates 108 more coordinates.
Each deleted coordinate has a monic defining equation and an explicitly
verified nonnegative quadratic restoration. Two restorations have negative
coefficients; their rational sum-of-squares certificates prove natural-domain
nonnegativity exactly. Every substitution is checked in every row, and the
degree remains at most two. The final equation is the sum of squares of
all 189 resulting residuals. Independent integer polynomial multiplication
collects and compares all 30,058 coefficients. Thus the two contraction
phases preserve existence in both directions over `N`, not just on sampled
solutions.

`verify.py` checks the source ledger, affine export, complete contractions,
collected quartics, liveness, degree, coefficient height, semantic manifests,
and corruption controls. `--rebuild` additionally runs the portable builder
in a fresh temporary directory and requires byte equality of every emitted
JSON object for the chosen endpoint. The checkers retain their checks under
`python -O`. Finite computations validate literal syntax and transformations;
they do not infer the unbounded theorems from examples or decide whether
the polynomial has a zero.

The principal equation improves the inspected 261-natural-variable quartic
simultaneously in dimension, residual count, monomial count and coefficient
height:

    261 -> 241 variables,
    194 -> 189 residuals,
    31,679 -> 30,058 monomials,
    85,566,955 -> 85,187,728 coefficient height,
    degree 4 -> degree 4.

These are comparisons within the direct, small-literal-coefficient natural
quartic architecture. Other repository constructions use fewer variables
with different degrees, domains or large coefficient payloads.

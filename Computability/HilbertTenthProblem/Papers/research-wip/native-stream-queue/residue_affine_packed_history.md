# A paid finite orbit for residue-affine maps

The [literal compiler](residue_affine_packed_history.py) gives a fixed-arity
Diophantine representation of arbitrarily long finite trajectories of a fixed
positive residue-affine map. The ordinary starting integer and target enter
directly. Residue selection, division, selected products, duration, bounded
digits and chronological transport are all paid.

For the shortcut Collatz map the default nonempty-orbit polynomial costs
**134=64M+70A**, with21 positive witnesses, five comparisons and propagated
degree at most748. The raw SOS option costs165 with28 witnesses and degree
at most124. Including a zero-step orbit costs two more operations. These are
orbit-relation counts, not a claim that Collatz is universal or that every
input reaches1. No numerical universal bound is asserted.

This closes the finite-iteration obligation left by the
[factored residue-affine step](residue_affine_factored_counter_step.md).
Its prime-encoded universal counter substrate remains subject to its separate
ordinary-input exponent loader. The established75/87 and explicit U9 bounds
are unchanged. The [receipt](residue_affine_packed_history.json) contains the
actual default schedule and its literal operation ledger.

## 1. The fixed map and the complete relation

Fix a nonempty table of integer pairs

    (a_s,d_s), 1<=s<=m, a_s>=0, d_s>=1.

It defines a total positive map by the unique decomposition

    n=m*q+s, q>=0, 1<=s<=m,
    f(n)=a_s*q+d_s.                                      (1)

For fixed positive x,y the compiled polynomial has positive existential
coordinates if and only if

    f^T(x)=y for some integer T>=1.                      (2)

Neither T nor any history length is a supplied free parameter. The number
of supplied coordinates and source gates depends only on the fixed table.

The shifted residue convention is deliberate. For a total positive map
written in the old convention f(mq+r)=a_r*q+d_r,0<=r<m, replace its zero
row by (a_0,a_0+d_0) at s=m and leave rows1 through m-1 unchanged.
Their offsets are f(1),...,f(m), hence strictly positive. Nonnegative
slopes are preserved. In particular the prime-encoded counter maps in the
earlier packet fall within(1), after expanding their fixed residue tables.
That connection supplies a computational substrate, not a free conversion
of ordinary input into its prime-power code.

## 2. Source and domains

Choose a baseline slope a0 occurring in the table. There is one exceptional
class for every other distinct slope; let g be their number, so g<=m-1.
Supply positive selector hats Ehat_s, one quotient-word hat What, one
selected-product hat Zhat_a per exceptional class, and positive slacks
eta,beta. Define

    E_s=Ehat_s-1, W=What-1, Z_a=Zhat_a-1,
    J=sum_s E_s, h=x+y+eta,
    K=least power of two >=max(4,m+1,1+max_s(a_s+d_s)),
    B=K*h, P=(B-1)J+1,
    G_a=sum_(s:a_s=a) E_s, R=(h-1)J.                   (3)

The two outer equations are

    J+What+sum_a Zhat_a+beta=P,                        (4)
    B*N+x=C+P*y,                                     (5)

where the exact paid linear forms are

    N=a0*W+sum_a(a-a0)Z_a+sum_s d_s E_s,
    C=m*W+sum_s s E_s.                               (6)

Negative slope differences are allowed in the emitted source. The proof
does not assume N nonnegative before selection is typed.

Concatenate the following scalar AND lanes in base P:

    (E_s,J,E_s)             for all m residue selectors;
    (W,(B-1)G_a,Z_a)       for all g exceptional classes;
    (W,R,W)                for the quotient range.      (7)

Let their packed integers be H,M,A, in that order. Put ell=m+g+1 and let
v be the least power of two at least ell. Prescribe native scale

    Q=B*P^v.                                          (8)

The builder pays the squaring chain for P^v and its multiplication by B.
It embeds the complete prescribed AND64 at ports(H+1,M+1,A+1,Q),
folding these into the literal padded words16H+12,16M+10,16A+8 and scale16Q.
All22 native auxiliaries and16 comparisons remain in the raw source.

## 3. Pretyping positivity and sound chronology

On every positive assignment E_s,W,Z_a,J,G_a are nonnegative, h>=3,
B>=12 and P>=1. The native hats, padded words and scale are therefore
positive before any equation is used. Equation(4) excludes J=0: it would
give P=1 while What+beta>=2. Consequently J>=1 and P>=B.

Also(4) gives W,Z_a,J<P and E_s,G_a<=J. Therefore

    (B-1)G_a<=P-1, R=(h-1)J<P,
    0<=H,M,A<P^ell<=P^v<Q.                            (9)

These are entirely algebraic bounds; they do not presume typed selector
bits, dyadic radices or a duration. The complete native theorem now gives
dyadic Q and H AND M=A. Since Q=B*P^v is a positive power of two, B and P
are dyadic. Since K is dyadic and B=K*h, h is dyadic as well.

Write B=2^b,P=2^p. The equality P-1=(B-1)J and J>=1 imply b divides p:
reducing p modulo b leaves a number2^r-1 in[0,B-2] divisible by B-1,
so r=0. Thus

    P=B^T, J=1+B+...+B^(T-1), T>=1.                  (10)

Because all lane coefficients are in[0,P) and P is dyadic, the joined
AND splits into exactly(7). Each E_s is a bitwise subset of J. Its digits
are0 or1 at the time positions. The equality sum E_s=J gives exactly one
selected residue per time: its lowest sum is at most m<B, so reduction
modulo B forces sum1 without a carry; divide by B and repeat.

The range lane W AND R=W now writes

    W=sum_(t<T) q_t B^t, 0<=q_t<h.                   (11)

Here h is dyadic, so the digit h-1 permits exactly its low bits. The class
lanes select the same quotient digits where the selected residue has that
slope. In particular the actual digits of the paid words in(6) are

    C_t=m*q_t+s_t,
    N_t=a_(s_t)*q_t+d_(s_t).                         (12)

Both are positive and below B. Indeed C_t<=m*h<B, and
N_t<=(a_s+d_s)h<B. The endpoints x,y are below h by(3).
These bounds justify canonical base-B comparison in(5), even when(6)
used negative baseline differences. Its low digit says C_0=x; the middle
digits say C_(t+1)=N_t; its top digit says N_(T-1)=y. The decomposition
in(1) is unique, so this is an actual T-step orbit of f. No unordered
flow or endpoint-only condition has replaced the chronology.

## 4. Positive completeness, including zero quotient words

Given a genuine finite orbit x=n_0,...,n_T=y with T>=1, take a dyadic h
strictly larger than x+y and every quotient floor((n_t-1)/m). There is no
assumption that the intermediate orbit is bounded by its endpoints.
Set eta=h-x-y>0 and choose(10). Pack the actual residue choices and
quotients, and the selected quotients for each exceptional class. A
zero quotient word or an unused slope class has supplied hat1 and is
fully allowed.

The exceptional classes are disjoint, so sum Z_a<=W and
W<=(h-1)J. Hence the remaining slack satisfies

    beta=P-J-What-sum Zhat_a
        =(B-2)J-W-sum Z_a-g
        >=(B-2h)J-g
        =(K-2)hJ-g>0.                               (13)

The last inequality uses K>=4,K>=m+1,g<=m-1,h>=3 and J>=1.
All outer equations, bounds and lanes hold. The inherited prescribed
native theorem supplies positive native witnesses at the new scale16Q.
No old native tuple at another scale is reused. This completes both
directions of(2), including T=1 and histories with W=0.

## 5. Literal forms, example and empty histories

All numeral multiplications are paid. The compiler shares identical literal
instructions, folds multiplication by0 or1, and may compare all occurring
baseline slopes to select the cheapest emitted schedule. This finite search
claims only the best among those emitted baseline schedules.

After the raw source, the existing [positive-scale](native_binary_positive_scale.md),
[computed-field](native_binary_computed_fields.md),
[norm-unit](native_binary_norm_units.md) and
[index/coupled-unit](native_binary_index_coupled_units.md) wrappers apply with
their actual producer/consumer and private-field guards. Their scope is
unchanged: graph projections where proved, and fresh positive auxiliary
reconstruction for the normalized strong/linear forms. Sections3--4 supply
the positive native interface and complete outer relation required by them.
The checker audits their complete corrected outputs, not just equalities
restricted to zero tuples.

For a raw certificate with C gates there are18 comparisons and m+g+25
positive witnesses. The five forms have the following cost changes:

| Form | Certificate | Comparisons | Witnesses | Polynomial |
|:---|---:|---:|---:|---:|
| Raw SOS | C |18|m+g+25|C+53|
| Positive-scale SOS |C|17|m+g+24|C+50|
| Six computed fields SOS |C|11|m+g+18|C+32|
| Normalized norm units |C+5|7|m+g+18|C+25|
| Coupled index units |C+8|5|m+g+18|C+22|

The default source also uses the computed identity J=sum E_s to emit

    sum d_s E_s = d_min*J + sum (d_s-d_min)E_s,
    sum s E_s = J + sum (s-1)E_s.                    (14)

These are exact identities on every integer assignment; neither selector
bits nor any equation is assumed. In the example below, they replace
2E_1+E_2 by J+E_1 and E_1+2E_2 by J+E_2, saving two literal
multiplications. The optional `shared_selector_sum=False` retains the
unfactored136-operation schedule. The checker compares complete outputs,
active interfaces and every retained residual for both forms.

The shortcut Collatz map uses table((3,2),(1,1)): on odd n=2q+1 it
returns3q+2=(3n+1)/2; on even n=2q+2 it returns q+1=n/2.
The selected baseline is1. Its literal counts are:

| Form | Certificate M+A | Polynomial M+A | Witnesses | Degree bound |
|:---|---:|---:|---:|---:|
| Raw |112=52M+60A|165=70M+95A|28|124|
| Positive scale |112=52M+60A|162=69M+93A|27|124|
| Computed fields |112=52M+60A|144=63M+81A|21|256|
| Normalized norm units |117=57M+60A|137=64M+73A|21|778|
| Coupled index units |120=59M+61A|134=64M+70A|21|748|

These are propagated upper bounds through the actual source, including the
guarded exact main-norm cancellation. They are not asserted exact degrees.
The default seven factor bounds are118,280,65,9,152,54,54, summing to732;
the largest remaining residual bound is8, giving732+2*8=748.

For T>=0, multiply the chosen complete polynomial by x-y. Over the
integers the result is zero exactly when either the old polynomial is
zero or x=y. This adds1M+1A, preserves the positive witness domain and
adds at most1 to its degree bound. In the x=y branch arbitrary positive
values may be assigned to all witnesses; no nonempty native history is
required. The default empty-orbit option therefore costs136=65M+71A with
the same21 witnesses and degree at most749.

## 6. What remains separate and reproducible evidence

The proof solves the generic finite-iteration problem for(1). It does not
solve Collatz termination or assert that a particular small residue table
is universal. The counter-map construction in the earlier packet uses an
initial value K*(2^e*3^x-1)+j_start; its variable exponent3^x remains a
separate paid loader obligation. Expanding its fixed residue table and
applying this history compiler is legitimate, but no unexecuted combined
universal source or operation bound is claimed here.

The checker records the literal schedule, complete raw-source/native-oracle
identities, all inherited corrected outputs, exact empty-orbit product
identities, and finite genuine histories. Exhaustive short outer assignments
also compare arithmetic transport with literal consecutive states and reject
corrupted selected products. These finite checks supplement the unbounded
proof. None purports to materialize the large positive native Pell tuples
or prove nontermination from a finite simulation cutoff.

Run with the repository verification dependencies:

```sh
python3 residue_affine_packed_history.py
```

Author receipt generation and a separate fresh default replay passed. The
receipt checks70 ledgers and complete source closures;224 full raw identities
(112 signed);672 inherited correction identities (336 signed);280 exact
empty-orbit product identities;560 complete shared-selector/unfactored identities
(280 signed); and896 genuine paths with3,136 chronological
steps, including52 all-zero quotient histories. It exhausts28,032 short
outer assignments and rejects18 corrupted selected products. All seven local
links resolve. Root independently reviewed the complete136 proof/source and
replayed its default, then checked31,164 typed assignments on four new tables,
including104 accepted histories and98 corrupted selected products, with an
independent executor. That review found no issue. The134 delta is the
all-tuple identity(14). Native's full final proof/source review and fresh
replay passed, with no findings. Its separate executor checked115 ledgers
on12 tables,920 complete shared/unfactored output and residual identities
(460 signed),184 independently rebuilt raw SOS identities and6,450 typed
outer assignments, including26 accepted histories and10 rejected selected
product corruptions. Zero slopes, zero quotient words and nonmonotone
histories were included. These remain component/algebra checks rather than
materialized native Pell zeros. Author's final134 receipt generation and
fresh replay also passed.

Root's final134 delta review and fresh default replay also passed. It
independently read the shared J/minimum-offset identities and new literal
counts, then repeated its separate31,164-assignment oracle on four new
tables:104 accepted histories and98 rejected selected-product corruptions
still agreed after the two-multiplication saving. No findings remain.

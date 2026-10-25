# Symmetric residue bounds replace individual sign certificates

## Result and precise source boundary

The primary endpoint is `merged_aggregate_centered/equation.json`: the sum
of the squares of its 186 explicitly listed quadratic residuals is an
ordinary quartic in 260 unrestricted integer variables. Its fully collected
coefficient list has 5,325 nonzero monomials and coefficient height 128,446.
The companion `grouped_centered/equation.json` uses 261 integers, 185
residuals, 5,332 monomials and the same height. Every variable is quantified
over all of Z. There are no positivity conventions on unnamed inputs.

Both are obtained from the literal `strict_dimension` signed source of
the incoming *Cofinal anchors and height one equations for ZFC consistency*,
Round 17. That source's centered endpoint has 282 integers, 192 residuals,
5,491 monomials and height 128,446. Its source is pinned to the bytes in
`parent/strict_dimension`, and its independent checker and ordinary proof
dependencies are retained. The public repository comparison pin is
`e0c98c629bf10d30b695884f6b1d2ab361bdf513`.

The new argument changes only how eleven low binomial remainders receive
their integer interval certificates. It does not alter the numerical C222
proof calculus, factorial fixed point, CRT encoding, semantic Pell anchor,
power requests or self-sized radix. In particular it introduces no machine
simulation, Jones polynomial, new numerical coefficient port, or exponent
primitive in the final equation.

Here is the logical claim, with its dependency made explicit. The retained
ordinary source theorem identifies integer solvability of the old signed
graph with a finite C222 derivation, and identifies the latter with a finite
ZFC refutation. The new theorem below proves existential equivalence of the
new and old signed graphs while preserving all their common semantic
coordinates. Their exact integral projections and translations preserve
integer solvability. Consequently ZFC proves, for each displayed fixed
quartic P,

    (there is no integer tuple z with P(z)=0) iff Con(ZFC).

The ordinary argument is formalizable in ZFC. This packet does not claim a
newly compiled end-to-end Lean/Rocq endpoint or an encoded object-language
ZFC proof object. Finite coefficient checks do not replace this unbounded
argument, and no assertion of consistency or global optimality is made.

## 1. A general signed remainder theorem

For every nonnegative integer n there are integers a,b,c with

    n = a^2+b^2+c(c+1).                                  (1)

The right side is nonnegative at every integer triple. For surjectivity,
the three-square theorem represents 4n+1 by three squares: it is not of
the excluded form 4^e(8h+7). Modulo four exactly one of the three entries
is odd. After placing that entry last, write the three entries as 2a,2b,
2c+1, and divide the identity by four. This is the same universal
nonnegativity certificate used by the retained signed source.

**Lemma 1 (a symmetric residue certificate).** Let L be a positive integer.
Let c_1,...,c_m be integers with 0<=c_i<L/8, and suppose arbitrary integers
r_i satisfy r_i=c_i modulo L. If integers a,b,c satisfy

    L^2 - 2 sum_i r_i^2 - 1 = a^2+b^2+c(c+1),             (2)

then r_i=c_i for every i. Conversely, if m<=32 and r_i=c_i, the certificate
(2) has integer witnesses a,b,c.

Proof. Nonnegativity in (1) gives 2r_i^2<L^2, hence

    |r_i| < L/sqrt(2) < 3L/4.

Therefore |r_i-c_i|<7L/8<L. The difference is a multiple of L, so is zero.
Conversely,

    2 sum_i c_i^2 < (2m/64)L^2 <= L^2.

The difference L^2-2 sum_i c_i^2 is a positive integer. Subtracting one
leaves a nonnegative integer, which has representation (1). This proves
both directions without requiring nonnegative inputs r_i. The factor two
in (2) is essential to this proof: replacing it by one does not give the
needed separation from c_i-L. Explicitly, L=9,c_1=1,r_1=-8 satisfies
0<=c_1<L/8 and r_1=c_1 modulo L, but L^2-r_1^2-1=16=4^2 even though
r_1 is the wrong residue.

**Lemma 2 (a low-digit margin).** Let q>=2, k>=1 and n>=0 be integers.
Suppose binom(n,j)<=q/16 for 0<=j<k. The canonical low binomial residue

    c(n,k) = sum_{j=0}^{k-1} binom(n,j) q^j

satisfies 0<=c(n,k)<q^k/8, and

    (q+1)^n = c(n,k) modulo q^k.                          (3)

Proof. The binomial theorem gives (3). The geometric sum gives

    c(n,k) <= (q/16)(q^k-1)/(q-1)
            < q^(k+1)/(16(q-1)) <= q^k/8.

No interpretation of any supplied remainder r is used in this estimate.
Combining Lemmas 1 and 2 turns a signed modular remainder into the usual
nonnegative Euclidean remainder.

**Scaled version.** If L=qL0 with q>0, replace selected entries r_i in (2)
by q r_i. The resulting bound implies |r_i|<3L0/4 for those entries. If
their canonical residues satisfy c_i<L0/8, then q c_i<L/8. The same proof
works for a mixed group of scaled and unscaled residues. This is the only
extra observation used by the 260-variable endpoint.

## 2. The literal inherited interface

The following notation denotes semantic coordinates already present in
the parent graph. It is not a list of extra quantified variables. After
the parent's private Pell argument and before any remainder interval has
been used, the graph has the following meanings:

    t = 16+h0^2,       V = (F^2+1)^t,
    y = V(V-1),        H0 = 1+sum of the nine representatives,
    K = x,             N = B^x,             q = (B H0)^x.

The independent representatives are a,b,c,d,S,Sp,u,v,C0. The syntax label
h is a fixed polynomial in a,b,c,d. All nine representatives and h occur
as exponents in genuine requests at base q+1. The exact requests include
the numerator (q+1)^n for each of the following eleven cases:

| Remainder | Upper binomial index n | Lower digit position k | Denominator |
|---|---:|---:|---:|
| choose0.remainder | F^2+t | t | q^t |
| range8.remainder | C0 | t | q^t |
| range0.remainder | a | t+1 | q^(t+1) |
| range1.remainder | b | t+1 | q^(t+1) |
| range2.remainder | c | t+1 | q^(t+1) |
| range3.remainder | d | t+1 | q^(t+1) |
| range9.remainder | h | t+1 | q^(t+1) |
| range4.remainder | S | y+1 | q^(y+1) |
| range5.remainder | Sp | y+1 | q^(y+1) |
| range6.remainder | u | x | q^x |
| range7.remainder | v | x | q^x |

Each numerator row makes its supplied remainder congruent to (q+1)^n
modulo its listed denominator. This remains true if every quotient and
remainder is provisionally signed. The retained multiplication definitions
make this a literal divisibility assertion, not a bounded-quantifier
abbreviation.

The old source adds one private slack s_i for each remainder, with

    L_i = r_i+s_i+1,       r_i s_i >=0.                   (4)

The last relation is encoded by one copy of (1), hence three independent
integer witnesses per interval. Once L_i>0 is known, (4) gives r_i,s_i>=0.
The transformation removes exactly these eleven bound rows and eleven
ternary product-certificate rows. In the 261-variable variant it inserts
four copies of (2), for the four denominator groups in the table.

Crucially, the three initial scalar certificates for the factorial remainder,
factorial slack, and exact-binomial output slack remain. Denote these three
nonnegative coordinates by r,s,o. Their literal identities are

    B=r+s+1,       q=B+o+1,       F B=V+s.                (5)

The first two give B>=1 and q>=2 before interpreting any power. The graph
also retains the endpoint equations

    x=F+1+(y+1)u0,       x=1+[1+(t+1)y]ut.               (6)

No factor of (4) is used in (5), (6), the square frame, the semantic anchor,
or the private Pell orientation argument.

## 3. Soundness: arithmetic recovery in an acyclic order

The first task is to avoid using the missing remainder signs to prove their
own recovery. We therefore give the full order, not just a final margin
estimate that assumes F=t! prematurely.

### 3.1 Powers, representatives and endpoints come first

The parent's square frame, signed semantic anchor and pooled coordinate
errors have not changed. Its proof in `ORIENTATION_FIRST_PROOF.md` identifies
every principal pair with the canonical signed Pell polynomials at its
requested index, before using a remainder interval. At a base n>=2, a
negative requested exponent would make an integer m satisfy m n^j=1 for
j>0, after the source's large-modulus estimate turns the modular identity
into an exact one. Thus every such requested exponent is nonnegative, and
the output is its genuine nonnegative power. These facts hold for either
sign of the private Pell center.

Apply the t pair first to q^t and then to (F^2+1)^t; the possible base one
causes no difficulty because t>=16 is already known. Hence V=(F^2+1)^t.
Equation (5) gives F>=1, and

    F B >= V >= F^2+1,       B>F>=1,       B>=2, q>=3.

In particular V<=FB<B^2. The retained cofinal identity gives
y=V(V-1)>F+2. The q^x request forces x>=0. If u0<=-1 then the first equation
of (6) would give x<=F-y<0; hence u0>=0 and x>=F+1>=2. The second equation
forces ut>=1, and therefore

    x >= 2+(t+1)y.                                      (7)

As t>=16, F>=1 and V>1, this implies x>=6 (indeed the actual lower bound is
much larger). This proof has not yet used F=t!.

Every actual representative, and h itself, is an exponent at base q+1>=4.
The same negative-index argument makes all representatives nonnegative.
Thus H0>=1, and the base BH0>=2 is legitimate. The retained x requests give
N=B^x and q=(BH0)^x exactly. The other denominator and numerator powers are
likewise exact. All eighteen requests are recovered at this stage. The
strict-budget parent proof guarantees the t+1 denominator by its retained
one-step Pell addition; it is exactly q times the t denominator.

Consequently

    q=(BH0)^x >= B^6 >=16 B^2 >16V.                     (8)

This strengthened radix margin holds before any low remainder or binomial
has been decoded.

### 3.2 Decode only the factorial digit next

The inherited coefficient lemma proves for all F>=1, t>=1 and 0<=j<=t that

    binom(F^2+t,j) <= (F^2+1)^t = V.

It does not require F=t! or F^2>=t. By (8), these coefficients are strictly
below q/16. Lemma 2 gives a canonical low remainder c0<q^t/8.

For completeness, this coefficient bound has a short direct proof in the
present square-parameter case. Write m=F^2. If m>=t, monotonicity through
position t gives binom(m+t,j)<=binom(m+t,t), and the latter is
the product of 1+m/i for 1<=i<=t, at most (m+1)^t. If 4<=m<t,
each coefficient is at most 2^(m+t)<4^t<=(m+1)^t. The remaining positive
square is m=1; every coefficient in row t+1 is at most the sum of the
coefficients of its parity, namely 2^t=(m+1)^t. This proof does not use
any factorial or remainder interpretation.

In the four-group variant, (2) at denominator q^t gives
|choose0.remainder|<3q^t/4. In the three-group variant the merged certificate
gives |q*choose0.remainder|<3q^(t+1)/4, hence the same inequality after
division by the already positive q. The unchanged numerator row makes this
remainder congruent to c0 modulo q^t. Their distance is less than q^t, so
they are equal. This step needs no bound for any of the other ten canonical
remainders. Their squared terms are simply nonnegative in the common bound.

The exact-binomial output bound 0<=B<q was retained in (5). The numerator
identity, the newly correct low remainder, and the coefficient bound through
position t show

    B = binom(F^2+t,t).

The unchanged factorial fixed-point proof now applies to (5), with t>=16,
and gives F=t!. The same B is the product of the pairwise coprime factors
d_i=1+F^2/i, 1<=i<=t. This restores the factorial and CRT meanings at the
same stage as the parent, without assuming any other remainder sign.

### 3.3 Every remaining digit has uniform spare radix capacity

The retained raw index congruence is B | C0+F^2+1. As t>=16 and F=t!, the
product formula gives B>F^2+1. Since C0>=0 was already proved, C0 cannot be
zero. Therefore C0>=1 and H0>=2.

From (7) and y>=F+1, every lower digit position in the table is positive
and at most x. For any ordinary representative a_i>=0 and 0<=j<k<=x,

    binom(a_i,j) <= max(1,a_i)^j <= H0^(x-1) <= q/64.    (9)

The last inequality uses x>=6, B>=2 and q=B^x H0^x. It also covers j=0
and a_i=0, without the invalid expression 0^0 or an assumed positive
representative.

For the derived label, the unchanged constructor ledger supplies

    h <= H0^ell,       ell=4194304.

The repair for zero representatives in the parent proof is relevant here:
if n=max(a,b,c,d), then the inherited degree majorant uses
max(1,n)+1. Because C0>=1 is a separate representative, this is at most H0.
The retained factorial inequality at t>=16 is ell(t+1)<2F, while (7) gives
2F<x. Thus for 0<=j<t+1,

    binom(h,j) <= H0^(ell*t) <= H0^(x-1) <= q/64.        (10)

The factorial coefficients from the preceding stage are below q/16; (9)
and (10) give the same bound, with room to spare, for all remaining cases.
Lemma 2 now gives the canonical remainder c_i<L_i/8 for all eleven entries.

Each new group certificate gives |r_i|<3L_i/4, including the scaled entries
after division by q. Its unchanged numerator equation gives r_i=c_i modulo
L_i. Lemma 1 therefore gives r_i=c_i, and in particular

    0<=r_i<L_i for every i.

Set s_i=L_i-r_i-1>=0. Their products r_i s_i are nonnegative, so (1) supplies
the old eleven product certificates. This restores every deleted row of
the exact old signed source while leaving its common semantic coordinates
unchanged. All other rows were retained literally. Thus every new zero
extends to an old zero. The source's range decoding and finite-refutation
calibration now apply.

## 4. Completeness

Start with any zero of the old signed source, or with any finite refutation
and the parent's constructive witness assignment. Its recovered arithmetic
has all properties just used: x>=6, F=t!, q=(BH0)^x, H0>=2, the exact powers,
and the coefficient margins (8)--(10). Its eleven supplied remainders are
the canonical low residues c_i. Therefore each satisfies c_i<L_i/8.

For the 261-variable variant the four group sizes are 2,5,2,2. Lemma 1
supplies all four ternary certificates. For the 260-variable variant, set
Q2=q^2 and S0=c0^2+c8^2, using the existing square wire and the new sum-square
wire. At the merged denominator L=q^(t+1) the seven entries are

    q*c0, q*c8, c_a, c_b, c_c, c_d, c_h.

Each is nonnegative and less than L/8. The new merged guard is exactly

    L^2 - 2 Q2 S0
        - 2(c_a^2+c_b^2+c_c^2+c_d^2+c_h^2) - 1
        = alpha^2+beta^2+gamma(gamma+1).                  (11)

Its left side is nonnegative by Lemma 1 with m=7, and hence has the displayed
ternary representation. The other two groups have size two. Keep every
other parent coordinate and multiplication wire, and fill the new wires
and ternary witnesses. This constructs a new zero. Old slacks and old
guard witnesses that no longer occur are harmless unused coordinates and
are removed by the exact projection.

This is existential equivalence over the common front. It is not a claimed
bijection between all auxiliary witness assignments; ternary representations
are nonunique.

## 5. Quadratic compilation and the additional saved variable

The separate four-group certificate is already quadratic. The unmerged
source removes eleven bound rows and eleven interval-certificate rows,
and inserts four quadratic certificates with twelve fresh integers. The
old 33 interval-certificate witnesses disappear. Integral monic projection
removes the unused old slacks and redundant gate definitions, yielding
261 variables and 185 rows.

In (11), Q2=q^2 already exists as the parent's wire `mul.520`. That wire was
previously eliminated by projection. The merged variant retains it and adds
one quadratic definition S0=r0^2+r8^2. The two seven-entry terms are then the
bilinear product Q2*S0 and five squares. One old ternary certificate loses
three witness variables, while two additional multiplication/sum wires
remain, saving one further variable. It adds one surviving residual, so the
result is 260 variables and 186 rows. A tested version with two separate
wires q*r0 and q*r8 has the same dimension but ten more collected terms;
the aggregate version is the selected endpoint.

The compiler factors the inherited Horn equations, applies only integral
monic substitutions that leave every residual quadratic, and records an
exact inverse restoration sequence. It then applies integral translations,
which are bijections of Z^n. Squaring and summing all residuals gives the
ordinary degree-four polynomial. The independent checker reconstructs the
complete altered source, every factorization and restoration, the exact
translation, and every collected coefficient. It also checks the domain,
that every variable occurs, and deliberate corruption cases.

The final comparison is:

| Endpoint | Integer variables | Quadratic rows | Monomials | Height |
|---|---:|---:|---:|---:|
| inherited strict_dimension_centered | 282 | 192 | 5,491 | 128,446 |
| grouped_centered | 261 | 185 | 5,332 | 128,446 |
| merged_aggregate_centered | 260 | 186 | 5,325 | 128,446 |
| merged_cap32_centered | 259 | 185 | 23,960 | 240,653 |

All have exact degree four. The 260-variable result saves 22 variables
and six rows against the latest inherited endpoint, while also reducing
support by 166 terms at unchanged height. The 261-variable companion uses
one fewer residual than the 260-variable endpoint. These are achieved
finite constructions, not lower bounds on possible future equations.

The 259-variable companion uses the identical merged semantic source. It
allows at most 32 terms in the restored polynomial during the same exact
monic elimination, in place of the default 16, and removes one additional
coordinate. Its certificate proves the same integer existential equivalence
and preservation of quadratic residuals. Its increased support and height
are explicit costs of saving that variable. Raising this implementation's
support cap to 64 or 128 produced byte-identical uncentered equations, as
recorded in `PROJECTION_CAP_COMPARISON.json`; this is a finite search result,
not an optimality theorem.

## 6. Attribution and further questions

The natural-domain pooled low-digit work in the incoming `conzfc_graph_digits`
packet supplies an important predecessor: it pools nonnegative remainders
using a shared sum bound. The present signed theorem instead uses a symmetric
quadratic bound and proves the signs by uniqueness of short modular lifts.
It requires the staged factorial bootstrap above; merely summing the old
signed interval inequalities would not suffice. The adjacent-denominator
merger uses q^(t+1)=q*q^t to amortize one more ternary certificate.

The directly inherited mathematical framework is recorded in the closure
map. The new contribution is Lemmas 1 and 2 as instantiated in the literal
signed source, their noncircular soundness schedule, the scaled merger and
the smaller fully materialized quartics. No literature-wide priority is
claimed for the elementary general lemmas.

The immediate next questions are whether additional denominator groups can
share a quadratic certificate with fewer new wires than the witnesses it
removes; whether the stronger margins permit another useful quadratic
form with smaller collected support; and whether the general signed
residue theorem can be formalized once and reused by the repository's
different arithmetic compilers. No such extension is assumed in the
released equivalence.

# Canonical signs extract the common square before natural quadratization

## Exact claim and retained boundary

All coordinates range independently over N={0,1,2,...}. The new raw source
has 310 coordinates and 262 quadratic residuals. The independently replayed
contraction gives a 206-coordinate/158-row dimension endpoint and a
208-coordinate/160-row sparse endpoint, before residual-basis optimization.
Each final equation is the sum of the literal squared residuals, hence is a
single polynomial of exact degree four. Its complete collected coefficients
are supplied, not an exponentiation or other implicit primitive.

The parent is the round19 even-horizon cofinal descending source, whose complete
ordinary proof and arithmetic/logical closure are retained under `inherited/`.
Relative to that retained C222/ZF/ZFC calibration, each new equation has a
natural zero iff there is a finite syntactic ZFC refutation. Consequently ZFC
proves its no-natural-zero statement equivalent to Con(ZFC). This is not a
proof of consistency, a global minimality claim, or a newly kernel-checked
end-to-end ZFC derivation. Finite exact checks establish the specified algebra;
the unbounded canonical-lift argument below establishes the new domain step.

## 1. The source polynomial is unchanged

Use the literal parent coordinate names, and abbreviate its nonnegative
representative-minus-one coordinates by a,b,c,d,S,Sp. Set

    delta0 = S-Sp,
    delta_i = S-Sp-m_i  (1<=i<=8),
    delta9 = a-c,             delta10 = b-c,
    delta11 = (a-c)^2(b-c)^2-(d+2)^2,
    delta12 = S-Sp-mul.358,
    delta13 = mul.363-mul.369,
    delta14 = mul.372-mul.373,

where (m1,...,m8) are the existing gates

    (mul.339,mul.341,mul.343,mul.345,mul.347,mul.349,mul.351,mul.353).

The old axiom/rule disjunction value is exactly

    R = product_(i=0..8) delta_i^2
          * (delta11^2+delta12^2) * delta13^2 * delta14^2.       (1)

Its local nonnegative source is R+beta1^2+beta2^2, where the two beta
differences are untouched. These are literal circuit identities: the old
rows `sqd.0` through `sqd.14`, `mul.355`, `mul.357`, and `mul.374` through
`mul.384` specify (1). The source-evaluation row is RETAINED, with its R
input replaced by the equal expression below.

Orient eleven affine factors as

    g_i=-delta_i (0<=i<=8),  g9=-delta13,  g10=delta14,
    Q=product_(i=0..10) g_i,  E=(a-c)(b-c),  D=d+2.

Ten successive product gates construct Q, starting with g0*g1; no separate
coordinate for an affine factor is needed. One gate constructs E. Three more
gates construct

    Z0=Q(E-D),       Z=Z0(E+D),       T=Q(-delta12).

The replacement local source is

    Z^2+T^2+beta1^2+beta2^2.                                 (2)

The identities Q^2=product delta_i^2*delta13^2*delta14^2 and
(E-D)(E+D)=E^2-D^2 show R=Z^2+T^2 over the integers, without any sign
hypothesis. Every defining row is quadratic, as are the final squares in (2).
Exactly 28 old square/product gates are replaced by 14 new product gates.
No original semantic coordinate, power, range request, Pell seed, frame atom,
endpoint, or label polynomial changes. The full local source polynomial,
and therefore its numerical majorant and logical zero set, is IDENTICAL.

The independent `check_source.py` verifies each of those literal gate rows,
all 247 otherwise unchanged rows, the retained evaluation row, both formal
factorization identities, natural domains and the raw census. Its negative
controls explicitly include accidentally omitting the source-evaluation row.

## 2. Soundness restores every old natural witness

Take an arbitrary natural zero of the new raw source. Retain all shared
coordinates. Restore each old `sqd.i` as delta_i^2, and restore `mul.355`
and `mul.357` by their nonnegative square/product formulas. Restore the
old chain `mul.374` through `mul.384` in its stated order. Every restored
value is natural, regardless of the signs of any delta or g. The exact
identity in Section 1 recovers the old evaluation row. Every other old row
was retained verbatim. Thus this is a natural zero of the complete parent.

Apply the parent soundness proof in its already justified acyclic order:
positive-center and pooled-bound restorations; shared scale and semantic
Pell anchor; six exact powers; even descending factorial bootstrap F=t!;
carry-free binomial ranges and reciprocal CRT decoding; the literal local
source bound; factorial-weight Horn-flow and the retained logical calibration.
The new product gate signs are not used to infer local rule signs or local
nonnegativity. Local nonnegativity follows from the EXACT SAME sum-of-squares
source polynomial (2)=(1)+beta1^2+beta2^2.

## 3. Canonical completeness supplies the new natural signs

It is NOT claimed that every old natural witness admits the new gates: a
particular old tuple can have negative partial products. Instead start from
a finite syntactic refutation and use the parent's constructive completeness
argument, making different, permitted CRT representative choices.

First choose the even horizon t>=4, F=t!, n=F^2-1, V=n^t and y=V-1. The
parent proof bounds the pending proof-tree products by (1+tF)^t<V and uses
F|y to obtain pairwise coprime beta moduli. Choose x by beta CRT and enlarge
it in its congruence class as required. Set B=binom(n,t) and N=B^x. All of
these choices precede the lifted column representatives.

The parent chooses positive representatives modulo N^2 for the encoded
columns. In the minus-one coordinate convention used here, adding any
multiple of N^2 preserves every such congruence and positivity. In particular
it preserves the precision needed for local polynomial evaluation and
binomial valuation divisibility. There are no parity or square conditions on
these natural representative coordinates.

Choose representatives for c,d,S,u,v and the encoded row index, satisfying
the inherited conditions. Then choose b in its required class with b>c.
Choose Sp in its required class with Sp>S. Finally choose a in its required
class, sufficiently large to satisfy all of the following finite conditions:

* a exceeds c+d+3;
* a is at least every already chosen nonanchor seed index and coordinate;
* (S+1)(1+F(a+1)) > (Sp+1)(1+F(b+1)).

These are lower bounds on a. Their feasible set contains a full tail, so its
intersection with the fixed class modulo N^2 is nonempty. In particular there
is no circular choice of N: N was fixed using only t,F,y,x and B.

Now check every new gate's sign using literal parent rows:

1. g0=Sp-S>0 and g_i=Sp-S+m_i>0 for 1<=i<=8. All m_i are original natural
   product gates. The branch factor -delta12=Sp-S+mul.358 is also positive.
2. Write M=mul.36. The literal product rows give

       mul.361=F(b+1),
       mul.363=(Sp+1)(1+F(b+1)),
       mul.364=F(a+1),
       mul.366=F(4+4b+2M),
       mul.368=(S+1)(1+F(a+1)),
       mul.369=(1+mul.366)mul.368.

   The last lower bound chosen for a makes mul.368>mul.363; hence
   g9=mul.369-mul.363>0.
3. The literal rows also give

       mul.370=F(6+4b+2M),
       mul.372=(Sp+1)(1+mul.370),
       mul.373=(S+1)(1+mul.361).

   Because mul.370-mul.361=F(5+3b+2M)>0 and Sp>S, g10>0.
4. b-c>=1 and a-c>d+3 imply E=(a-c)(b-c)>d+2=D. Thus E, E-D, E+D
   are positive, so all partial products, Z0,Z,T are natural.

Every old deterministic gate is evaluated using these representatives;
the old local source remains a nonnegative multiple of N by the inherited
precision-N^2 argument. The new equal source therefore uses the same natural
evaluation quotient.

## 4. The semantic anchor and remaining choices remain acyclic

The source's unchanged derived-label sum J obeys the literal constructor
bound J>=I(a+1,b+1)>=2(a+1)^2. The choice of a above dominates the fixed
indices t,x,y+1,n, all other representative indices, and the encoded row
index. Its own index is a+1. Hence J>=2 max_i k_i for every one of the
thirteen nonanchor seeds. This is exactly the parent's sufficient hypothesis
for natural completeness of the merged error-square cap. No lift of S or
Sp is performed after this anchor choice; in particular there is no demand
that S exceed J or any syntax weight.

Only after all these representatives are fixed, define the self-sized sum
S_base=1+C+A_a+A_b+A_c+A_d+A_S+A_Sp+A_u+A_v and q=(N*S_base)^x.
Every representative remains below S_base regardless of the size of its lift.
The literal label bound J<=S_base^(2^22) and the already proved
2^22(t+1)<x are unchanged. Thus every needed nonfactorial low coefficient
is at most S_base^x. Every factorial low coefficient is at most V<N. A pooled
level has at most five members, and

    5*S_base^x+N < N^x*S_base^x = q.

Consequently the four pooled low-digit budgets retain natural slacks exactly
as in the parent proof. Arbitrarily large representative lifts cause no new
carry problem because q is chosen afterward.

Next compute the denominator powers and frame W. Then choose its lower Pell
witness, A in the common-root congruence class sufficiently large, and the
principal, auxiliary positive-center, comparison and seed Pell witnesses.
The anchor dominance just checked supplies its merged-error quotient. None
of these choices changes a,b,c,d,S,Sp or the already fixed indices. This
finishes canonical completeness for the new natural raw source.

## 5. Contraction and literal quartics

The subsequent monic contraction is a different, stronger pointwise step.
Each eliminated coordinate has an explicit integer-polynomial restoration
certified as a rational sum of affine squares plus nonnegative monomials.
The independent parent checker verifies every certificate, substitution,
domain and full SOS expansion. These contractions therefore biject the
appropriate solution sets on the same natural domains; no canonical-lift
argument is silently substituted for a contraction certificate.

Any subsequent row-basis changes are invertible integer ROW shears, leaving
the coordinates and their independent natural domains untouched. Exact
inverse maps and complete coefficient collections are separately checked.

The new semantic reduction is square extraction combined with cofinal CRT
sign orientation. Its soundness is pointwise, but its completeness is only
canonical, which is all the refutation-to-zero equivalence needs.

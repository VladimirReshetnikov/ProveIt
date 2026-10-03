# The five-gate auxiliary quotient block and a paid positive-gap chart

No operation saving was found. In a precise independent-port model, the new auxiliary ordinate producer

    V = c(Tf−1)−Rf²

requires at least three nonconstant multiplications and two additions/subtractions. Its current five gates attain both bounds. This is a lower bound for that local polynomial with the stated paid ports, **not** a lower bound for either complete universal polynomial or for all zero-equivalent replacements.

The [helper](complete_auxiliary_quotient_block_scout.py) and [receipt](complete_auxiliary_quotient_block_scout.json) also contain eight complete literal sources. They read pinned current JSON; no predecessor Python, builder, historical census or archived program executes. The parent files remain unchanged.

| Complete source | M | A | Total | Degree claim |
|---|---:|---:|---:|---|
| Normalized85, original quotient producer |48|37|85|Exact175, inherited identical polynomial|
| Normalized85, Horner producer |48|37|85|Exact175, identical polynomial|
| Normalized85, flat producer |48|37|85|Exact175, identical polynomial|
| Normalized positive-gap chart, direct strong norm |49|39|88|Gate upper247 only|
| Normalized positive-gap chart, factored strong norm |51|40|91|Gate upper241 only|
| Ordinary86, original quotient producer |47|39|86|Exact131, inherited identical polynomial|
| Ordinary86, Horner producer |47|39|86|Exact131, identical polynomial|
| Ordinary86, flat producer |47|39|86|Exact131, identical polynomial|

All eight retain 18 strictly positive witnesses, the ordinary input, all six fixed compiler numeral ports, and every paid finalizer gate. The two gap forms rename the supplied f coordinate to g and restore f explicitly. The original same-polynomial forms have naive gate-degree bounds185 and141; those loose bounds do not replace the already proved exact175 and131.

## 1. Actual source and bounded interface

The parents are [normalized85](complete85_auxiliary_bezout_projection.md) and [ordinary86](complete86_ordinary_auxiliary_projection.md), with their actual complete saved packets. In both,

    c = R10a,  R = r_lhs,  T = auxiliary_quotient,
    f² = L16,  V = aux_u_rhs.

The parent source already pays f² for its strong factor. It also pays c² and Delta*c² for the main factor. The new V uses exactly

    Tf; Tf−1; c(Tf−1); Rf²; c(Tf−1)−Rf²,

or3M+2A. The four internal registers in this display have no consumers outside this producer. V itself feeds its square and hence the auxiliary norm. The helper authenticates the literal consumers and the paid square before rewriting.

The two tested exact alternatives are

    V = f(cT−Rf)−c,
    V = (cTf−c)−Rf².

They each also cost3M+2A. The complete circuits retain all existing uses of f², c² and the strong coefficient; no apparent saving is obtained by discarding a still-live square. These are two displayed reassociations, not an exhaustive arithmetic search.

For the lower bound only, c,T,R,f are algebraically independent. Initially available ports are 1,c,T,R,f,c²,f²,Delta,Delta*c², with Delta also independent. Rational constants are free; there is no division. A claimed polynomial identity using the Delta ports can be specialized at Delta=0 without adding gates, leaving c² and f². This specialization is an algebraic lower-bound device. It does **not** assert that the actual compiler's computed Delta is zero, constant or independent of its other fields.

Other actual paid core registers, the seven factor equations, and the complete product finalizer are outside this local model. In particular the bound says nothing about a cheaper whole-core schedule exploiting those dependencies, a different auxiliary coefficient, a supplied-coordinate projection, or a polynomial with merely the same positive zeros.

## 2. Three multiplications are necessary, including higher-degree intermediates

Allow arbitrarily many additions and scalar operations. After Delta=0, every expression available before a nonconstant multiplication is in the vector space

    L = Affine(c,T,R,f) + span(c²,f²).

Suppose at most two nonconstant multiplications compute V. Write their outputs as

    Q1 = u v,                    u,v in L,
    Q2 = (u' + alpha Q1)(v' + beta Q1),  u',v' in L.

The final output is in L+span(Q1,Q2). Constants, zero products and multiplication by a scalar can be absorbed into these vector spaces. Thus this normal form allows arbitrary intervening additions and includes operands involving paid quadratic ports and Q1.

Every cubic homogeneous part of a product of two elements of L belongs to

    c²*Lin(c,T,R,f) + f²*Lin(c,T,R,f).                    (1)

This space does not contain the monomial cTf. Consequently one product cannot compute V. Nor can two products independent of each other, **even if their quartic parts cancel**: the cubic part of their sum is still in (1).

Consider a genuinely used Q1 with degree greater than2. Its degree is3 or4. If both Q2 operands contain Q1 with nonzero coefficient, Q2 has degree at least6; its leading term cannot cancel against L or Q1. If exactly one operand contains Q1 and the other is nonconstant, the highest degree is deg(Q1)+deg(other)>deg(Q1). The part not containing Q1 has smaller degree, so again the top term cannot cancel. A constant other operand only produces a linear combination of Q1 and L. If neither operand uses Q1, the independent-product argument applies. These cases exclude useful first products of degree greater than2 without assuming homogeneous gates or forbidding cancellation.

If deg(Q1)<2, it lies in L. If deg(Q1)=2 but its quadratic part lies in span(c²,f²), it also lies in L and is redundant. Therefore a useful first product has degree2, comes from two affine-linear operands, and has quadratic part q that is a product of two linear forms and is not in span(c²,f²).

Both Q2 operands now have degree at most2. If both had nonzero quadratic parts, Q2 would have a nonzero quartic part, impossible because neither L nor Q1 has degree4. Thus one operand is affine-linear. Independence of q,c²,f² shows that canceling an operand's quadratic part cannot leave a hidden Q1 contribution. Since the target cubic is nonzero, its cubic part must have the form

    ell * (alpha q + lambda c² + mu f²)
       = f(cT−Rf).                                      (2)

The homogeneous quadratic C=cT−Rf has rank4, so it cannot be a product of two linear forms; hence it is irreducible. Unique factorization in the polynomial ring forces ell to be proportional to f. Equation (2) would then imply that some

    cT−Rf + lambda' c² + mu' f²                         (3)

is a product of two linear forms. In the variable order c,T,f,R, its symmetric coefficient matrix is

    [ lambda'  1/2       0       0   ]
    [ 1/2       0        0       0   ]
    [ 0         0       mu'    −1/2  ]
    [ 0         0      −1/2      0   ].

Its determinant is identically1/16, for every lambda',mu'. Thus (3) has rank4, whereas a product of two linear forms has rank at most2. This contradiction proves the three-multiplication lower bound. The checker expands the determinant as a polynomial in both parameters; sampling parameters is not the proof.

## 3. Two additions/subtractions are necessary

Now allow arbitrarily many multiplications and free rational constants, but at most one addition/subtraction. Before that gate every nonzero register is a monomial. Afterwards each available expression is a monomial times a nonnegative integral power of the one binomial formed at that gate. The initially paid c²,f² are themselves monomials; setting Delta=0 causes no new addition.

The polynomial

    V = cTf−c−Rf²

is irreducible over Q[c,T,R,f]. Viewed as a polynomial in R over Q[c,T,f], it is primitive because

    gcd(f²,c(Tf−1)) = 1;

it has degree1 over the fraction field, so Gauss's lemma applies. Since V has three distinct monomials, it cannot be a monomial times a power of a single binomial: irreducibility would require that power to be1 and the monomial to be a unit, leaving only two monomials. At least two additions/subtractions are necessary. Together with Section2, the current3M+2A schedule is optimal in the declared local model.

This is distinct from the earlier [five-gate auxiliary-norm bound](auxiliary_norm_five_gate_lower_bound.md), which treats K*V²−(K−1)y² with independent K,V,y. The two component bounds cannot simply be added into a whole-circuit lower bound; sharing or different interfaces may couple them.

## 4. A sound positive coordinate change, fully charged

For the normalized source write

    t = i c²,  a = R12,
    Delta = a²+4a+3 = (a+1)(a+3),
    Ns = f²−Delta*t².

At every positive parent zero, Ns=1 by the parent's proved unit theorem. Since f,t,a>0,

    f²−(a+1)²t² = 1+2(a+1)t² > 0,

and therefore the new coordinate

    g = f−(a+1)t

is a strictly positive integer. Conversely, every positive new tuple restores

    f = g+(a+1)t > 0

unconditionally. Substituting this formula into the entire old polynomial gives an exact signed polynomial graph identity, and these maps restrict to inverse bijections on the complete positive zero sets. The argument uses the full parent domain, not only canonical Pell fibers.

In the literal source t is already paid. Restoring f adds

    a+1; (a+1)t; g+(a+1)t,

namely1M+2A. The direct-substitution source consequently costs88=49M+39A. It includes both retained f consumers, f² and Tf. Omitting either restoration or the square needed by V would miscount the chart.

The alternative factored strong identity is

    Ns = g² + 2(a+1)t(g−t).

With b=(a+1)t already paid for f, it is evaluated as g²+2b(g−t). Simultaneously the auxiliary coefficient can be computed as

    Kaux = [i*(Delta*c²)]²,

using the paid main port Delta*c². The checker authenticates the actual identities Delta=a²+4a+3 and t=ic² before applying these cuts. The old private t², Delta*t² and coefficient gates disappear; the complete new count is nevertheless91=51M+40A. This is a second paid chart, not a claim that its particular strong-norm schedule is optimal.

The chart above is asserted only for normalized85. The ordinary86 strong equation is t²=Delta(f²−1), so the same inequality for f−(a+1)t is unavailable. No ordinary positive chart is inferred by analogy.

## 5. Evidence and limits

Seven predecessor byte pins include both complete author trios and the older isolated-norm proof. All eight full output arrays are saved, with all692 gates live and every supplied port used. The source rewrites preserve every untouched row literally; the exact local V identities, the strong-gap identity and the auxiliary coefficient identity therefore lift to the complete finalizers. These cut identities are checked by sparse coefficient arithmetic, independently of the finite evaluations.

The receipt also records384 complete signed evaluations, including192 rational assignments,32,016 retained register equalities, and48 exact positive strong-component Pell cases. The latter use small component parameters and are not complete native/compiler zeros. No enormous full Pell tuple is materialized. The degree upper bounds of the two gap charts are only literal gate bounds; no exact degree is claimed for them.

This bounded scout supplies neither a better universal operation count nor an obstruction to every possible improvement. It identifies a paid local minimum for the exact quotient producer and two valid but more expensive normalized coordinate implementations. In particular it does not justify deleting either congruence encoded by the Bezout parameterization, replacing supplied ic² divisibility by an unconstrained port, or treating a merely canonical inverse as valid on all positive zeros.

Reproduce without predecessor execution:

    python3 complete_auxiliary_quotient_block_scout.py --root /path/to/native-stream-queue --expect complete_auxiliary_quotient_block_scout.json

The same exact receipt replay works with python3 -O. Checks use explicit exceptions, including recursively type-exact receipt comparison; assertions are not relied upon. Writer and fresh normal/optimized replays from / pass.

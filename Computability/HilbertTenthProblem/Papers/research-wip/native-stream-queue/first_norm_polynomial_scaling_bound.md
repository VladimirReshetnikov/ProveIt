# Arbitrary polynomial scaling cannot shorten the first norm below five gates

Every nonzero polynomial multiple of the current first-norm polynomial requires **at least three multiplications and at least two additions/subtractions** at its six dependent paid ports. This includes every nonmonomial positive polynomial multiplier. It extends the monomial-only bound; it does not establish a minimum for the complete 84-operation polynomial.

The precise interface consists of

    T, X, Y, k, E=XY, Z=kY,
    P=T²−(EZ)(EZ+k)=T²−X²Y⁴k²−XY²k².

Here T,X,Y,k are algebraically independent over the rationals, and E,Z have exactly the displayed dependencies. Let G be any nonzero element of Q[T,X,Y,k]. Any division-free arithmetic circuit with these six ports, fixed rational constants, and binary addition, subtraction and multiplication that computes **G*P** requires at least 3M and at least 2A. The multiplier is not an additional free input. The separate bounds allow arbitrarily many operations of the other kind.

G may have arbitrary degree, signs, coefficients and support, including factors of P itself. No positivity assumption on G is needed for the arithmetic bound. G=1 attains five gates; attainment at five is not claimed for other multipliers.

## 1. Literal current-source boundary

In the pinned `complete84_scaled_strong_output.json`, bind

    T=tau_root, X=wn2, Y=sn2, k=R10b,
    E=UM, Z=ksn2.

The retained source literally pays

    UM=wn2*sn2;
    ksn2=R10b*sn2.

The five component rows are

    tau_square=T*T;
    first_root_base=E*Z;
    first_next=first_root_base+k;
    first_product=first_root_base*first_next;
    norm_first=tau_square−first_product.

Their count is 3M+2A. All seven definitions are authenticated by the fresh checker and expanded at the four independent boundary variables. The two paid products are dependent monomials, not independently variable substitutes. The local theorem does not import any Pell equation, history property, first-index equation or valid-compiler specialization.

## 2. A generic specialization reduces every multiplier

Give all affine operations for free; proving a multiplication bound in this relaxed model suffices. Let d be the total degree of G in T,X,k, treating its coefficients as polynomials in Y. Choose a coefficient of that maximal degree which is a nonzero polynomial in Y. There exists a nonzero rational t at which this coefficient is nonzero: only finitely many rational choices are excluded. Thus

    G_t=G(T,X,t,k) != 0,
    degree_(T,X,k)(G_t)=d.

If d=0, this choice simply ensures G(t) is a nonzero rational scalar.

After Y=t, every available port is affine in T,X,k: E=tX and Z=tk. The target is

    G_t*P_t,
    P_t=T²−t⁴X²k²−t²Xk².

Because t is nonzero, P_t has degree four. Polynomial degrees add in this integral domain, so the target degree is d+4. A circuit with at most two multiplication gates and any number of affine operations has degree at most four. Therefore d>0 immediately excludes two multiplications.

It remains to exclude two multiplications for a nonzero scalar multiple of P_t. Normalize that scalar for free in the relaxed model. The following argument includes the actual nonzero t coefficients; it does not assume the multiplier survives Y=1.

## 3. The scalar quartic still needs three multiplications

With at most two products and free affine operations, a degree-four output must have the form

    h*(alpha*Q+u)*(beta*Q+v)+b*Q+z,             (1)

where Q is the first product of two affine forms, u,v,z are affine in T,X,k, and h,alpha,beta are nonzero rational constants. A degree-four output needs the second product, both its operands must involve Q, and its nonzero output coefficient h cannot be discarded. All additions before, between and after the products are absorbed into this form.

Its quartic homogeneous part is h*alpha*beta*Q_2², whereas P_t has quartic part −t⁴X²k². Unique factorization makes Q_2 a nonzero scalar multiple of Xk. Since Q itself is one product of two affine forms, their nonzero linear parts are proportional to X and k, in either order. Consequently

    Q=qXk+rX+sk+z0, q!=0,

with no T term. Allowing arbitrary q,r,s,z0 only relaxes the possible family.

Set X=0. Q is affine, so bQ+z contributes no quadratic terms. The target becomes T². Thus the product of the linear parts of the second-product operands is a nonzero multiple of T² in Q[T,k]. Each linear part must itself be a nonzero multiple of T. In particular, if u_k,v_k denote the k coefficients in u,v, then

    alpha*s+u_k=0, beta*s+v_k=0.                (2)

Returning to general X, the two operands in the second product contain only Xk, X, T and constant terms. Their product has no Xk² term; neither bQ nor z can supply one. Explicitly the coefficient of Xk² in (1) is

    h*q*[alpha*(beta*s+v_k)+beta*(alpha*s+u_k)]=0

by (2). Its coefficient in P_t is −t², which is nonzero. This contradiction excludes two products in the remaining case, and proves **M>=3 for every nonzero polynomial G**.

## 4. One addition cannot produce any polynomial multiple

All six paid ports are monomials in T,X,Y,k. In a circuit with at most one addition/subtraction, every value before that operation is a scalar monomial. Its output is a binomial, possibly degenerate. Every subsequent nonzero value is therefore

    scalar * monomial * B^n, n>=0,             (3)

where B is that one binomial. This induction permits arbitrary squaring, reuse, multiplication and fixed scalar operations.

P is irreducible. Regard it as a monic quadratic in T over Q[X,Y,k]. Its radicand is

    (kY)² X(XY²+1).

The valuation of this radicand at the irreducible polynomial X is exactly one, so it is not a square in Q(X,Y,k). The quadratic is irreducible over that fraction field, and monicity and Gauss's lemma imply irreducibility in Q[T,X,Y,k]. Also no variable divides P.

We next show that P cannot divide any nonzero binomial. Its three support exponents, in coordinates (T,X,Y,k), are

    (2,0,0,0), (0,2,4,2), (0,1,2,2).

Their affine span has dimension two. The following elementary width argument supplies the needed factor obstruction without assuming anything about G.

For a nonzero polynomial f and any rational weight vector w, let width_w(f) be the largest w-weight of a support exponent minus the smallest. In a polynomial ring over a field, both highest-weight parts and lowest-weight parts multiply without becoming zero. Hence

    width_w(fg)=width_w(f)+width_w(g).          (4)

For a binomial B, choose w orthogonal to the difference between its two exponent vectors. Then width_w(B)=0. Because P's support differences span dimension two, some rational vector w orthogonal to the one binomial difference is not orthogonal to all support differences of P. For that w, width_w(P)>0. If P divided B, (4) would contradict width_w(B)=0. A monomial or constant B is excluded in the same way by choosing any w for which P has positive width.

Now suppose G*P had form (3). In the polynomial unique-factorization domain, irreducibility makes P prime. It cannot divide the scalar monomial, and so would have to divide B. That is impossible. This includes G having additional factors of P, binomial powers with arbitrarily large n, and arbitrary cancellation among terms of G. Thus **A>=2 for every nonzero polynomial G**, independently of the number of products.

## 5. Consequence for complete-source scaling, and limits

Write the complete source as

    F84=P*N−Delta,

where N is the product of the other six actual factors. Formally replacing P by G*P and the final offset by G*Delta gives G*F84. If G is nonzero everywhere on the relevant positive domain, the complete positive zero sets coincide. Nonmonomial examples such as 1+X²+Y² fall within the new component obstruction just as monomials do.

This does not make the final offset, multiplier, remaining factors or their products free. The component result says that computing the scaled first factor from only the six declared ports cannot use fewer than five gates, even if the rest of such a scaling were free. Hence this route cannot improve the current source merely by replacing its isolated five-row first-norm component with a scaled version.

Extra already paid registers, shared computation with another factor, rational-function multipliers, changed coordinates, and polynomials agreeing only on constrained zero sets are outside this theorem. A multiplier that is formally nonzero may vanish at some positive assignments, so no zero-set equivalence is asserted without the stated nonvanishing condition. No new complete circuit, fixed-program recipe, universality theorem, exact full degree or global 84-operation lower bound is claimed.

## 6. Inert provenance and bounded fresh evidence

The standalone helper authenticates the seven files below as bytes. It reads the complete 84 JSON source as inert data, records its complete-array digest, and authenticates the literal dependent producers and five-row component. No predecessor code is executed or imported.

| File | SHA-256 |
|---|---|
| complete84_scaled_strong_output.py | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| complete84_scaled_strong_output.json | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| complete84_scaled_strong_output.md | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |
| first_norm_monomial_scaling_bound.py | `8f938efc5e1690d173bd9524cf83b60d3b78b2146be11593771632f44b0a3f58` |
| first_norm_monomial_scaling_bound.json | `b687e870b6a841f178c238399688f42ddd43640692d034526cf6b15b6a63c238` |
| first_norm_monomial_scaling_bound.md | `1a7677200ada8b171268aeb5189a9477dc2c9a3743fffb6e1f4d3de11dd3be4c` |
| first_norm_five_gate_lower_bound.md | `3f7580635b63b6cc7bda27b23022db99c85fdc4341c34ea1fb5d55f42e00c2fc` |

Fresh exact sparse arithmetic expands P and its radicand, verifies the odd X valuation and a nonzero support minor, and independently derives all three X=0 quadratic coefficients and the forbidden cubic coefficient of the general two-product form. After the forced coefficient substitutions, that cubic coefficient is identically zero. Twelve finite polynomial multipliers corroborate the generic specialization and product-degree formula, including examples vanishing at Y=1 and G=P or P². These examples do not establish the unrestricted theorem; Sections 2–4 do.

The receipt binds the helper bytes. Its parser rejects duplicate keys and noninteger JSON numbers; required checks use explicit exceptions and remain active under optimized Python. The fresh helper has no symbolic-library dependency.

Replay from any directory with the installed predecessor files:

    python3 first_norm_polynomial_scaling_bound.py --root ABS_WIP --expect first_norm_polynomial_scaling_bound.json
    python3 -O first_norm_polynomial_scaling_bound.py --root ABS_WIP --expect first_norm_polynomial_scaling_bound.json

The writer and fresh normal and optimized exact replays from working directory `/` passed. Root independently read the entire proof and helper and found no correction. These checks do not execute any predecessor.

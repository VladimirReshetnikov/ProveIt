# Polynomial scaling cannot shorten the native index/transport cut

Every nonzero polynomial multiple of the actual index/transport product needs at least **4 multiplications and 5 additions/subtractions** at its declared nine-input cut. The original product attains nine gates. If the multiplier depends on the simultaneous translation of the two index coordinates, the minimum rises to **5M+5A=10**, and a simple multiplier attains it.

This extends the earlier exact-product theorem to arbitrary polynomial multipliers at the same inputs. It gives no cheaper universal source and no lower bound for circuits using additional donor registers, changing coordinates, or preserving only the complete positive zero set. The established universal source remains 84 operations.

## 1. Actual target and arithmetic model

Use the same paid cut as `complete84_index_transport_joint_boundary.md`:

| Symbol | Source register or supplied value |
|---|---|
| k | R10b |
| R | r_lhs |
| E | UM |
| h | h |
| w | w |
| C | marked_rhs |
| U | q_minus_F |
| t | transport_quotient |
| r | repunit |

The fixed scalar K=Kconstant is nonzero on every authentic compiler slice. The factors are

    N=k−R−hE,
    T=(K+w)C+U−tr,
    J=N*T.                                              (1)

The symbol J here is the joint factor, not the repunit witness Jrep. Let the coefficient field have characteristic zero. For any nonzero polynomial H in these nine cut inputs, consider a division-free arithmetic circuit computing HJ. Arbitrary scalar constants, reuse and cancellation are permitted; every binary addition, subtraction or multiplication costs one operation. No extra computed value, free division or fused operation is allowed.

The exact-product predecessor proves 4M+5A for H=1. Its proof did not cover arbitrary H. The addition argument below uses the same support invariant, while the new multiplication argument avoids degree-by-degree circuit cases and applies to every multiplier at once.

## 2. A directional-derivative bound for multiplication circuits

For a polynomial P in n independent variables define the vector space

    W(P)={v in k^n : the directional derivative D_v P is a scalar}.

Constants, including zero, are allowed derivatives. Since differentiation and the scalar-subspace condition are linear in v, this is indeed a vector space.

**Lemma 1.** If P is computed with m multiplication gates whose two operands are nonconstant, allowing all affine operations for free, then

    codimension W(P) <= 2m.                            (2)

**Proof.** Order the counted product gates as g_1,...,g_m. Before each gate, every available wire is an affine combination of the original variables and the preceding g_i. Consequently each of its two operands can be written as a homogeneous linear form in the original variables, plus a scalar and a linear combination of preceding product outputs. Collect the linear forms from these representations, at most 2m of them, as ell_1,...,ell_(2m). Induction shows that every g_i is a polynomial in those forms. The final output has the form

    P=Q(ell_1,...,ell_(2m))+ell_out+c,

where ell_out is one additional homogeneous linear form. For every v annihilating all ell_i, D_v P=ell_out(v) is scalar. Thus their common kernel is contained in W(P), so its codimension is at most the dimension of their span, at most 2m. This also covers cancellations, unused gates, linearly dependent forms and counted products whose outputs happen to simplify to affine expressions. ∎

This relaxes the actual gate model: scalar products and additions are free only for this multiplication lower bound. The number of charged multiplications in the real model is at least m.

**Lemma 2.** Let A and B be nonconstant polynomials and H nonzero. If D_v(HAB) is scalar, then it is zero and D_v A=D_v B=0.

**Proof.** The claim is immediate when v=0. Otherwise choose invertible linear coordinates (z,y_1,...,y_(n−1)) with D_v=partial/partial z. Characteristic zero implies that a nonzero scalar derivative would make HAB=c*z+d(y), with c a nonzero scalar. Such a polynomial cannot have a nonconstant factorization: degree in z forces one factor to be independent of z, and that factor must divide the unit leading coefficient c. But (HA)*B is a product of two nonconstant polynomials. Hence the derivative is zero. Then HAB is independent of z. Nonzero polynomial degrees in z add under multiplication over the integral domain k[y], so A and B are each independent of z. ∎

The proof does not require A or B to be irreducible, relatively prime, or homogeneous. The nonconstant-factor hypothesis is essential: an affine polynomial itself has constant directional derivatives.

## 3. All multiplier cases need four products

Apply Lemma 2 to P=HNT. The equations for a direction v preserving both factors are

    D_v N=v_k−v_R−v_h E−h v_E=0,
    D_v T=v_w C+(K+w)v_C+v_U−v_t r−t v_r=0.

Comparing coefficients in the independent inputs gives

    v_h=v_E=v_w=v_C=v_U=v_t=v_r=0,
    v_k=v_R.

Their common kernel is exactly the one-dimensional line generated by

    e=e_k+e_R.

Therefore W(HJ) is contained in this line, so its codimension in the nine-dimensional input space is at least eight. Lemma 1 proves m>=4. This argument allows arbitrarily high-degree multipliers and arbitrary circuit cancellations; no degree cap or finite search is involved.

There is also an exact refinement. Since D_e J=0,

    D_e(HJ)=J*(partial_k+partial_R)H.

By Lemma 2 any scalar derivative of HJ must vanish. The polynomial ring is an integral domain. Hence

    W(HJ)=span(e) if (partial_k+partial_R)H=0,
    W(HJ)={0} otherwise.                              (3)

In the second case its codimension is nine, and Lemma 1 gives m>=5. This is a condition on the actual multiplier, not on its degree. For example H=k meets the second condition; H=1 meets the first.

## 4. At least five additions survive every multiplier

A circuit with a additions/subtractions and any number of products has output support of affine dimension at most a. To prove this, maintain one vector space containing every difference of exponents within the support of every wire. Initially each nonzero input is a monomial and the space is zero. A product adds two support translates without enlarging their common direction space. An addition requires at most one new direction, the displacement between the two translates. Cancellation can only remove support points. Scalar and zero wires cause no problem.

Because K!=0, the support of J contains the six distinct monomials

    kC, RC, hEC, kwC, kU, ktr.

Relative to kC their exponent differences are

    R−k, h+E−k, w, U−C, t+r−C.

The symbols on this line denote exponent-basis vectors. Projection to coordinates R,h,w,U,t gives the identity matrix, so these five differences are independent. Thus the Newton polytope of J has affine dimension at least five.

For nonzero polynomials over a field,

    Newt(HJ)=Newt(H)+Newt(J).

A generic weight exposes a unique vertex in each factor; the product of its nonzero coefficients exposes the corresponding sum vertex. This proves the equality even when other terms cancel. The Minkowski sum contains a translate of Newt(J), so its affine dimension is at least five. The support invariant therefore forces at least five additions/subtractions for every HJ.

Combining the separate bounds proves

    M>=4 and A>=5 for every nonzero H,
    M>=5 and A>=5 if (partial_k+partial_R)H!=0.        (4)

## 5. Attainment and binding to the real source

For H=1, the existing schedule is

    hE=h*E; n0=k−hE; N=n0−R;
    kw=K+w; cprod=kw*C; t0=cprod+U;
    tr=t*r; T=t0−tr; J=N*T.

It costs 4M+5A. Thus the minimum across all nonzero polynomial multiples is exactly nine. For H=k append Jscaled=k*J, costing 5M+5A. Since (partial_k+partial_R)k=1, ten is the exact minimum across the second multiplier class. These are minima across their specified classes; not every multiplier attains them.

The cut is genuinely algebraically independent on each fixed compiler slice. For completeness write m=Bm1, ell=twice_cell_bits, retain the shifted source port MF, and hold x,eta and the unused supplied parameters fixed. The actual producers give

    r=m*Jrep, q=r+1, U=q−F,
    E=w*s*q^4,
    R=(qU−Z)(q²−1)+(MC+q*MF)*Jrep,
    C=U−Z−alpha−ell*x, k=eta+zeta.

On the nonempty rational locus w*q*(q²−1)!=0 they have the inverse

    Jrep=r/m, F=q−U,
    Z=qU+((MC+q*MF)*r/m−R)/(q²−1),
    alpha=U−Z−ell*x−C,
    s=E/(w*q^4), zeta=k−eta,

with h,w,t unchanged. This proves independence before imposing any norm or source-zero equation. The proof uses rational inversion only to establish independence; it neither adds a division gate nor reconstructs positive witnesses.

In the actual complete84 graph, the two factor producers cost eight gates and one further multiplication forms their joint product. Reassociation with the exterior factors can expose this nine-gate block without changing the whole count. Every upstream producer and all other consumers remain charged. The proof does not grant access to q, individual products hE,wC,tr, or any other donor beyond the nine cut inputs.

Multiplying this joint factor does not by itself preserve the complete product-minus-discriminant equation. Even a multiplier nonzero on every relevant positive tuple needs a separate full-output equivalence argument before a source change is justified. The lower bound applies whether or not such an argument exists; it is not a certificate that these local multipliers preserve universality.

## 6. Evidence and limits

The full exact-product predecessor and its rational independence proof were read as inert mathematical text. The six-port scaled-finalizer note was read through Section 4's start for the already established support/Minkowski method. The actual84 JSON was read only as static definitions and supplied ports; no saved array was evaluated. Exact byte bindings and read scopes accompany this proof note.

Root derived Lemmas 1–2 and their application; an independent peer checked the directional-space argument and the refinement before the full note was written. Final full-note review is a separate record. No numerical or finite circuit search is used to establish any quantified bound.

No previous claim is refuted or dropped: the older nine-gate result remains correct at H=1 and is extended to the stated multiplier family. Arbitrary rational charts, extra donors, cross-factor sharing, different positive-zero equations and redesigned computational substrates remain outside this theorem. No supplied, archived, frozen or predecessor helper or source array was executed or imported. The universal84 arithmetic frontier is unchanged.

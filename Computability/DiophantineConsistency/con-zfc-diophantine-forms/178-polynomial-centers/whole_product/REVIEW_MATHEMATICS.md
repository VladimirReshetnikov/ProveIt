# Independent review of the 116-operation, degree-208 equation

This is a separate AI-assisted mathematical and artifact review. It is not
external human peer review or an end-to-end proof-assistant compilation.
The exact graph reviewed is identified by the SHA-256 in
`INDEPENDENT_REVIEW.json`.

## Conclusion

The literal whole-product center is an integer polynomial, its norm scaling
is correct, and its signed transport and positive-completeness arguments
are valid relative to the explicitly retained parent calibration. The exact
degree is 208 and the operation count is 116. All ten quantified coordinates
remain strictly positive integers; all four fixed coefficient integers are
unchanged. No zero or absence of zeros is established separately.

## Independent algebra and graph audit

`review_graph.py` imports neither `build.py` nor the component verifier.
It independently expands all 31 new gates in the polynomial ring
Z[A,Y,k,U,b,c], recovers every unchanged parent gate, checks whole-graph
liveness, and authenticates the actual fixed numeral bytes. Its small
polynomial helper is retained with attribution in `review_poly.py`.

For F=EV, define Qj as the polynomial quotient of F by A^j in this ring.
The script reconstructs the quotients independently by monomial exponents
and verifies exactly

    W4=U(4AF-2Q1-Q3/2).

It also checks that Q3 has even coefficients. This integrality follows
structurally from

    F=(b-c)E+2U²b(A²-1)E²,

since E has A-degree two. Thus Q3/2 is an integer polynomial, and the
delivered circuit expresses it without a division gate.

The actual graph is equivalent to the following explicit center:

    S=(kY)[ell+k-(kY)(Y+1)],  e2=(kY)²,
    theta=U²b,
    Rc=theta(3E+e2)-(b-c),
    Sc=4E²+3S²+e2²,
    W4=U[2S Rc+A(4EV-theta Sc)].

Here S is the polynomial quotient of E by A. The identity between this
formula and the independent quotient construction holds in the free
integer polynomial ring, not merely on a putative zero set.

The center is subtracted at the carrier level. Accordingly Z is exactly
Z0-MW4, where Z0 is the square-transport parent numerator. The norm uses
16G. The actual output is therefore

    (Q-1)(Z0-MW4)²-16M²G(QV²-1).

No sign condition has been added to the polynomial.

## Signed bounds without assuming a positive rank

The parent root extraction, strong-pair relations and index exclusions
give, before proving B>=0,

    G=g², z=±4gy, QV²-(Q-1)y²=1,
    g<f/6, |b|>8f³-1/2>7f³, f>128,
    y<3|V|/2, |V|<3f|b|/2.

The factor 16 changes prime valuations by an even amount. It therefore
does not affect extraction of the square G. The rational adjacent-Pell
descent applies to y=|z|/(4g), with the same Q and V as before.

Here is a direct majorant proof for the new center. Write

    E=e2 A²+e1 A+e0,
    e2=k²Y²,
    e1=k²Y(1-2Y-2Y²),
    e0=1+k²Y(Y+1)[Y(Y+1)-1].

On the positive domain, e2,e0>0, e1<0, and A>33Y. Consequently

    |e1|/(e2 A)=(2Y+2-1/Y)/A<4/33<1/3.

For Eabs=e2 A²+|e1|A+e0, this implies Eabs<2E: indeed
3|e1|A<e2 A², so 2|e1|A<E, while Eabs=E+2|e1|A.

A coefficientwise absolute majorant for F is

    Fabs=|b-c| Eabs+2U²|b|(A²+1)Eabs².

The root bounds give |b-c|<2|b| and |V|>f|b|/2. Using
f>2(A²-1)U²E, one obtains

    Fabs/|EV| < 8/f + 8(A²+1)/(A²-1) < 10.

The last bound already follows from f>128 and A>=16; the actual positive
domain has A>=1057. For each j, polynomial truncation gives
|Qj|<=Fabs/A^j. Therefore

    |W4-4AUF|
      <= U Fabs(2/A+1/(2A³))
      < 10U|F|(2/A+1/(2A³))
      < (1/2)AU|F|.

The final inequality holds for every A>=16. Thus W4 has the sign of V,
and, writing C0=AUE,

    (7/2)C0|V|<|W4|<(9/2)C0|V|.

The already proved estimate C0<3g/2 now yields

    4gy+|W4| < (51/4)g|V|
               < (17/8)f|V|
               < (51/16)f²|b|
               < (51/(112f))b² < b²/4.

This is an absolute estimate and covers V<0 as well as V>0.

## Bootstrap, denominator order and completeness

The inverse correction continues to satisfy rho<|b|/q⁶ uniformly in R.
The exact carrier relation is

    z=n+kappa+sigma-(1+hb²)B/h-rho-W4.

If B<=-1, the transport term is less than -b². The preceding absolute
budget and |b|/q⁶<b²/2 would force n<0. Hence B>=0. Only afterward are
the positive-rank mask bounds and the remaining index recovery invoked.

The new center W4 is integer-valued, so its subtraction leaves unchanged
the fractional-part relation used by the inverse-correction proof.
In particular the order remains: q^4 index congruence, whole-product
projection, proof that q is dyadic, then cancellation of the possible
factor 3 and full q^6 denominator recovery. No premature integrality
assumption is introduced by the scale four.

For canonical complete witnesses V is positive, and hence W4 is positive.
The parent estimate g>kappa+sigma+|rho| makes

    n=4gy+W4+(1+hb²)t+rho-kappa-sigma

a positive integer. This constructs the actual positive coordinate n and
does not assert that an arbitrary shear preserves positivity.

## Exact degree and cost

In the independent ring, the weights of A,Y,k,U,b,c are 4,2,1,7,4,3.
The complete defect W4²-16GV² has weighted degree 106 and leading part

    8A^8Y^8k^8U^6b²-48A^6Y^12k^8U^6b².

The center itself has weighted degree 65. With square transport,
deg Z0=21, deg M=11 and deg Q=80. Thus the unique dominant full-output
contribution is QM² times that defect, of degree 208. The other output
terms have degrees at most 177,152,122,72.

The independent checker substitutes the complete dependent leading forms,
including b0=q0 B0, rather than treating the six interface symbols as
algebraically independent at the end. It obtains the full nonzero component

    9*2^11*q0^88*w^18*s^52*i^10*k0^32*B0²*(w²-6s²),

where q0=beta J, k0=eta+zeta, and
B0=k0 sT-q0²(q0-F). The coefficient is 9*2^11 for scale four;
using the scale-eight coefficient would be an error.

The graph contains exactly 71 multiplications, 24 additions and
21 subtractions, total 116. All 116 operations, all ten inputs and all
four fixed numeral ports are live. These are exact finite algebraic checks;
the inherited unbounded arithmetic and logical calibration remain named
proof dependencies.

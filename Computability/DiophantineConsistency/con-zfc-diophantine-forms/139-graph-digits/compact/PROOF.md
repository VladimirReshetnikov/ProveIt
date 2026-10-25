# A lower center for the doubled product square

## Result, baseline, and exact scope

This component is a new ten-positive-variable polynomial with 87 live binary
arithmetic operations and exact total degree 323. Its baseline is package
133's complete 85-operation, degree-328 polynomial at ProveIt commit
`1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`. It retains the entire directly
indexed BFS943 coefficient tuple of that polynomial. It is a small new
operation/degree tradeoff, not a variable-count record or a global minimum.

Section 7 gives a sharp-center sibling with 88 operations and exact degree
318. Both literal polynomials and their four fixed coefficient payloads are
supplied and independently checked.

The old polynomial and its new arithmetic proof are retained under
`upstream133/compact/`. The consistency interpretation still uses that
package's identified native/compiler/refutation calibration. No new formal
Lean/Rocq or encoded ZFC proof object is claimed. The change described here
is an ordinary proof formalizable in ZFC, and does not assert Con(ZFC).

## 1. Literal definition

Use every formula and all ten positive inputs of the retained
`upstream133/compact/PROOF.md`, Section 1. In particular

    U=i c^2, E=1+V0(V0+1)k^2, a=Delta U^2 E,
    F0=1+a, G=E F0, Fsqr=1+4aF0,
    Q=Delta(Fsqr-1), b=c(T+alpha)-R, V=Fsqr*b-c,
    P=q^3(q-1), M=P mu^2 H,
    B=(K0+w)C-F, Kpos=X(3c-2X)+2.

Define the new lower center

    d=(A-1) U E.

Replace only the carrier by

    Z=P mu^2 [H(n+V(d-bB))+Kpos]
       +H[mu^2((q-1)Y-q^3 B)-P e].

The single polynomial equation is

    Q[Z^2-M^2 G V^2]+[M^2 G-Z^2]=0.

All names other than the ten listed inputs are integer-polynomial
abbreviations. `equation_87_degree323.json` is the full literal arithmetic
circuit. `construct_coefficients.py` reconstructs the complete four fixed
integers from the parent's finite printed recipe and checks every raw hash
and bit length against the retained literal parent circuit.

## 2. Exact shear and soundness

Let N85 be the retained polynomial with carrier center n-bVB and N87 the new
one. The identity

    n+V(d-bB)=(n+dV)-bVB

proves, over the free integer polynomial ring,

    N87(other inputs,n)=N85(other inputs,n+dV).

The substitution is not positive on all arbitrary positive inputs, because
V has not yet been oriented. To avoid a circular use of the old theorem,
first apply precisely the pretransport arguments in package 133, Sections
2--4, to a positive zero of N87. Those arguments allow any rational carrier:
they use only the unchanged Q,G,V,M and the product-square equation. They
recover positive integers g,y with G=g^2 and

    QV^2-(Q-1)y^2=1,

the doubled strong Pell pair, and the odd main Pell index. Before assuming
any transport sign they prove b>c and V>0. They do not depend on the literal
carrier center n-bVB. Since d>0, the integer n+dV is now strictly positive.
All other old inputs are unchanged. The exact polynomial shear therefore
maps this zero to a positive zero of N85. Its retained soundness theorem
gives the finite syntactic refutation. No positivity of B or C was used to
justify the shear.

## 3. Constructive positive completeness

A refutation provides the canonical witnesses of package 133, Section 8.
In its notation s=Y/q^3, kappa=Kpos/H, rho=e/mu^2 and t=B/(q-1) are integers,
with s,kappa>0, rho,t>=0. Put W=1+(q-1)bV. The canonical root sign is positive,
and the old carrier variable is

    n85=g y+W t+rho-kappa-s.

The new value n=n85-dV is integral. The exact identity

    G-d^2=E+2(A-1)U^2 E^2>0

gives g>d. Both are integers, so g-d>=1. Moreover b>c and Fsqr>3 give V>2c,
whereas H>3X and X>1 give

    0<kappa=[X(3c-2X)+2]/H<c,
    0<s=Y/q^3<Y<c.

The auxiliary Pell equation has y>V>0. Consequently

    n=(g-d)V+g(y-V)+W t+rho-kappa-s
      >V-kappa-s>0.

The exact shear maps this constructed tuple back to the canonical old zero,
so N87 vanishes. This proves both existential directions with ten strictly
positive inputs. Composition with the unchanged native/refutation calibration
gives in ZFC: absence of a positive zero of N87 iff Con(ZFC).

## 4. Arithmetic cost

In the 85-operation parent, three gates compute bV, bVB, n-bVB. Replace those
three by five gates:

    d=(A-1)*UE, bB=b*B, u=d-bB, v=V*u, center=n+v.

Both A-1 and UE=U*E already occur in the live parent prefix. Therefore exactly
two operations are added: 87 in all. Every binary sum, difference, product,
square and fixed scalar product counts. There are 52 multiplications,
20 additions and 15 subtractions; all ten inputs and all four fixed ports
remain live. Named intermediate polynomials add no unknowns.

## 5. Global exact degree and a nonzero leading coefficient

All unknowns have degree one; fixed coefficients have degree zero. Denote by
Z0 the old uncentered carrier numerator. Then Z=MdV+Z0. The global degree
bounds from the unchanged prefix are

    deg Q=86, deg M=13, deg G=56, deg V=80,
    deg d=28, deg Z0<=99.

The output polynomial is identically

    -M^2[Q(G-d^2)+d^2]V^2
    +2(Q-1)MdVZ0+(Q-1)Z0^2+M^2G.

Because G-d^2=E+2(A-1)U^2E^2 has exact degree 51, the first displayed term
has exact degree 26+86+51+160=323. The other three have respective degree
bounds 306,284,82. Thus no cancellation at degree 323 is possible.

Writing q0=beta*J and k0=eta+zeta, the entire highest homogeneous form is

    -2^11 q0^153 w^33 Y^77 i^14 k0^44 (q0-F)^2.

For example, the coefficient of J^153 w^33 Y^77 i^14 eta^44 F^2 is
`-2^11 beta^153`, nonzero for the actual beta. Its total degree is 323.
The checker supplements this symbolic derivation with independent finite-field
univariate coefficient propagation using the actual reconstructed fixed tuple.
That check is a lower-bound witness for the literal circuit; the displayed
identity proves the global upper bound.

## 6. Comparison

The latest relevant points are 84/436 and 85/328 in package 133, the new
87/323 and 88/318, and the retained 89/288. Here a pair denotes operations/degree and all
domains are ten strictly positive integer unknowns. The new point lowers
degree five at a cost of two operations against 85/328; it improves degree
113 at unchanged operations against package 131's 87/436. It does not dominate
85/328 or 89/288. The main research contribution of the overall task may lie
in other branches; this is an independently checkable small Pareto improvement.

## 7. A sharp-center sibling: 88 operations, degree 318

Set d=AUE instead, retaining exactly the same factored carrier and output.
The graph first computes d0=(A-1)UE and then d=d0+UE, adding one operation to
the lower-center circuit. This is 52 multiplications, 21 additions and
15 subtractions. The exact shear N88(n)=N85(n+dV) still applies. At a positive
zero, the same pretransport proof gives V>0 and d>0, so soundness is unchanged.

The earlier simple inverse-shear bound g>d is no longer true. The following
strict positivity in the canonical transport quotient supplies completeness
instead. The inherited source projection gives X=2^R, R>3q, w=X/q, C>=1 and
F<q. For q>=32, 2^(3q)>q^2 (indeed 2^q>q for every positive integer q), so
w>q>F. Consequently

    B=(K0+w)C-F>0, hence B>=1.

The inherited pretransport fifth-index bound is b>4g. Also d<2g, since

    4G-d^2=4E+(3A^2-4)U^2E^2>0.

All these statements concern the already calibrated canonical witnesses,
not arbitrary input values. Therefore bB-d>0. Using W=1+(q-1)bV and
(q-1)t=B, choose the integral new variable

    n=n85-dV=g y+t+rho-kappa-s+V(bB-d).

The positive integer bB-d is at least one. Since y,g>0 and t,rho>=0,

    n>V-kappa-s>0.

This proves positive completeness even for the upper center; it does not
assume a freely adjustable old carrier variable or assert t=0 is possible.

Now the exact defect is

    G-d^2=E-U^2E^2,

of degree 46. The same four-term global identity in Section 5 has degree
bounds 318,306,284,82. Its entire highest homogeneous form is

    +2^10 q0^150 w^32 Y^76 i^14 k0^44 (q0-F)^2.

For example the coefficient of J^150 w^32 Y^76 i^14 eta^44 F^2 is
2^10 beta^150, nonzero. The literal circuit is
`equation_88_degree318.json`. The independent checker proves both cut-register
identities exactly and verifies degree attainment for each actual fixed tuple
by coefficient propagation along its stated finite-field ray.

The strict canonical B>0 observation and this sibling were suggested and
independently reviewed by a separately tasked research agent in the same
AI-assisted workflow. No external human review is implied.

## 8. Stronger form: bijections of the positive zero sets

The existential completeness proofs above can be strengthened to an exact
correspondence for both centers. The global triangular polynomial shears

    n_old=n_new+dV,   n_new=n_old-dV

are inverse on integer tuples because d and V are independent of n. They
preserve the positive zero sets as well, though they need not preserve the
positive orthant at arbitrary nonzero points.

The new-to-old positivity was proved in Section 2: root recovery and
pretransport folding give V>0 before invoking the old soundness theorem.
For the old-to-new direction start with any positive zero of the old
85-operation polynomial, and use its complete ordered decoding. It gives
C>0, F<q, R>3q and X=2^R, hence B>=1 as in Section 7. It also gives
k=2*psi_{2V0+1}((R+1)/2)>=R+1, so rho=(k-R-1)/mu^2>=0, and integer
t=B/(q-1)>0. The earlier root and transport bounds give b>4g, y<3V/2,
V>2c and 0<kappa,s<c. The signed root equation has either epsilon=1 or -1.

For either center, 0<d<=AUE<2g, so bB-d>2g. Therefore

    n_old-dV=epsilon*g*y+V(bB-d)+t+rho-kappa-s
             >(g/2)*V-kappa-s
             >V-kappa-s>0,

because g>2. This covers both signed radical branches. Thus each displayed
shear is a bijection between the old positive zero set and the corresponding
new positive zero set. The statement is conditional on no consistency
assumption: it is an ordinary implication about arbitrary putative zeros.

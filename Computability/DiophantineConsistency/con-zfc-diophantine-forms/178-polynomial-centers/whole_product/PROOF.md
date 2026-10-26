# The whole-product center: unbounded proof

The complete self-contained statement, all ten-variable polynomial definitions,
the four fixed coefficient recipes, and the full argument are in
`../report/main.tex` (compiled as `../report/report.pdf`). This file records
the new proof in plain text, with the inherited interface identified explicitly.

## Definitions and inherited interface

Use the definitions in `../compact/PROOF.md`, Section 2, with the same actual
four-number tuple, unsquared trace f=1+2a, inverse Lucas correction, and
L=b^2. There are exactly ten independent strictly positive inputs. All
lettered registers are integer polynomials. The parent root and low-index
arguments in Sections 3-4, independently of the signs of B,C,R,b, give at a zero:

* G=g^2, E=tau^2, F0=f0^2, g=tau*f0>0;
* Q V^2-(Q-1)y^2=1 with an integer y>0;
* b is nonzero and has the sign of V;
* |b|>8f^3-1/2>7f^3, g<f/6, y<3|V|/2, |V|<3f|b|/2;
* C0=AUE<3g/2<f/4; f>2c>128 and A>16.

The new finalizer uses 16G instead of G. Valuation parity is unchanged,
because 16 is a square. Rational adjacent-Pell descent gives Z/M=epsilon*4*g*y,
where epsilon is +1 or -1. The integer polynomial shift in Z has no effect
on these root and index arguments.

## The exact ordinary polynomial

Set e2=(kY)^2, S=(kY)*(ell+k-(kY)*(Y+1)), theta=U^2*b,
Rc=theta*(3E+e2)-(b-c), and Sc=4E^2+3S^2+e2^2. Define

    Omega=U*(2*S*Rc+A*(4*E*V-theta*Sc)).
    Z0=h*D*(H*(n-b^2*B)+K)-H*(D*B+h*(e6-6*q^4*s)).
    Z=Z0-M*Omega.
    P=Q*(Z^2-16*M^2*G*V^2)+(16*M^2*G-Z^2).

The complete definitions of h,D,H,K and the remaining registers are given
in the article and common proof. The literal JSON contains only binary
addition, subtraction and multiplication, fixed integers, and the stated
ten positive variables. It has 116 live operations.

## Why the shift is small enough before B is known positive

Temporarily regard A as a formal indeterminate t. Put

    E(t)=e2*t^2+e1*t+e0,
    e1=k^2*Y*(1-2Y-2Y^2),
    e0=1+k^2*Y*(Y+1)*(Y*(Y+1)-1),
    V(t)=(1+2*(t^2-1)*U^2*E(t))*b-c,
    F(t)=E(t)*V(t).

At t=A these evaluate to E,V,EV. Let Qj be the value at A of the
polynomial quotient of F(t) by t^j. Q3 is coefficientwise even, because
the degree-at-most-two summand E(t)*(b-c) contributes nothing and the
remaining summand has factor 2U^2*b. An exact polynomial identity is

    Omega=U*(4*A*E*V-2*Q1-Q3/2).

The quotient notation is proof notation only. The division-free formula
above is the delivered equation. In particular, the proof does not replace
polynomial division by a numeric quotient or floor at some chosen input.

For a polynomial in t, denote its absolute-coefficient evaluation at A
by a superscript #. Since delta=(Y+1)/A<1/16, |e1|<2e2(Y+1), and
0<e0<=e2(Y+1)^2,

    E#(A)<=e2*(A+Y+1)^2, E>=e2*A^2*(1-2delta), E#(A)<2E.

The complete coefficient majorant of F obeys

    F#(A)<2E*(|b|+c)+8*(A^2+1)*U^2*E^2*|b|.

Use |b|>=1, c+1<2U^2E, and |V|>(f-c)|b|>Delta*U^2*E*|b|.
Then

    F#(A)/|EV| < 4/Delta+8*(A^2+1)/Delta
               =8+20/Delta<10.

Deletion of low coefficients gives |Qj|<=F#(A)/A^j. Therefore

    |Omega-4AUEV| <10U|EV|*(2/A+1/(2A^3)) < AU|EV|,

using A>=16. Thus Omega has the sign of V and

    3AUE|V|<|Omega|<5AUE|V|.

The scaled root and shift consume only a quarter of the square transport:

    4gy+|Omega| <6g|V|+5AUE|V|
                 <(9/4)f|V|<(27/8)f^2|b|<b^2/4,

because |b|>7f^3 and f>2. All these estimates hold before the sign of B
or R is recovered. The center is not assumed positive prematurely.

## Signed bootstrap and exact arithmetic handoff

For proof only put rho=(e6/6)/q^6, sigma=s/q^2, t0=B/h, kappa=K/H,
and W=1+h*b^2. The rational carrier identity is

    Z/M=n+kappa+sigma-W*t0-rho-Omega.

The inverse Lucas correction gives e6/6<=k-R-1<b for every integer R,
so rho<|b|/q^6<b^2/2. If B<=-1, then W*t0<-b^2 and kappa,sigma>0.
Consequently n< b^2/4-b^2+b^2/2<0, impossible. Thus B>=0, then C>0.

Only now apply the parent mask bound 3q<R<q^4, obtain b,V>0, and use
V=-c mod f and V=-R mod c to identify the main index with R. Since Omega
is an integer polynomial, Z0/M=epsilon*4gy+Omega is integral. Hence every
subsequent congruence in the inherited inverse-Lucas proof is unchanged:
recover the first index modulo q^4; obtain H|6hK; project to X=2^R;
deduce q is a power of two; only then cancel the factor 3 at the full
q^6 denominator. Recover q^2|s, q^3|Y, h|B and the native endpoint.

This proves soundness to a finite syntactic ZFC refutation using the
identified whole-tuple native/refutation calibration. It does not use an
arbitrary tuple merely satisfying the elementary numerical inequalities.

## Positive completeness

A finite syntactic refutation supplies the retained canonical outer data
and Pell witnesses. The trace-linear auxiliary coordinate has the positive
integral construction in source163. For these witnesses b,V>0, hence
Omega>0. Set

    n=4gy+Omega+(1+h*b^2)*t0+rho-kappa-sigma.

Every term is integral; the parent's explicit g>kappa+sigma+|rho| bound
makes n>0. The new carrier is 4gy and the polynomial vanishes. Thus both
directions hold internally in ZFC, and negation yields the required
unsolvability-equivalence with Con(ZFC).

## Exact degree and proof status

The separate algebra checker verifies all 84 center monomials, all 594
norm-defect monomials, the exact degree-106 defect, the actual 116-row DAG,
all fixed coefficient bytes and the exact degree-208 leading form. See
`ALGEBRA.md`, `CHECK.json` and `INDEPENDENT_REVIEW.json`.

Finite algebra checks do not prove the preceding unbounded estimates or
the inherited logical calibration. Those are ordinary mathematical proofs
formalizable in ZFC. No new compiled end-to-end Lean/Rocq proof, proof of
consistency, asserted zero, global minimum or worldwide priority is claimed.

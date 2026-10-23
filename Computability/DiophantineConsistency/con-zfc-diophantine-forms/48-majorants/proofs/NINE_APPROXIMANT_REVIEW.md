# Independent review of the polynomial square-root approximant

This addendum independently verifies the root's stronger majorant and its exact degree calculation. The definitions and positive domains are those in `NINE_WEIGHT_REVIEW.md`. In particular, all arguments hold before any square conditions or margin condition are assumed.

Put

    e=i*J*C,
    E=C*D*e,
    F=(D-1)*D^2*e^2+1,
    a1=D*F*I,
    S=e*(8*D^2-4*D-1),
    V8=S*G*H,
    a1new=64*a1.

These are polynomial definitions. `e` is supplied by the explicit product `iJC`, not a quotient of existing registers.

## 1. Exact identity

Direct expansion gives

    (8D^2-4D-1)^2 = 64D^4-64D^3+8D+1.

Consequently

    S^2-64DF = e^2(8D+1)-64D.

As `I=(G^2-1)H^2+1`, the full defect is exactly

    delta8=V8^2-64a1
          =[e^2(8D+1)-64D]*G^2*H^2
             +64DF*(H^2-1).

The actual positive domain gives `e>=7`, `D>=2`, and `H>=1`. In particular,

    e^2(8D+1)-64D > 4D*e^2 >0.

Thus `delta8>0` on every allowed assignment.

## 2. The stronger gap

Retain `Bstar=P(P+R)`. The previous review proves `D>2P`, `R<P`, and `G>F`. Therefore

    2*Bstar < 4P^2 < D^2.

Also `S<8D^2 e`, so

    delta8/V8 > e*G*H/(2D)
               > (D-1)*D*e^3/2
               > D^2
               > 2*Bstar.

The middle inequality uses `G>F=(D-1)D^2e^2+1` and `H>=1`. The next is equivalent to `(D-1)e^3>2D`, which holds already for D>=2 and e>=3.

Since `V8>Bstar`, the displayed defect bound implies

    (V8-Bstar)^2-64a1
       =delta8-2Bstar*V8+Bstar^2 >0.

Hence

    Bstar < sqrt(64a1) < V8-Bstar.

The lower bound follows from the stronger inherited `sqrt(a1)>Bstar`.

Together with `sqrt(a0)<h*Bstar`, this proves all separation and integer-centering bounds required by the h-weight finalizer, now with `a1new` and `V8`.

## 3. Square predicates and the fixed margin

For any positive integer a1, `64*a1` is an integer square if and only if a1 is an integer square. One direction is immediate. In the other, an integer root divided by 8 is a rational square root of an integer, and hence is itself an integer. No extra variable or divisibility condition is needed.

The finalizer is

    Omega=u*m,
    Theta=u*(n+Mdiv)+v-Omega*(2*Mdiv+h*V8),
    Q9=(Theta^2-Omega^2*(a0+64*h^2*a1))^2
        -256*Omega^4*h^2*a0*a1.

Here `m=K^2*Gcap-4*(C-KY)^2*Gcap-8*g*K^2` remains the computed margin. It is not a new/free witness. The only new finalizer witness is the already counted n. The argument in `NINE_WEIGHT_REVIEW.md` establishes the same existential conditions: a0 and a1 squares, u dividing v, and m positive. Completeness uses the actual positive value of m and takes `n=mZ-Mdiv-v/u`.

## 4. Exact total degree and diagonal leader

Let `t=deg(N)` and W be the source packing width. The source construction has leading coefficients `N:2^2`, `R:2^4`, while the retained tail gives

    deg(D)=20t+4,    lc(D)=2^34;
    deg(e)=10t+3,    lc(e)=2^19;
    deg(G)=103t+22,  lc(G)=2^179;
    deg(H)=3t+1,     lc(H)=2^5;
    deg(F)=80t+18,   lc(F)=2^140;
    deg(a0)=48t+14,  lc(a0)=2^84;
    deg(a1)=312t+68, lc(a1)=2^542;
    deg(Omega)=115t+3W+31, lc(Omega)=-2^211.

In the cancellation-resolved defect, the unique largest term is `8D e^2 G^2 H^2`. Thus

    deg(delta8)=252t+56,
    lc(delta8)=2^(3+34+2*19+2*179+2*5)=2^443.

Write `E0=u(n+Mdiv)+v-2Omega*Mdiv`. Then exactly

    Theta^2-Omega^2*(a0+64h^2a1)
      =E0^2-2E0*Omega*h*V8+Omega^2*h^2*delta8-Omega^2*a0.

The degrees of those four terms are respectively

    236t+6W+66,
    389t+6W+99,
    482t+6W+120,
    278t+6W+76.

The third uniquely dominates. Its leading coefficient is `2^(422+443)=2^865`. Squaring gives degree `964t+12W+240` and leading coefficient `2^1730`. The subtracted `256Omega^4h^2a0a1` has degree only `820t+12W+208`, so it cannot cancel that leader.

These bounds are valid for multivariate total degree. Specializing every witness to one indeterminate gives the stated nonzero diagonal leading coefficient, so the upper bound is attained. The literal emitted circuit should still be independently checked for exact correspondence with the formula and its resolved certificate.

## Review conclusion

The stronger approximant preserves the finalizer's full existential meaning and yields the claimed degree formula. I found no algebraic, sign, or square-class gap in this construction. As throughout, this is an ordinary mathematical proof of the new local adapter, with the existing source/ratio/foundational theorem dependencies retained explicitly.

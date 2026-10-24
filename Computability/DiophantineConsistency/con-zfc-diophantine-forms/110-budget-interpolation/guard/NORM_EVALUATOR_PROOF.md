# An 83-operation cleared five-root norm

All quantities in this note are indeterminates over the integers. This is an arithmetic-circuit identity, valid without sign, nonzero, or squareclass hypotheses. The function `cleared_norm5_compact2` evaluates

    delta^16 product over eps in {−1,1}^5 of
    [x − eps1 sqrt(a) − eps2 sqrt(b) − eps3 sqrt(c)
       − eps4 sqrt(d) − eps5 sqrt(cn/delta)].

The displayed denominator is cleared symbolically. The actual circuit has only binary addition, subtraction, and multiplication, including multiplication by each small constant. It has 83 live gates, improving the inspected 93-gate cleared evaluator. No arithmetic-circuit optimality claim is made.

## Complete evaluator

Use the following polynomial registers (each fixed power is evaluated by ordinary multiplication):

    x2=x*x; s=c+d; t=a+b; ab=a*b; D2=delta*delta;
    J=delta*(x2+s-t)-cn;
    K0=J*J+4*delta*(delta*(s*x2+c*d-ab)-cn*t);
    K1=4*delta*x*(J+2*delta*d);
    K2=4*delta*x*(J+2*delta*c);
    K3=4*delta*(J+2*delta*x2);
    Z=64*delta^3*ab*cn;
    f0=K0*K0+c*K1*K1+d*K2*K2+c*d*K3*K3-Z*(x2+s);
    f1=K0*K1+d*K2*K3-Z*x;
    f2=K0*K2+c*K1*K3-Z*x;
    f3=K0*K3+K1*K2-Z;
    g0=f0*f0+4*(d*f2*f2-c*(f1*f1+d*f3*f3));
    g1=f0*f2-2*c*f1*f3;
    N=g0*g0-16*d*g1*g1.

The literal implementation shares 4*delta, 2*delta, their common products, and Z*x. The gate count refers to its interned binary DAG, not to a naïve textual expansion of this display.

## Exact identity proof

Work in the free rank-four algebra with basis 1,u,v,uv and relations u^2=c, v^2=d. Put y=x+u+v. This plus-sign convention merely permutes the eventual conjugate factors. The cleared three-root norm is

    N3(y)=K(y)^2−64*delta^3*a*b*cn*y^2,
    K(y)=[delta*(y^2−a−b)−cn]^2
         −4[delta^2*a*b+delta*cn*(a+b)].

The four coefficients of K(y) are exactly K0,K1,K2,K3 above. This follows from y^2=(x^2+c+d)+2xu+2xv+2uv and ordinary multiplication. The scalar coefficient simplifies to the factored K0 display.

The four coefficients of N3(y) are f0,2f1,2f2,2f3. Taking the norm first under u→−u gives scalar coefficient

    f0^2+4d f2^2−c(4f1^2+4d f3^2)=g0

and v coefficient

    4(f0 f2−2c f1 f3)=4g1.

Taking the remaining quadratic norm gives g0^2−16d g1^2. Thus N is exactly the 32-factor product after multiplying by delta^16. This argument occurs in a free algebra, so it remains valid for dependent, negative, and zero radicands; no field-degree assumption is used.

`check.py` independently forms the defining conjugate product in a formal radical ring, in reverse elimination order, clears its denominator monomial by monomial, and compares all 20,349 coefficients. It also rejects a deliberately corrupted coefficient. These exact finite identities supplement the proof above.

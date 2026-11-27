# Reuse V as the transport weight

Reusing the existing V register removes the multiplication kI and the addition that formed L. The zero-offset circuit has 96 live operations and exact degree 432. The direct circuit has 101 live operations and exact degree 400. Both counts and degrees hold for the original and BFS-renamed compact44 coefficient tuples. [Circuit verifier](check.py)

The accepted index-weight kernels use L=kI+b, with

    k=eta+zeta, I=i*c², Delta=A²-1,
    b=c(T+alpha)-R, Df=1+Delta*I², V=Df*b-c.

The existing pretransport argument gives b>=1,c<=I,c>k and I>k before
any sign or divisibility premise for the transport carrier B. Since
Delta>=3,

    V-(kI+b)=Delta*I²*b-c-kI
             >=I*(Delta*I-k-1)>0.

Thus choosing Lnew=V makes the complete negative-B transport majorant
strictly stronger. The later W=1+gL congruences are unchanged. From any
old positive zero, all kernels and B remain fixed, old soundness gives
B>=0, and the polynomial shear

    nnew=nold+[V-(kI+b)]*B

is positive. Its normalized center equals the old one exactly. An
inverse positive n-map at arbitrary new zeros is not asserted: new
soundness instead repeats the original transport contradiction first.

For the zero-offset circuit the degree bounds at Z, s and h are 39, 108 and 104. For the direct circuit they are 37, 100 and 96. In both cases only the fourth power of s reaches the maximum possible output degree.

For zero-offset q0=beta*J,X0=w*q0,k0=eta+zeta, the predicted full top is

    2^16 q0^168 X0^40 w^8 i^24 Y^88 k0^48
          *(q0-F)^8*(q0-F-alpha)^8.

After X0=w*q0, its J^224*w^48*i^24*Y^88*eta^48 coefficient is
2^16*beta^224>0. For direct X0=q0+x and

    B0=(q0*K0+X0)*(q0-F-alpha)-q0*F,

the expected full top is

    2^16 q0^176 X0^40 i^24 Y^88 k0^48*(q0-F)^8*B0^8.

The J^192*x^48*i^24*Y^88*eta^48 coefficient is2^16*beta^192>0,
independent of K0.

The verifier reconstructs both complete circuits from their pinned [parent programs](../ten-positive-index-weight/README.md), checks every row is live, and compares all 35 coefficients of the final norm polynomial at its four input registers. To certify the total degree, it propagates a global degree bound along every gate. It computes the coefficient at that bound modulo 65537 on the line J = i = Y = eta = w = t for the zero-offset circuit, with x replacing w for the direct circuit and all remaining witnesses zero. Evaluating on this line certifies a coefficient of the polynomial and carries no positivity assumption on test inputs. The top coefficients are 1020 for both zero-offset tuples and 16266 and 8415 for the two direct tuples. Each nonzero residue proves the corresponding degree bound is attained.

Run `python3 check.py` for the four degree certificates. Use `python3 check.py --source` to print every arithmetic row. The original and BFS-renamed coefficient files are authenticated as separate whole tuples. The later [saturated-Pell construction](../ten-positive-saturated-pell/README.md) achieves 92 operations at degree 283.

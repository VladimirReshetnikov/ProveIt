# Independent degree certificate for the centered 15-integer norm

This component certifies algebraic degree only. The semantic three-root parity
argument and the complete ordinary polynomial are supplied by the main
construction. `audit.py` uses Python's standard library and a verbatim copy
of the exact sparse-ring engine from ProveIt's joint22-centered checker
(`ring.py`). It does not import the new 15-variable builder.

Run `python3 audit.py`. It expands the entire centered inner norm on eight
independent atoms. It does not attempt to infer exact degree from circuit
syntax or random specialization.

Use atom weights

```
X:2, Y:4, R0:5, h:1, f:1, c:1, T:1, n0:1.
```

The authentic substitutions are

```
a=(X+1)Y, Delta=a^2+4a+3,
m=XY^2, k=R0+1+hXY,
V=cTf-R0 f^2-c, Q=Delta(f^2-1), d=c^4,
n=2n0+1-2hYR0, delta=Q-1, D=d delta,
B0=mk, S=k(2m+1), A0=1+m(m+1)k^2,
z=n+2B0+2SV,
Abar=4A0 D, Bbar=Q delta, Cbar=4S^2 d(QV^2-1),
Rnorm=D z^2-Abar-Bbar-Cbar,
Tnorm=Rnorm^2-4(Abar Bbar+Abar Cbar+Bbar Cbar),
N3=Tnorm^2-64 Abar Bbar Cbar D z^2.
```

The exact 61891-term polynomial Tnorm has weighted degree109 and complete
leading part

```
512 X^9 Y^13 R0^3 h^3 f^6 c^8
    [R0 f^2+hY(X-2f^2)].
```

The subtracted triple tail has weighted degree at most212. Therefore N3 has
weighted degree218 with leading part equal to the displayed square. The
ordinary sum of the two retained squared residuals has degree88, so the
positive-unit-product finalizer has degree306.

## Why the upper bound is attained after the actual substitution

Let the actual independent variables be those of the main 15-variable form,
including J3,w3,v_scale,C,z,f,h,c. The highest homogeneous components are

```
x=36 beta J3 w3,
y=54 beta^3 J3^3 v_scale,
r=-(3 beta J3)^3 (12 w3 C-3 beta J3 z).
```

They are the degree2,4,5 parts of X,Y,R0 respectively. The displayed
weighted leader of Tnorm specializes to

```
512 x^9 y^13 r^3 h^3 f^6 c^8 [r f^2+hy(x-2f^2)].
```

This is a nonzero polynomial. In particular r is independent of h, so the
h-free term r f^2 in the bracket cannot cancel with the other two terms.
The true leading part of the squared retained guard is h^8 x^8 y^16.
Thus the complete degree306 part of the final equation is

```
2^18 x^26 y^42 r^6 h^14 f^12 c^16
       [r f^2+hy(x-2f^2)]^2.
```

A simple actual-coefficient witness is

```
[J3^184 w3^26 v_scale^42 z^8 h^14 f^16 c^16] P15_centered
    = 2^112 3^210 beta^184 > 0.
```

The h^14 term selects the square (r f^2)^2 in the bracket. The z^8 term
then selects the z monomial in each of the eight r factors. No other
leading term has the required h exponent, so it cannot alter this
coefficient. This proves exact degree after the actual numeral beta is
substituted, independent of the remaining ports.

The center is an integral coordinate shear preserving oddness. Evaluating
`n=2*(n0-h*Y*R0)+1` uses only three additional binary gates compared with
`n=2*n0+1`. Since n0 ranges over unrestricted integers, the coordinate
change has the integral inverse n0_old=n0_new-hYR0 (with the sign adjusted
to the direction of the map); no positivity witness is required.

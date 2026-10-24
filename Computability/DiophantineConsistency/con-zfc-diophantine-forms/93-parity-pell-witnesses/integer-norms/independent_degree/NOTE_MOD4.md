# Modulus-four centered variant: independent degree and parity audit

This is the final modulus-four refinement, kept separate from the earlier
odd-root variant in audit.py and NOTE.md. Run `python3 audit_mod4.py`.
The shared sparse-ring engine has the same explicitly inherited provenance.

Use the same atoms, weights, authentic V=cTf-Rf^2-c, and definitions of
m,k,Q,d,delta,D,B0,S,Afirst as in NOTE.md, except change the root expression
and cleared radicands to

```
n=4(n0-hYR)+2,
L=n+B0+4SV,
Abar=Afirst D,
Bbar=Q delta,
Cbar=16S^2 d(QV^2-1).
```

The octic norm formula itself is unchanged. It now represents radicands
Afirst, Q/d, and 16S^2(QV^2-1)/(Q-1).

## Exact degree

The fully expanded inner polynomial has 61557 terms, weighted degree109,
and complete leading part

```
2048 X^9 Y^13 R^3 h^3 f^6 c^8
      [R f^2+hY(X-2f^2)].
```

The triple tail remains bounded by degree212. Hence the norm degree is
218 and the unit-product degree is306.

With x,y,r the genuine leading forms of X,Y,R specified in NOTE.md, the
full degree306 homogeneous component is

```
2^22 x^26 y^42 r^6 h^14 f^12 c^16
       [r f^2+hy(x-2f^2)]^2.
```

Thus the exact actual-numeral coefficient witness is

```
[J3^184 w3^26 v_scale^42 z^8 h^14 f^16 c^16] P_mod4_centered
    = 2^116 3^210 beta^184 > 0.
```

The proof that no cancellation can alter this coefficient is precisely the
h-exponent and z-exponent argument in NOTE.md, with the factor16 increase
in the square of the inner leading polynomial.

The uncentered modulus-four norm, with n=4n0+2, has weighted degree222,
leader 2^22 m^8 k^8 V^6 Q^2 d^4, and unit-product degree310. The corresponding
simple actual coefficient is

```
[J3^184 w3^28 v_scale^44 z^6 h^16 f^16 c^16] P_mod4_uncentered
    = 2^122 3^212 beta^184 > 0.
```

## Change to the parity extraction proof

All sign, nonzero, negative-Q, and V=0 arguments in PARITY_AUDIT.md remain
valid. Since W is divisible by4, X and m=XY^2 are divisible by4. Therefore
B0=mk is divisible by4 and Afirst=1+m(m+1)k^2 is1 modulo4. The root sum
L=n+B0+4SV is2 modulo4.

For Q>1 and |V|>=1, the three positive radicands are Afirst, Q/d,
and 16S^2 Dy. Cancellation between the first and third is impossible
because S^2>Afirst and Dy>=1. Cancellation between the first and second
would leave L=+/-4S sqrt(Dy). Rational adjacent-Pell descent makes the
square root an integer, giving L=0 modulo4, a contradiction. Cancellation
between the second and third would leave L=+/-sqrt(Afirst); rational square
root integrality makes this an odd integer, contradicting L=2 modulo4.

The f=+/-1 exception similarly has Q=0 and root sum
L=+/-sqrt(Afirst)+/-4S. Its rational first root is integral and odd,
again impossible. Thus all roots in the remaining branch are rational.
The first and third roots are respectively an odd integer tau and
4S times an integer nu. Their signed-sum identity forces the middle root
i to be an odd integer. Restore r=(i-1)/2 as before.

For completeness, the old tau and i are both odd. Either tau+i or tau-i
is2 modulo4; choose the sign of i accordingly. Changing i to -i preserves
its source strong-norm equation and is allowed because r is unrestricted.
Then L=tau+i+4Snu is2 modulo4, and

```
n0=(L-B0-4SV-2)/4+hYR
```

is an integer. No positivity constraint is imposed on n0.

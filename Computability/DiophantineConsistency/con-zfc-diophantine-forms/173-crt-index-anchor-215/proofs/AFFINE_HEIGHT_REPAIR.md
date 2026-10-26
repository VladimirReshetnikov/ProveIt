# Recovering small coefficients after the 215-coordinate projection

This is an exact polynomial-coordinate result, independent of any Pell,
CRT, or consistency assumption. Every operation has an integer inverse.
The ordered certificates and the independent forward/inverse replay are
the authoritative specification; indices below belong to the indicated
intermediate chart, not to an unannounced semantic interpretation of the
final coordinates.

## Pell coordinates and the residual basis

For each principal pair keep the difference d=X-AY and ordinate Y, but
replace the third coordinate Z=AY by X=d+Z. The inverse is Z=X-d.
The multiplication and norm rows become

```
X-d-AY=0,       2dX-d^2+Y^2-1=0.
```

For a pooled request block the same two rows can now be written as

```
K-2 sum Y(m-X)-(2A-n)L=0,
sum ((m-d)^2-Y^2)-nK+L=0.
```

The pooled orientation row can be adjusted by adding retained norm rows
and the retained squared-index bound. These elementary row operations
preserve its simultaneous zero set with all other rows. This chart makes
the output-error bilinear expression substantially less dense. It is not
a new unbounded Pell theorem; it is an exact coordinate and residual-basis
change implementing the existing theorem.

## A local source of the projected large coefficients

After the recorded first residual-basis pass on the 215-coordinate source,
write a=x8, b=x9, c=x19, z=x20, u=x21 and v=x33. Two defining rows contain

```
u-(a+2z-1)^2-1,
v-(23a+32b+8c-2z+9)^2-1.
```

A downstream row contains `w+1-L^2-L`, where

```
L=186a+256b+64c-16z-2v+64.
```

Squaring this residual is responsible for coefficients on the order of
10^10 in the collected quartic. Those coefficients are not intrinsic to
the existential relation.

First add twice row5 to row6, reversing an earlier support-oriented row
operation. Then apply the following four coordinate substitutions IN ORDER,
leaving all unmentioned coordinates fixed:

```
old x19 = new x19 -3x8 -4x9 -1,
old x33 = new x33 -3x8 +32x19 -8x20,
old x21 = new x21 -3x8 -8x20,
old x20 = new x20 +2x19.
```

Each displayed right side uses the coordinates current at that stage.
Every target has coefficient one and is absent from its own added affine
part, so each inverse merely negates that added part; inverse operations
are applied in reverse order.

Afterward the two large square arguments become

```
4c+s,       4c-s,       s=a+2z-1,
```

and L becomes `-2v`. This symmetric coordinate choice keeps both branches
small. Centering one branch alone merely transfers a large square to the
other branch, which is why the two branches must be treated together.
The literal collected height falls from13,607,063,249 to333,108. Six
additional residual-basis operations lower it to324,724.

## Centering a second pair of quadratic forms

In that next chart put `L0=2x8+4x9-x19`. The quadratic part of row45 is
exactly

```
-4(x58-2L0)^2-8(x59-L0)^2.
```

The two further substitutions

```
old x58 = new x58 +4x8 +8x9 -2x19,
old x59 = new x59 +2x8 +4x9 -x19
```

remove that repeated linear form. They lower the largest residual
coefficient to192 and the collected polynomial height to91,679.
Eleven final integer translations reduce the collected support without
increasing either height.

## Final exact result

The resulting single sum-of-squares polynomial has

```
215 unrestricted integer coordinates;
154 quadratic residuals;
exact total degree4;
5660 collected nonzero monomials;
maximum absolute collected coefficient91679;
maximum absolute residual coefficient192.
```

The optimization chain contains75 elementary operations:14 principal-Pell
coordinate shears,37 first basis operations,5 mixed local operations,
6 further basis operations,2 final coordinate shears, and11 translations.
The independent checker imports no producer or optimizer. It compares
all coefficients at every forward boundary, checks each inverse, checks
the composed inverse, verifies every supplied quartic expansion, and
confirms that all215 coordinates occur.

This gives a bijection between the integer zero sets before and after
coordinate changes. Residual-basis changes preserve the zero set pointwise.
It does not claim equality of the two polynomial functions on arbitrary
nonzero residual tuples.

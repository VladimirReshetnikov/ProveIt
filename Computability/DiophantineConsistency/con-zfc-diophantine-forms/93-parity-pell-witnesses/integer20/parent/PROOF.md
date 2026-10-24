# Complete centering and degree certificate

All quantified coordinates in this note range over **Z**. Fixed coefficients
are those in `coefficients/BINDING.json`. No sign or nonzero condition on a
witness is used in the new reduction.

The parent is `joint/joint22_degree16.json` in the authenticated
`ZFC_Diophantine_Joint_Guards_2026-10-24.zip` arrival. Its exact polynomial,
literal circuit and ordinary proofs are copied under `provenance/`; their
hashes and the arrival archive hash are pinned in `provenance/PINS.json`.
In particular, the parent has already performed its strong-norm row
operation and monic eliminations of V and I. Those inherited transformations
are separate from the free polynomial identity proved here.

Use the ordered 22 coordinates

```
J3,F,alpha,z,f,h,r,v_scale,w3,tau,eta,y,gamma,o,j,E,c,a,
pair_root,pair_pos1,pair_pos2,pair_pos3.
```

The following are polynomial abbreviations, not additional unknowns:

```
J = 3*J3+1;                q = beta*J+1;
W = 4*(3*w3+1);            X = q*W;
Y = (2*v_scale+1)*q^3;     C = q-F-alpha;
V = f*o-c;                k = 1-V+j*c+h*E;
H = 4*a+3;                Delta = a^2+H;
I = (2*r+1)*c^2;
R = ((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J;
d = (cone_A*F)*(cone_B*C)-(q-cone_A*F-cone_B*C)^2;
t = eta*(k-eta);
Pos = 1+pair_pos1^2+pair_pos2^2+pair_pos3*(pair_pos3+1).
```

The new equation is the sum of the squares of these ten residuals:

```
a-E-Y,
E-X*(a-E),
c-eta-k*(a-E),
tau^2-E*(c-eta)*(k+E*(c-eta))-1,
(X+a*c+gamma*H)^2-Delta*c^2-1,
c*j-V-R,
(K0+W)*C-F-z*(q-1),
I^2-Delta*(f^2-1),
(f*o+y)^2-Delta*(f^2-1)*(c+y)*(2*f*o+y-c)-1,
d*t-(pair_root^2-d-t+1)^2-Pos.
```

The abbreviated rows above are explanatory. The artifact `equation.json`
has only the declared coordinate and fixed-leaf names in its residuals;
`build.py` checks their complete equality to the literal circuit.

## Polynomial witness maps in both directions

Write p=f*o and Q=Delta*(f^2-1). The parent's ninth residual is

```
A_old = Q*((p-c)^2-y_old^2)+y_old^2-1.
```

The universal ring identity

```
(p-c)^2-(p+y)^2 = -(c+y)*(2*p+y-c)
```

gives the new ninth residual exactly when y_old=p+y. Define T on Z^22 by
fixing every coordinate except y and setting its old value to y+f*o.
Define U by fixing every coordinate except y and setting its new value to
y_old-f*o. Since neither f nor o changes, U(T(x))=x and T(U(x))=x for every
integer tuple. No division, positivity or polynomial-zero premise is needed.

The parent's other nine residuals do not contain y. Consequently, for every
row index i and every tuple x,

```
A_new_i(x) = A_parent_i(T(x)),
A_parent_i(x) = A_new_i(U(x)).
```

Squaring and summing gives the same identities for the full polynomials.
Thus T and U give inverse bijections of their complete integer zero sets.
This conclusion would not follow for a positive-only domain; the result here
uses unrestricted integer coordinates throughout.

The checker expands both identities for **each of all ten rows**, over all
22 coordinate symbols and all six coefficient symbols. It also expands the
two compositions on y. There is no reliance on only checking the auxiliary
row or on a particular compiler-selected witness.

## Exact degree after fixing the coefficients

The ten residual degrees in the 22 witness coordinates are respectively

```
4, 3, 3, 4, 4, 4, 2, 6, 7, 6.
```

The ninth row is the only row of degree seven. Its complete degree-seven
homogeneous component is

```
-2*a^2*f^3*o*(c+y).
```

Its square is therefore the entire degree-fourteen component of the sum of
squares:

```
4*a^4*f^6*o^2*(c+y)^2.
```

In particular, the coefficient of a^4*f^6*o^2*y^2 is the integer 4,
independent of every coefficient port. The degree remains exactly fourteen
on the specified fixed tuple. The checker verifies the entire homogeneous
component, as well as this selected nonzero coefficient. A naive degree
propagation through the reused parent DAG still returns sixteen; its
cancellation is the reason that estimate is not used as an exact certificate.

## Literal evaluator and inherited coefficient interface

The parent's 118-gate circuit already computes fo=f*o, and its only direct
use of y is the gate y2=y*y. Insert centered_y=fo+y immediately before that
gate and replace its two operands by centered_y. Every other gate, every
residual output and the SOS finalizer are unchanged. The resulting acyclic
list has exactly 119 live binary gates: 58 multiplications, 32 additions and
29 subtractions. This includes all scalar products and squares. It uses 100
gates for the ten residuals and 19 for their ten squares and nine additions.
Shared named values and fixed numeral leaves are free under this declared
arithmetic-circuit convention.

The six coefficient payloads are copied intact from the parent's source34
tuple, including beta=2^1064921-1, cone_A=2^1113, cone_B=2^666104 and the
already shifted MF. All compressed and uncompressed hashes, bit lengths and
minimal little-endian encodings are checked. The reduction changes no native
stencil, determinant scale, guard proof, machine seed or calibration premise.

The new unconditional theorem is the polynomial zero-set bijection above.
Interpreting absence of zeros as Con(ZFC) still uses the parent's ordinary
unbounded native/Pell/refutation interface. No end-to-end Lean calibration or
encoded object-ZFC derivation is supplied by this Python certificate.

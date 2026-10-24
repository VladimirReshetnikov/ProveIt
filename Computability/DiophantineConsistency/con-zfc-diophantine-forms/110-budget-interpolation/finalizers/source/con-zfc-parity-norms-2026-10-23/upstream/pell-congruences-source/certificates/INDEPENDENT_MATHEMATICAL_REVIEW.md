# Independent mathematical audit: determinant, residue orientation and CRT

This audit was written independently of the polynomial builder. It is an
internal mathematical review, not external peer review or a proof-assistant
certificate. All claims below are conditional only on the explicitly
inherited source-34/source-64 native and Pell theorems, as are packages 70
and 71. The new algebraic compatibility and CRT arguments are proved here.

## 1. Common source and simultaneous completeness

Both constructions use the complete source-34
`mixed-parity-unrounded-1064921` tuple. Write

```
d = 1064921, B = 2^d, beta = B-1,
A_F = 2^1113, A_C = 2^666104,
q = beta J_old + 1, C = q-F-alpha,
U = A_F F, W = A_C C,
G = UW-(q-U-W)^2.
```

The determinant guard is `G = 1+x^2+y^2+z(z+1)`. Its right side is
strictly positive. Therefore `UW > (q-U-W)^2`, so U and W have the same
nonzero sign and

```
|q-U-W| < sqrt(UW) <= (|U|+|W|)/2.
```

Consequently q has their sign and
`|q| > (|U|+|W|)/2 >= |F|+|C|`, because both fixed scales are at least two.
Thus F, C and alpha=q-F-C have the same nonzero sign. In particular the
two former guards `F alpha > 0`, `F C > 0` can be restored. This argument
includes negative q and uses no native completeness hypothesis.

This order matters: restore both former Pos rows first, obtaining a zero
of package 70's residue-oriented equation. Its signed power-recovery
theorem then applies with all hypotheses unchanged. It proves
`X = e 2^R`, `R` odd, and the imposed residue `X = 2 (mod 3)` forces e=1.
The deleted square coordinate is `u=2^((R-1)/2)`. There is no use of
positive X before this deduction.

Completeness must use one common witness family, not separately chosen
witnesses for the two reductions. The source-34 coefficient proof supplies
canonical witnesses after rank tuning with

```
q=2^t, t=dN odd, R=3 mod 4, R>t,
J_old=(2^t-1)/(2^d-1), w_old=2^(R-t-2).
```

The rank controller changes only the permitted lower dummy at native
exponent 1063. The determinant proof's top C digit is at 3296, with all
other C support at most 2195; the F leading digit remains at 8791.
Package 71 explicitly bounds the lower convolution digits after every
permitted dummy change. Therefore its estimates

```
q/2 <= A_F F < 4q/5,
q/2 <= A_C C < 3q/5
```

hold on this very same tuned family. They imply G>0.

Since d and t are odd, beta=1 mod 3 and J_old=1 mod 3. Since R-t is a
positive even integer, R-t-2 is nonnegative even and w_old=1 mod 3.
Thus `J_old=3J3+1`, `w_old=3w3+1` admit integer inverse coordinates
on these witnesses. The determinant and residue requirements are
simultaneously satisfiable; no new tuning condition is needed.

For the direct quartic variant, simply set `X_old=3X3-1`. Its canonical
inverse is `X3=(2^R+1)/3`. No separate congruence condition on J or w is
needed. This variant is unsuitable for monic elimination of X without
further work because its X3 equation has leading coefficient three.

Replacing two guards and six private variables by one guard and three
variables gives 37 variables / 24 quadratic rows from package 70's
40 variables / 25 rows. Its six and eleven already-verified monic
eliminations give 31 variables / 18 cubic rows and 26 variables / 13
quartic rows. The determinant uses only J, F and alpha, none of the
eliminated coordinates, so these maps do not alter it. The exact degree
certificates `tau^4:1`, `r^2 c^4:4`, `a^4 f^4:1` survive.

## 2. A rank-adapted CRT lemma

Let c and f be nonzero integers and suppose

```
f^2 = 1 (mod c).
```

Then gcd(f,c)=1. For every integer R, the simultaneous congruences

```
V = -c (mod f), V = -R (mod c)
```

are equivalent to the existence of an integer T with

```
V = f(cT-fR)-c.                         (CRT)
```

Forward proof: write V=fo-c. Since c divides V+R, the integer
`f(o+fR) = V+c+f^2 R` is divisible by c. Coprimality implies
c divides o+fR. Put T=(o+fR)/c to obtain (CRT).

Reverse proof: put o=cT-fR. Then V=fo-c, and

```
V+R = fcT-c-(f^2-1)R
```

is divisible by c. Thus j=(V+R)/c is an integer and the original two
equations V=fo-c and V=jc-R hold. These maps are inverse, including all
signs. The proof does not assume f is congruent to +1 or -1 modulo c;
the weaker square congruence is exactly enough.

### Why the hypothesis holds before auxiliary rank recovery

The preliminary signed Pell argument uses the first norm, the main norm,
the index relation `k=R+1+hE`, the common-sign guards and the ordinary
strong equation. It yields integers p,m with

```
|c|=psi_b(p), |f|=chi_b(m), p divides m.
```

This is package 70, Section 4.2, before Section 4.3 identifies p=R.
The elementary divisibility sequence identity
`psi_b(p) | psi_b(m)` for p|m gives

```
f^2-1 = (b^2-1) psi_b(m)^2 = 0 (mod c^2).
```

Therefore the CRT hypothesis holds without the auxiliary index equation
which it is used to restore. This avoids circular reasoning. The nonzero
conditions are also already known: c is a positive absolute Pell
ordinate and the ordinary strong equation forces f^2>1.

The full modulus f^2 is unnecessary. The sometimes suggested expression
`f^2(cT-R)-c` gives only a subprogression and would require a stronger
completeness choice. Formula (CRT) parametrizes the entire old congruence
class and gives a direct bijection after the preliminary Pell facts.

## 3. Degree accounting for the smaller companions

Use the literal native rank polynomial

```
R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J_old,
q=beta(3J3+1)+1, J_old=3J3+1,
k=R+1+hE.
```

R has degree four in the unknowns and k also has degree four. Start from
the 37-variable affine-J,w quartic and make the eleven standard lift
eliminations, but restore `zeta=k-eta` using the packing-index row, rather
than using the auxiliary-index row. Make the invertible shifts

```
tau_old=tau_tail+E(c-eta), y_old=V+y_gap.
```

Replace o and j by T using (CRT), retaining V as a coordinate and
retaining the single new degree-six residual

```
V - f c T + f^2 R + c.
```

Finally eliminate I by `I=(2r+1)c^2`. The result has 24 variables and
11 residuals. The critical residual degrees are:

| Residual | Degree at most |
|---|---:|
| CRT definition | 6 |
| Ordinary strong equation | 6 |
| Main c relation `c-eta-k(a-E)` | 5 |
| Shifted first norm `tau_tail^2+(2tau_tail-k)E(c-eta)-1` | 6 |
| Eta/zeta guard `eta(k-eta)-Pos` | 5 |
| Centered auxiliary norm below | 8 |

The auxiliary row is exactly

```
V^2 + (1-(2r+1)^2 c^4) y_gap (2V+y_gap) - 1.
```

Its square contributes `16 r^4 c^8 y_gap^4`; no other residual uses
y_gap. Hence the sum-of-squares equation has exact degree 16, provided
the literal artifact agrees with these specified rows. Treating V as a
free coordinate with a defining equation is essential for this degree.

Eliminating V as well using its monic CRT row gives 23 variables and
10 residuals. Now V has degree six, so the auxiliary row has degree
13 and the SOS degree is at most 26. Its pure-J3 leading term is

```
648 beta^4 r^2 c^4 y_gap f^2 J3^4.
```

Therefore the coefficient of
`r^4 c^8 y_gap^2 f^4 J3^8` in the full SOS is
`419904 beta^8`, strictly positive for the actual beta. The degree is
exactly 26. These are symbolic certificates for the specified formulas;
the emitted packets must still be independently checked against them.

## 4. Further monic eliminations and half-centering

Eliminate a from the 23-variable system by the retained monic equation
`a=E+(2v_scale+1)q^3`. This leaves 22 variables and degree 26: the
auxiliary row has not changed, and the main norm and strong row have
degree at most ten. Next eliminate E by

```
X=4q(3w3+1), Y=(2v_scale+1)q^3,
E=XY, a=(X+1)Y.
```

Here deg X=2, deg Y=4, deg E=deg a=6, and deg k=7. The result has
21 variables; the main norm, the strong row and the shifted first norm
have degree at most 14, and all others have no larger degree. Thus its
SOS degree is at most 28; a separate coefficient check should establish
the exact degree on the authentic fixed slice.

Finally eliminate eta by `eta=c-kY`. Now deg eta=deg zeta=11,
and the eta*zeta guard has degree 22. A naive retention of the former
tau shift gives a first-norm row of degree 24. The following exact lemma
reduces that row to degree 18.

### Half-centered integral-root lemma

For arbitrary integers P and k, the equation

```
tau_old^2-P^2+Pk-1=0
```

is equivalent, by a bijection of integer roots, to

```
Ttau^2+2Ttau(2P-k)+k^2-4=0,             (HC)
Ttau=2tau_old-2P+k.
```

The identity between the left sides is `HC=4*old`. Conversely (HC)
reduced modulo four says `(Ttau-k)^2=0 (mod 4)`, so Ttau-k is even.
Therefore `tau_old=(Ttau+2P-k)/2` is an integer. Substitution and division
by the nonzero integer four restore the old equation. This proof uses no
pre-existing parity promise for k and imposes no new congruence guard.

After the eta elimination, `P=k+E*kY` has degree 17 and k has degree
seven. Thus the half-centered row has degree at most 18, whereas the
eta*zeta row retains degree 22. The 20-variable SOS therefore has degree
at most 44. It is exactly 44: write v=v_scale and w=w3; the leading
monomials are

```
Y: 54 beta^3 J3^3 v,
E: 1944 beta^4 J3^4 w v,
kY: 104976 beta^7 J3^7 h w v^2.
```

The eta*zeta guard has leading part `-(kY)^2`; consequently its square
contributes

```
104976^4 beta^28 J3^28 h^4 w3^4 v_scale^8.
```

No other row has degree 22. The displayed positive coefficient certifies
exact total degree 44 for the actual beta.

## 5. General simultaneous-positivity compression

Package 68 proves, for all integers x,y,

```
x>0 and y>0  iff  exists s in Z:
xy-(s^2-x-y+1)^2 > 0.
```

Its proof is elementary: positivity of the right side forces xy>0;
the both-negative case is excluded by the large square. For x,y>0 choose
the square nearest the positive integer x+y-1. Its squared error is
strictly smaller than x+y-1, and x+y-1<=xy. This is the existing
nearest-square lemma, explicitly reused here rather than claimed anew.

Apply it to the remaining positive quantities G (the determinant) and
Z=eta*zeta. Replace their two separate Pos triples by one integer s and
one Pos triple. The single row is

```
G Z - (s^2-G-Z+1)^2 - Pos(p1,p2,p3).
```

This deletes six private variables and adds four, a net saving of two;
it replaces two rows by one. Both directions are immediate applications
of the lemma, so it is compatible with every preceding existence and
zero-set transformation. Its degree is at most max(deg G+deg Z,
2 max(2,deg G,deg Z)), and deg G remains two.

The following resulting bounds follow from the explicit degrees above.
For the first row, the non-CRT 25-variable equation means the ordinary
26-variable octic after eliminating V=fo-c and shifting y_old=V+y_gap.

| Parent | deg Z | Paired unknowns | Maximum new SOS degree |
|---|---:|---:|---:|
| 25 variables, degree 10, non-CRT | 3 | 23 | 12 |
| 24 variables, degree 16, CRT | 5 | 22 | 20 |
| 22 variables, degree 26, CRT | 5 | 20 | 26 |
| 21 variables, degree 28, CRT | 8 | 19 | 32 |
| 20 variables, degree 44, CRT | 22 | 18 | 88 |

The exact-degree certificates for the stated recipes can be chosen as
follows; all powers of beta are fixed coefficients, not variable degrees.

| Paired form | Monomial | Coefficient |
|---|---|---:|
| 23 / 12 | `eta^4 f^4 o^4` | 1 |
| 22 / 20 | `eta^4 J3^16` | `43046721 beta^16` |
| 20 / 26 | `r^4 c^8 y_gap^2 f^4 J3^8` | `419904 beta^8` |
| 19 / 32 | `eta^4 h^4 J3^16 w3^4 v_scale^4` | `1944^4 beta^16` |
| 18 / 88 | `J3^56 h^8 w3^8 v_scale^16` | `104976^8 beta^56` |

In the second, fourth and fifth rows, the new paired residual has leading
term `-Z^2` and its square has leading term `Z^4`. All other residuals
have lower degree. In the 20 / 26 form the existing auxiliary norm still
supplies the highest-degree certificate. These are derivations for the
specified formulas; an audit must verify the emitted artifacts against
them rather than copy these bounds as untested metadata.

## 6. Exposing the monic native transport coordinate

There is a further exact elimination, requiring no Pell or positivity
hypothesis. Initially C abbreviates q-F-alpha. Replace alpha by an
independent coordinate C, with inverse alpha=q-F-C. This is an integral
affine bijection in the two coordinates for every fixed q. The native
transport row is then visibly monic in F:

```
(K0+W)C-F-z(q-1)=0.
```

Eliminate F and its defining row by

```
F=(K0+W)C-z(q-1), alpha=q-F-C.
```

Every source occurrence must undergo the substitution, including both
the determinant and the packed rank. The rank simplifies exactly to

```
R=(q(q-F)-C)(q^2-1)+(MC+q MF)J_old.
```

Thus the new F has degree two and R has degree five. The determinant G
now has degree four. When E has already been eliminated, however, the
leading term hE of k still has degree seven, so the large-degree terms
of the eta*zeta guard are unchanged. This gives the following further
polynomials by a bijection of integer zero sets:

| Parent before transport elimination | New unknowns | Exact SOS degree |
|---|---:|---:|
| 25 / 10, non-CRT | 24 | 10 |
| 23 / 12, paired non-CRT | 22 | 16 |
| 20 / 26, paired CRT with E retained | 19 | 28 |
| 19 / 32, paired CRT with E eliminated | 18 | 32 |
| 18 / 88, paired CRT with eta eliminated | 17 | 88 |

In the 19 / 28 case the CRT expression for V now has degree seven and
the auxiliary row has degree fourteen. Its leading pure-J term gains
one factor of z, giving exact coefficient
`419904 beta^8` at `r^4 c^8 y_gap^2 f^4 J3^8 z^2`.

For 24 / 10 the packing-rank row has degree five and leading pure-J
term `81 beta^4 J3^4 z`, up to its row sign. Its squared coefficient at
`J3^8 z^2` is `6561 beta^8`; the auxiliary row also has degree five.

For 22 / 16 the paired row's degree-eight part is `-G_4^2`, where
`G_4=-cone_A^2 F_2^2` and `F_2=12w3*C-3beta*J3*z`. Its square has
coefficient `6561 cone_A^8 beta^8` at `J3^8 z^8`. The other residuals
have degree at most five. The two remaining degree certificates are
unchanged from 19 / 32 and 18 / 88 above, because their degree-leading
parts use hE and Y only, not the changed lower-degree R.

This is a coordinate choice followed by a monic equation elimination,
not an assertion that a quotient is automatically integral. It must be
implemented using a fresh C coordinate replacing alpha, rather than
substituting the old abbreviation back into the proposed definition of F.

## 7. Boundaries of this review

This is not an independent reproof of the native tile compiler, K215's
refutation calibration, or the inherited ordinary strong-rank theorem.
It checks that the new reductions invoke them with their existing
hypotheses, including signs and the order of the rank arguments. It
does not replace an object-language ZFC derivation or claim a worldwide
minimality result. The parent program must audit the actual residual
packets, coefficient binding, transformations, liveness and exact-degree
coefficients before release.

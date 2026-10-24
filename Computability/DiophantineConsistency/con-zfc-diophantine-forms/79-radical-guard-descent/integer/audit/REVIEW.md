# Independent review: determinant guard, signed bootstrap, and monic projection

Repository pin: `2605669a532342f153b13eb6b4a0af4b54f5fa37`.

## Verdict

The new **23 unrestricted integer variable / degree 12** candidate, the
**26 unrestricted integer variable / degree 8** candidate, the
**22 unrestricted integer variable / degree 14** companion, and the
**31 unrestricted integer variable / degree 6** companion are supported by
the ordinary mathematical arguments named below. Their composition introduces
no additional sign or canonical-witness gap that I can identify. The exact
algebra was independently reconstructed without importing the construction's
polynomial code. This is not a new proof-assistant kernel certificate and
does not reprove the entire native compiler or internal-ZFC transport.

The 23-variable polynomial is the sum of squares of 11 residuals of degrees
`4,4,3,4,6,4,4,3,4,6,6`. Its coefficient at `eta^4*f^4*o^4` is **exactly 1**,
independent of every fixed coefficient port, proving exact degree 12 on the
authentic coefficient slice. The 26-variable polynomial has 14 residuals of
degree at most four and coefficient **1** at `t^8`, proving exact degree 8.

The 22-variable polynomial has ten residuals of degree at most seven and
coefficient **4** at `a^4*f^6*o^2*y_tail^2`, proving exact degree14. The 31-variable
polynomial has18 residuals of degree at most three and coefficient **4** at
`r^2*c^4`, proving exact degree6. These claims were checked against the final
packets under `integer/forms`, not only against the exploratory files.

## 1. The guard is sound for all integer inputs

Set `q=beta*J+1`, `C=q-F-alpha`, `U=cone_A*F`, `W=cone_B*C`, and

```
G = U*W - (q-U-W)^2,
H = eta*zeta,
Pos(p1,p2,p3) = 1+p1^2+p2^2+p3*(p3+1).
```

The single new row is

```
G*H - (t^2-G-H+1)^2 = Pos(p1,p2,p3).
```

For arbitrary integers, `Pos` is positive. The row implies `G*H>0`, so
`G,H` have a common nonzero sign. If both were negative, write `G=-a,H=-b`
with `a,b>=1`; then the subtracted square would be at least `(a+b+1)^2>ab`.
This is impossible. Thus **G>0 and eta*zeta>0** with no prior assumptions
on `q,F,alpha,C,X,eta,zeta`.

For `cone_A,cone_B>=2`, `G>0` gives U and W the same sign and

```
abs(q-U-W) < sqrt(U*W) <= (abs(U)+abs(W))/2.
```

Consequently q shares their sign and
`abs(q)>(cone_A*abs(F)+cone_B*abs(C))/2>=abs(F)+abs(C)`.
Thus F, C, and alpha=q-F-C have the same nonzero sign. In particular the
old guards `F*alpha>0`, `F*C>0`, and `eta*zeta>0` follow before any use of
the signed-power bootstrap. There is no circular use of q>0.

Every positive integer admits the Pos representation (three squares for
4n-3). Therefore a new solution restores all three deleted old guard
triples. For the nonsigned form this already supplies a Q41 solution after
the monic restorations. For the signed form it supplies the precise
preconditions of the source-75 signed40 bootstrap.

Conversely, if G,H>0, put n=G+H-1. The integer square nearest n has squared
error less than n, while GH>=n. It supplies t making the left side positive,
and then a Pos triple exists. This direction uses neither a field-valued
root nor a noninteger witness.

## 2. The signed transformation has the required interface

The transformation removes `w_scale`, replaces `X=2*u_old^2` by
`X=4*q*u^2`, and replaces z by Z with the cleared transport

```
(K0*q+X)*C - q*F - Z*(q-1) = 0.
```

Source 75, `guards/PROOF.md`, proves the resulting signed40 source equivalent
to Q41 for the **whole source-34 mixed-parity-unrounded-1064921 tuple**. Its
argument recovers the ranks without assuming X positive, excludes X<0 by
the Mersenne congruence, then applies the positive-X/signed-Y argument to
recover X=2^R with R odd. Its separately documented review checked exactly
these signs and non-wrap conditions. Inspection of Q41's PROOF44 Sections
5-7 confirms that the inherited positive-X argument uses the old twice-square
row only for X>0; once X>0 is recovered, its later quantitative hypotheses
are retained.

The new determinant guard can be fed into this theorem because it first
restores all old sign triples, as proved above. Its stronger restriction
does not alter any arithmetic row used by the signed40 argument.

There is a useful all-input identity:

```
new_transport(Z=q*z) - q*old_transport(w_scale=u^2)
    = (X-4*q*u^2)*C.
```

It was independently verified as a polynomial identity. In soundness,
`q|X` and the new transport imply `q|Z`, by reducing modulo q. The guard
has already forced q nonzero. Thus z=Z/q is an integer, division by q
restores the old row, and no unproved quotient-integrality assumption is
being made. The signed40 theorem's remaining recovered values restore
`u_old=2^((R-1)/2)` and `w_scale=u^2`.

## 3. Canonical completeness of the two improvements is compatible

This is the most important composition check. It would be insufficient to
know only that each improvement has some complete witness family.

Both source-71 determinant completeness and source-75 signed-power
completeness use the same source-34 canonical rank-tuned accepting words.
The source-34 coefficient proof gives

```
q=2^t, t odd, R=3 mod4, R>3*q+1, X=2^R,
eta,zeta,F,alpha,C>0.
```

Source 71 proves, for these same words and all allowed rank-tuning dummy
changes,

```
cone_A=2^1113, cone_B=2^666104,
q/2 <= cone_A*F < 4*q/5,
q/2 <= cone_B*C < 3*q/5,
G>0.
```

Its leading-digit estimates are uniform in the canonical rectangle size
and the allowed lower dummy adjustments. They do not require changing the
parity construction used by source 75.

The signed witness replacement is

```
u=2^((R-t-2)/2),  Z=q*z_old.
```

The exponent is a nonnegative integer because R,t are odd and R>3q+1.
This replacement changes neither q,F,C nor eta,zeta. Hence **G>0 and H>0
remain true**, so the nearest-square guard is satisfiable on the same
canonical witness. The sign-guard replacement and signed-power replacement
therefore compose by an explicit common witness recipe. No assertion that
they preserve every old Q41 witness is needed or made.

The exact coefficient tuple matters: substituting arbitrary ports merely
satisfying a few inequalities, or substituting compact54 ports without a
new calibration, would not be covered by this proof.

## 4. Monic restoration is exact and integral

For the 23-variable candidate, the 12 deleted arithmetic coordinates are
restored by the following integer polynomials (in dependency order):

```
q=beta*J+1,
L=q^2-1, N=q^3, C2=c^2, F2=f^2, Baux=I^2,
Delta=a^2+4*a+3,
V=f*o-c,
zeta=1-V+j*c+h*E-eta,
X=4*q*u^2,
g=y^2-V^2,
D=X+a*c+gamma*(4*a+3),
P=eta+zeta+E*(c-eta).
```

Substituting these expressions into the modified 35-variable parent makes
exactly 12 defining rows identically zero and yields exactly the 11 supplied
rows. The independent script verifies every identity coefficient by
coefficient. This gives a solution bijection with that modified parent;
no division or square-root selection is involved in these eliminations.

For the 26-variable octic, retain V,zeta,w_scale,z and instead use X=2u^2.
The ten other definitions give exactly the supplied 14 rows, again by
coefficientwise identity.

For the sextic31 companion, retain the separate eta*zeta Pos guard and use
only the determinant replacement of the F*alpha and F*C guards. The signed
bootstrap still applies. Change the root coordinate by
`tau_old=tau_tail+P-eta-zeta`, then eliminate P,F2,g,N,C2,X by their monic
definitions. All six defining rows vanish, and all18 other rows match the
delivered packet. The root shear has the polynomial integer inverse
`tau_tail=tau_old-P+eta+zeta`, so it preserves integer solvability.

For the degree14_22 companion, perform a polynomial row operation before
eliminating I. Write

```
r_strong=I^2-Delta*(f^2-1),
r_aux=y^2-I^2*(y^2-V^2)-1.
```

Replace the second by

```
r_aux_new=r_aux+(y^2-V^2)*r_strong
         =y^2-Delta*(f^2-1)*(y^2-V^2)-1.
```

This operation has an explicit inverse (subtract the same multiple of the
unchanged strong row), so it preserves the zero set over any commutative
ring. Now eliminate `I=(2r+1)c^2`. This leaves a sextic strong residual and
an octic auxiliary residual, instead of the decic auxiliary residual caused
by direct substitution of I. The independent script applies the equivalent
operation to the original parent rows, `row21 += g*row20`, and then restores
all13 deleted coordinates. Finally it applies the integral coordinate shear
`y_old=V+y_tail`, whose inverse is `y_tail=y_old-V`. Then
`y_old^2-V^2=y_tail^2+2*V*y_tail` has degree three instead of four, so the
auxiliary residual has degree seven instead of eight. The ten surviving rows
agree exactly with the final degree14 packet.

## 5. Exact-degree evidence

In the 23-variable form, after `zeta=1-(fo-c)+jc+hE-eta`, the quantity H has
the term `-eta*f*o`. The guard's `-H^2` therefore has term
`-eta^2*f^2*o^2`, of degree six. The entire sum of squares has coefficient
1 at `eta^4*f^4*o^4`, as explicitly verified after expansion. All residuals
have degree at most six. This proves exact degree 12 without treating the
fixed ports as indeterminates for the degree measure.

For the octic, the private t occurs only in the new guard. Its t^4
coefficient is -1. The sum of squares consequently has t^8 coefficient1,
and all residuals have degree at most four. This proves exact degree8 for
every specialization of the fixed ports.

For the 22-variable companion, after root centering the new auxiliary row
has the degree-seven monomial `-2*a^2*f^3*o*y_tail` relevant to the chosen
witness. The complete SOS coefficient at `a^4*f^6*o^2*y_tail^2` is exactly4. For the sextic31
companion, the retained strong-index row has `-2*r*c^2`, and the complete
SOS coefficient at `r^2*c^4` is exactly4. Both coefficients were checked
after full expansion, not inferred solely from individual summands.

## 6. Validation and limits

The independent sparse algebra implementation has a different monomial
representation from the construction code and does not import it. It also
checks every declared variable is live and no other quantified variable
is hidden in the packets. It expands the full symbolic sum of squares:
16,366 terms for the 23-variable form and 5,459 for the 26-variable form.
The companion expansions have16,492 terms for22variables/degree14 and815
terms for31variables/degree6. The normal and Python `-O` modes both pass;
no acceptance condition is implemented with a removable `assert`.

Additional finite controls cover 65,025 signed triples for guard soundness
and 22,500 positive pairs for the nearest-square witness rule. These are
regressions, not substitutes for the universal proof. The compiler, Pell
classification/strong-rank/step-down, and finite-ZFC-refutation calibration
are inherited ordinary mathematical dependencies. This audit does not
change the repository's separate formalization status.

## Sources inspected

All paths below are under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/` at the pin
above:

- `64-structural-reductions/integer41/quartic41.json`, `PROOF41.md`, `PROOF44.md`.
- `75-signed-bootstrap/guards/PROOF.md`, `guards/review/MATHEMATICAL_REVIEW.md`.
- `71-determinant-guards/proofs/DETERMINANT_GUARD.md`.
- `68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md`.
- `34-integer14/coefficients/COEFFICIENT_PROOF.md`, especially its canonical
  parity and signed-family transfer section.

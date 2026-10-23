# Three coordinated shifts: a 62-operation quadratic system

## Result

The frozen repository pin is `8c6eec9d19ef80538c8e61ff6e0180040583446a`.
Package `30-quartic31` gives 31 positive unknowns and 22 quadratic
equations, evaluated with 65 binary additions, subtractions and
multiplications, or a single quartic sum of squares evaluated with 130.
Three coordinated changes of positive coordinates reduce these counts
to **62** and **127**. The number of unknowns, number of equations,
degree, and fixed coefficient tuple are preserved.

This improves this particular low-degree point; it does not beat the
59-operation frontier for higher-degree systems or the 67-operation
frontier for a single higher-degree polynomial. No optimality is claimed.

## Explicit construction

The 31 strictly positive integer unknowns are

```
J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,
N,E,T,c,a,X,D,C2,S,F2,V,g,I,Baux,Delta.
```

The four fixed integer coefficients `beta,K0,MC,MF` must come from one
complete authenticated blank-input compiler tuple. In particular
`beta=B-1` and `MF` is the shifted source mask. The same tuple used by
the predecessor can be used without any coefficient change. Any new
tuple needs its own compiler-interface proof.

Use the affine abbreviations

```
q=beta*J+1, k=eta+zeta, H=4*a+3, C=q-F-alpha.
```

The equations, in the delivered JSON order, are

```
S=q*q,
N=q*S,
X=w*q,
a=E+s*N,
E=X*(a-E),
c=k*(a-E)+eta,
T=E*(c-eta),
tau*tau=T*(T+k)+1,
D=X+a*c+gamma*H,
Delta=a*a+H,
C2=c*c,
D*D=Delta*C2+1,
k=j*c-V+1+h*E,
j*c-V=(q-F)*(N-q)-C*(S-1)+(MC+q*MF)*J,
(K0+w)*C=F+z*(q-1),
F2=f*f,
V=o*f-c,
g=y*y-V*V,
I=i*C2,
Baux=I*I,
Baux=Delta*(F2-1),
y*y-Baux*g=1.
```

Every residual is a polynomial of degree at most two. If `r_1,...,r_22`
are left sides minus right sides, the single polynomial

```
Q = r_1^2 + ... + r_22^2
```

has degree exactly four, because `tau^4` has coefficient one.
Over positive integers `Q=0` is equivalent to all 22 equations.

## Exact coordinate transformations

Let `L_old,P_old,z_old` denote the three predecessor coordinates being
changed. All other coordinates are untouched. The substitutions are

```
L_old=S-1, P_old=T+k, z_old=z+1.
```

The old defining equations for `L_old` and `N` become
`S=q^2` and `N=q*S`. The only other occurrence of `L_old` is in
packing, where it becomes `S-1`. Consequently this shift removes two
arithmetic gates and adds one, for a net saving of one gate.

The old first-root register equation is
`P_old=E*(c-eta)+k`. Its shifted version is `T=E*(c-eta)`.
The first norm becomes `tau^2=T*(T+k)+1`. The definition saves one
addition, while the norm replaces one subtraction by one addition.

Finally the predecessor's transport residual satisfies the identity

```
(K0+w)*C+(q-F)-(z+1)*(q-1)-1
  = (K0+w)*C-F-z*(q-1).
```

The shifted transport comparison therefore saves one gate, exactly as
in the repository's established retained59 construction.

These are identities in the polynomial ring, not only equalities at
solutions. The audit checks every one of the 22 transformed residuals
against both the predecessor's expression and its literal sparse data.

## Positivity and both directions

Given a new positive solution, reconstruct the predecessor by the three
displayed formulas. Since `q>1` and `S=q^2`, `L_old=S-1>0`.
Also `P_old=T+k>0` and `z_old=z+1>0`. The exact residual identities
then give a positive predecessor solution.

Conversely, in a positive predecessor solution, put `S=L_old+1=q^2`.
The defining equations imply `a-E=s*N>0`, hence
`c-eta=k*(a-E)>0`. It follows that
`T=P_old-k=E*(c-eta)>0`.

For the transport coordinate, use the already-established positive
transport-shift lemma from `27-wave4/operations/upstream/RETAINED59_PROOF.md`.
For predecessor solutions the inherited Pell/compiler theorem gives
`C>0`, `q>1`, `X=w*q=2^R`, and `R>3*q`, in particular `w>q>F`.
Thus `(K0+w)*C-F>0`. The predecessor transport equation rewrites as

```
(K0+w)*C-F=(z_old-1)*(q-1),
```

so `z_old>=2` and `z=z_old-1>0`. This is the one positivity step that
depends on the inherited arithmetic theorem, rather than polynomial
identities alone. It is not being inferred from finite numerical tests.

The transformations are inverse on positive zero sets. Composing the
bijection with the predecessor's compiler/Pell equivalence and the K215
calibration gives the ordinary mathematical theorem formalizable in ZFC:

```
Q has no positive integer solution  <=>  Con(ZFC).
```

Neither side is assumed or proved true. This construction is not a new
end-to-end Lean/Rocq certificate.

## Counts, exact audit, and normalization

The equality-comparison evaluator has 62 live binary gates:
33 multiplications and 29 additions/subtractions. Constants are fixed
inputs; multiplication by fixed numerals is charged. Comparisons and
reuse are free, as in the repository convention. All 31 witness ports
and all four coefficient ports are live.

The sum-of-squares finalizer costs 22 residual subtractions, 22 squares
and 21 additions, giving 127 operations. Its sparse expansion has
297 monomials when the four coefficient ports are retained as independent
formal symbols. The predecessor has 306 under that convention. This is
not a claim that substituting numerical coefficients can never merge terms.

Replacing each positive unknown `x` by `n_x+1` gives a quartic over
nonnegative integers. At all positive coordinates equal to one the fifth
residual `E-X*(a-E)` equals one, independent of the fixed coefficient
tuple. Hence the shifted quartic is nonzero at the all-zero tuple, as
required by the repository's Jones compressor normalization.

Run `python3 build_quartic31_62.py` with the `upstream/` directory present. It uses only the Python standard library, reads literal JSON,
does not execute upstream code, checks all 22 residual identities and
all circuit outputs exactly in a sparse polynomial ring, verifies degree
and liveness, and emits the system, quartic and audit receipt.

## Frozen sources

- `30-quartic31/arithmetic/quartic31.json`: exact predecessor data.
- `30-quartic31/arithmetic/QUARTIC31_PROOF.md`: predecessor bijection
  to the quartic32 presentation and positivity argument.
- `27-wave4/operations/upstream/RETAINED59_PROOF.md`: the established
  positive transport-coordinate shift.

All three are under
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`
at the frozen commit stated above. The predecessor data's SHA-256 is
recorded in `QUARTIC31_62_AUDIT.json`.

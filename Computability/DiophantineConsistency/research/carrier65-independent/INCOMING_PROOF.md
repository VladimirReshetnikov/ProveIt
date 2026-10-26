# The first Pell root carries the index congruence

Delivery paths: the literal graph is equation/carrier65.json; source copies are in sources/; the construction and checks are code/arithmetic.py, verify.py, and code/check_carrier65_independent.py. Historical relative source references below identify the pinned repository context.

## Result and exact comparison

This note gives explicit positive-zero maps and zero-existence equivalence
between the maintained admissible942 P66 equation and a polynomial in **14 positive
integer variables with 65 integer-leaf binary operations and exact degree
150**. The maintained parent has 15 variables, 66 operations and degree157.
The four fixed integers are unchanged. This is an arithmetic improvement of
that particular parent; it is not a global simplicity or priority claim.

The parent is pinned to ProveIt commit
`02a78a08603cbae248c19c23a75907c6c6bd6443` at
`Computability/DiophantineConsistency/candidates/one-page-admissible942/polynomial.json`.
Its complete printed coefficient recipe is `CURRENT_P66.tex`, copied from
the same commit's `Computability/DiophantineConsistency/equation.tex`.
The ordinary parent theorem is recorded in `ADMISSIBLE942_PROOF.md`, copied
from `research/admissible942-independent/PROOF.md`, especially Section12.
`P66_POSITIVE_PROOF.md` is the uniform P66 positive theorem copied from
source174's `compact66/calibration/P66_POSITIVE_PROOF.md`.

The new proof uses only elementary Pell arithmetic in addition to the
parent theorem. It needs no new native coefficient, tiling restriction,
controller prime, strong Pell multiplier, or canonical recomputation.

## The complete new polynomial

The fourteen independent variables are

```
J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma > 0.
```

Retain the parent's four fixed integer coefficients `beta,K0,MC,MF` and put

```
qminus=beta*J, q=qminus+1, C=q-F-alpha,
X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta,
ell=E*k*Y, c=k*Y+eta, a=E+Y,
H=4*a+3, Delta=a^2+H, D=X+a*c+gamma*H,
R=[qminus*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
tau=E*n+k-R,
V=f^2*(c*T-R)-c, S=i*Delta*c^2,
N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
Na=S^2*(V^2-y^2)+y^2,
Nt=(K0+w)*C+(q-F)-z*qminus,
Ns=Delta*f^2-S^2.
```

The single equation is

```
P65 = N0*N1*Na*Nt*Ns-Delta = 0.
```

All named quantities other than the fourteen variables are polynomial
abbreviations or fixed constants. Every exponent has a fixed nonnegative
integer value. The literal division-free evaluator is `carrier65.json`.

## 1. Elementary consecutive-product Pell facts

Let `m>=2` and `D0=m(m+1)`. There is no integer solution of

```
x^2-D0*y^2=-1.
```

Indeed `y=0` is impossible. For a solution with least positive `|y|`, replace
both coordinates by absolute values. Then `m*y<x<(m+1/2)*y`. Multiplication
by the inverse of the norm-one unit `(2m+1)+2*sqrt(D0)` gives another integer
solution with second coordinate `y'=(2m+1)*y-2*x`, strictly between zero and
y, a contradiction. The bounds follow by squaring, using `m*y^2>1`.

Every solution of `x^2-D0*y^2=1` with `x,y>0` is a positive power of
`(2m+1)+2*sqrt(D0)`. One elementary proof uses the same descent: no `y=1`
solution exists because `m^2<D0+1<(m+1)^2`; for `y>=2`, the new second
coordinate is nonnegative and smaller, and the new first coordinate is
positive. The descent terminates at `(1,0)` and reversing it generates all
solutions. Consequently, if `P=2m+1`,

```
x=chi_P(r), y=2*psi_P(r), r>=1,
```

where `chi_P(r)+psi_P(r)*sqrt(P^2-1)=(P+sqrt(P^2-1))^r`.
In particular:

* if `E` divides `m`, then `x=1 mod E`;
* `y=2` when `r=1`, whereas `y>=4P` when `r>=2`;
* `x>y` because `D0>1`.

The congruence can be read directly from the recurrence modulo E:
`chi_0=1`, `chi_1=P=1 modE`, and `chi_(r+1)=2P chi_r-chi_(r-1)`.
These finite-recurrence and descent arguments are formalizable in ZFC.

## 2. Unit signs in the new equation, before rank recovery

The fixed scalar conditions inherited from admissible942 are

```
beta>=31, K0>0, 0<MC<beta<MF<2*beta.
```

On every positive assignment, `q>=32`, `X,Y,E,a>0` and
`Delta=(a+2)^2-1>0`. Also

```
Ns=Delta*Ns_normalized,
Ns_normalized=f^2-Delta*(i*c^2)^2.
```

Cancelling the nonzero integer Delta from `P65=0` gives

```
N0*N1*Na*Nt*Ns_normalized=1.
```

Each factor is therefore +1 or -1. The elementary Pell obstruction above
excludes `N0=-1`: its coefficient is `m(m+1)` for `m=EY>=2`, and its second
coordinate is k, because `ell(ell+k)=EY(EY+1)k^2`.

`Delta` is 0 or3 modulo4, so a square minus Delta times a square cannot be
3 modulo4. This excludes `N1=-1` and `Ns_normalized=-1`. Since S squared is
0 or1 modulo4, `Na` is congruent to y squared or V squared modulo4; thus
`Na=-1` is impossible as well. There is only one remaining unit factor, so

```
N0=N1=Na=Nt=Ns_normalized=1,  Ns=Delta.
```

This argument does not assume a native computation, a sign of tau, a bound
on R, or a missing quotient. In particular the transport sign is known
before the old index condition is restored.

## 3. Scalar bounds with no index quotient

If C were nonpositive, then `Nt=1`, together with `K0+w>0`, `F,z>=1`,
would give

```
1=Nt <= (q-1)-z(q-1) <=0.
```

Hence `C>0`. Put `u=q-F=C+alpha`. Positive C,alpha,F imply
`2<=u<=q-1` and `1<=alpha<=u-1`. Therefore

```
2q-1 <= G:=(q-1)u+alpha <= q^2-q-1.
```

The positive mask term satisfies

```
0 < (MC+q*MF)*J < (1+2q)(q-1).
```

The rank consequently satisfies

```
q(q^2-1) < R < (q^2-q-1)(q^2-1)+(1+2q)(q-1)
                   =q^4-q^3.
```

In particular `R>1`, `R+1<E` and `R+2<E`, since `E=wsq^4>=q^4`.
The new root abbreviation obeys

```
tau=E*n+k-R >= E+k-R > k+2 >0.
```

## 4. Recover the omitted positive quotient

Apply Section1 to `N0=1` with `m=EY`. There is `r>=1` such that

```
tau=chi_(2EY+1)(r),  k=2*psi_(2EY+1)(r).
```

Because `E|EY`, `tau=1 modE`. Substituting `tau=En+k-R` yields
`E|(k-R-1)`. Define the proof-only integer

```
h=(k-R-1)/E.
```

Since `k>0` and `R+1<E`, one has `h>-1`, so h is nonnegative. If h were
zero then `k=R+1<E`. When r=1, k=2 would force R=1, contrary to Section3.
When r>=2, `k>=4(2EY+1)>E`, also a contradiction. Thus `h>0` and

```
k-hE-R=1.
```

Retain every supplied new variable except n, take the positive tau just
constructed as the old independent root, and take this h as the old index
quotient. Every retained abbreviation and factor is literally unchanged;
the restored factor Nk is1. The whole parent P66 polynomial therefore
vanishes. This proves the soundness map by an exact arithmetic reconstruction.

## 5. The reverse map and its stronger all-zero version

For the existence implication, the parent P66 completeness theorem supplies
canonical positive zeros with
`N0=N1=Na=Nk=Nt=Ns_normalized=1` and positive R. This is all that is needed
for the main theorem. The parent's full all-zero Pell/ratio sign-recovery
theorem establishes these properties for every positive parent zero, giving
the stronger map statement below when that additional result is invoked.
These unit signs must not be inferred merely from the parent product equation.

For such a zero, Section1 gives `tau=1 modE` and `tau>k`. Since `Nk=1`,
`k-R=1 modE`. The number

```
n=(tau-k+R)/E
```

is an integer and strictly positive. Keep the thirteen other surviving
coordinates and replace the old h,tau pair by n. Then `En+k-R=tau`, all
retained factors have their old values, and the new polynomial is zero.

Under that inherited all-zero sign-recovery theorem, the formulas for h and n
are inverse on the respective zero sets. In
particular restoring h returns the original h because `Nk=1`, and restoring
tau returns its original value. Every other variable and all four constants
are preserved. This gives the stronger complete-zero-set bijection. The
reported zero-existence theorem needs only the new-to-old map of Section4
and the canonical old-to-new map of this section.

## 6. Equivalence with syntactic ZFC consistency

The new arithmetic reconstruction is uniform under the scalar boxes.
Applying it and the canonical reverse map to the exact pinned
admissible942 coefficients, then composing with the parent's ordinary
native, K215, and syntactic-refutation calibration gives

```
ZFC proves:
  (there is no positive integer zero of P65) <-> Con(ZFC).
```

This uses the same syntactic consistency predicate as the parent. It does
not assume consistency, prove unsolvability, quantify only over externally
standard certificates, or provide a new end-to-end formal-kernel proof.
The new part is elementary arithmetic; the inherited calibration and its
formalization boundary remain explicit. The current admissible942 finite
controller certificate is unchanged because all four integers are unchanged.

## 7. Exact operation count and degree

Starting with the literal P66 DAG, delete the three rows forming Nk and its
one multiplication in the output product. Replace the independent tau leaf
by the three rows `En=E*n`, `tau_partial=En+k`, `tau=tau_partial-R`, moving
the first norm after the rank producer to preserve acyclic evaluation.
Thus `66-3-1+3=65` operations, split as37 multiplications,16 additions and
12 subtractions. Every variable, fixed port and gate is live.

For total degree, variables have degree1 and fixed integers degree0.
The new tau has degree7 whereas ell has degree11, so N0 retains degree22.
The other four factor degrees are18,62,2,46. Their sum is150; subtracting
degree12 Delta cannot cancel it. The only nontrivial leading cancellation
is the main norm. With `Z=X+gamma*H`, its complete identity is

```
N1=Z^2+2*a*c*Z-H*c^2,
```

which has exact degree18. Write `q0=beta*J`, `k0=eta+zeta`. The complete
highest homogeneous form of the new output is

```
8*q0^87*gamma*i^4*k0^13*w^12*s^25*T^2*f^4
  *(w*(q0-F-alpha)-z*q0).
```

The coefficient of

```
J^88*gamma*i^4*eta^13*w^12*s^25*T^2*f^4*z
```

is `-8*beta^88`, nonzero at the actual positive beta. Exact degree150 is
therefore attained, with no numerical genericity assumption.

`build_carrier65.py` uses only the standard library. It independently
expands the full323-term main norm ancestor cone and propagates complete
leading homogeneous polynomials, obtaining all56 leader terms. It also
checks topology and liveness, the all-value product substitution identity,
128 signed formula diagnostics and156 exact Pell carrier instances. These
finite checks verify arithmetic transcription and metrics. The unbounded
zero-set theorem is Sections1-5 and the calibration is Section6.

## 8. Scope of novelty search

The collection README and current root status at the pinned commit were
inspected. Searches for direct `tau=E*n`, `tau=E...k-R`, the65/150 point and
first-root quotient carriers found no instance of this exact construction.
The collection's prior65-operation P66 evaluator uses rational leaves and
still has15 variables; it is explicitly excluded from the integer-leaf
frontier. Source170's quotient carriers use a combined Pell root `tau*y`
and adjust the strong multiplier so that y has the needed residue. The
present construction uses the bare first root, whose residue1 is already
forced, and preserves all other witnesses on those maps. This is a bounded repository
comparison, not an assertion of literature-wide novelty.

The obvious normalization dividing the parent output by Delta was also
examined and rejected as a new result: it costs an extra multiplication
because the parent shares `Delta*c^2` with its main norm. The corresponding
degree tradeoffs and reduced auxiliary coefficient were already present in
sources51,54,59 and `complete84_scaled_strong_output.md`.

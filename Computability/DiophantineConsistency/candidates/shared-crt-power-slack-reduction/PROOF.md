# Removing both redundant Pell lower-bound slacks

This new sibling retains the fixed common bound `W=n+k` and uses the
literal beta majorant `H=E+F`. It removes the separate rows and slacks
asserting `A>=2` and `B>=2` in each positive-power certificate. Both
inequalities follow from the remaining rows. All equations here are
over **nonnegative integers**. Lean formalization remains paused.

The frozen prime-lift, fixed-power-bound and beta-majorant candidates
are unchanged. `SOURCE_PINS.json` records complete authenticated parent
files and exact replacement strings. Relative to fixed-power-bound,
there are four compiler replacements:

1. Allocate only `yk`, instead of `a2,yk,b2`.
2. Delete `A=a2+2`.
3. Delete `B=b2+2`.
4. Change the shared factorial argument from `E+F+t` to `E+F`.

The source predicate, numerical C222/refutation calibration, binomial
and factorial identities, signed quotient encoding, exporter and
affine-restoration rule are unchanged. Two matching audit modules are
adapted only to remove the two old witness assignments/identities.

## 1. The actual 22-witness, 13-constraint power graph

The inputs are positive naturals `n,k`, its output is natural `m`, and
`W=n+k` is a definitional gate. The remaining semantic witnesses are

```
A,T,Z,X,Y,U,V,S,R,B, yk,q4,vd,gap,
and eight natural signed-congruence quotient coordinates.
```

There are 22 witnesses in addition to the two inputs and output.
With `N(a,x,y)=x^2-(a^2-1)y^2-1`, the exact constraints after substituting
all addition/multiplication gates are

```
Y=k+yk,
N(A,X,Y)=0,                   N(A,U,V)=0,             N(B,S,R)=0,
B=1+4Y*q4,                    V=Y^2*(vd+1),
B=A mod U,                   S=X mod U,              R=k mod 4Y,
X+Y*n=Y*A+m mod T,
2*A*n=T+n^2+1,               T=m+gap+1,
N(W+1,A,W*Z)=0.
```

Each congruence is encoded using a difference of two natural quotients.
For example `S=X mod U` means `S+U*qp=X+U*qm`, so it implies the ordinary
integer divisibility `U|(S-X)`. No assumption about the sign of the
quotient is made. All displayed equalities use integer polynomial
arithmetic. The emitted residuals are quadratic because the shared
definitional gates are retained or substituted affinely.

The exact local audit substitutes all such gates and checks these 13
polynomials. In particular the two norms in A use the **same** A and
the actual row for V is the positive multiple `Y^2*(vd+1)`.

## 2. A>=2 follows from the positive T row

At any natural zero,

```
T=m+gap+1>=1,                 2*A*n=T+n^2+1>n^2+1.
```

But `n^2+1>=2n`, because `(n-1)^2>=0`. If `A<=1`, natural arithmetic
would give `2*A*n<=2n<=n^2+1`, a contradiction. Thus `A>=2`.
This proof uses only two retained rows and the natural domain. It uses
neither the last Pell norm nor the indexed-Pell theorem, and does not
assume the unknown output already equals `n^k`.

Restore the deleted slack, if needed, by `a2=A-2`.

## 3. B>=2 follows from the retained norm and congruence rows

Since `Y=k+yk` and `k>0`, we have `Y>=1`. The row

```
V=Y^2*(vd+1)
```

therefore implies `V>=Y`. With `d=A^2-1>=3`, the two retained norms give

```
X^2=1+d*Y^2>=1+d=A^2,       U^2=1+d*V^2>=1+d*Y^2=X^2.
```

All coordinates are natural, so `U>=X>=A>=2`. In particular U is a
positive modulus and `0<X-1<U`.

The retained definition `B=1+4Y*q4` first gives `B>=1`. Suppose `B=1`.
Its norm `N(B,S,R)=0` reduces to `S^2=1`, hence `S=1` over naturals.
The retained congruence `S=X mod U` then gives `U|(X-1)`. This contradicts
`0<X-1<U`. Thus `B>=2`.

Restore its old slack by `b2=B-2`. The proof does not invoke B's Pell
index, assume `q4>0`, or use either deleted lower-bound condition. All
premises appear among the exact 13 retained constraints.

## 4. Power soundness and completeness

Given a natural zero with `n,k>0`, Sections 2--3 restore both deleted
slacks. Set `wn=k,wk=n` to restore the older common-bound witnesses.
Every original positive-power constraint is now satisfied. The parent
indexed-Pell and power soundness theorems therefore give `m=n^k`.

For its ordinary-subtraction boundary, the retained final norm is

```
A^2=1+W^3*(W+2)*Z^2.
```

Since `A>=2`, Z cannot be zero. With `W=n+k>=2` and `Z>=1`, this gives
`A>W>=n`. Thus natural `A-n` agrees with ordinary subtraction, and the
moved power congruence is precisely the parent's congruence. This order
does not use an indexed-Pell conclusion to establish its own hypotheses.

Conversely, for every positive `n,k`, canonical fresh Pell witnesses
exist at **every** `W>=n,k`, and in particular at `W=n+k`. Explicitly put

```
A=chi_(W+1)(W),   W*Z=psi_(W+1)(W),
T=2*A*n-n^2-1,   X=chi_A(k),   Y=psi_A(k).
```

The Pell congruence `psi_a(j)=j mod(a-1)` makes Z natural. The bounds

```
n^k<=n^W<(W+1)^W<=A,          0<n^k<T,                Y>=k
```

license every required slack, and the standard Pell power congruence
and indexed-Pell criterion supply the remaining coordinates. Removing
the two old lower-bound rows cannot spoil this construction.
The full arbitrary-common-bound proof and exact mathematical source
pins are reproduced in `FIXED_BOUND_PROOF.md`. We reconstruct fresh
witnesses instead of shifting an existing bound W.

## 5. H=E+F has the required height and positivity

In the direct compiler's literal uncancelled source split, the beta
remainder row has sides `D=1+(t+1)y` and `S+r+1`. Its square contributes
`D^2+(S+r+1)^2` to E. Other contributions are natural, so `E>=D^2` and
`H=E+F>=1` before any macro is interpreted. The actual dependency cone
contains only `t0,m0,x,y,M0,U`, not CRT columns, encoded indices or power
outputs.

The separately retained endpoint is exactly `y=M0+r0+2`. It gives
`y>=2`, hence `D>=2t+3` and `H>=D^2>=t`. Use its ordinary gate equations
and this endpoint before interpreting the CRT. A statement `H>=t` for
arbitrary assignments violating the endpoint is false; the exact
majorant audit retains an off-source counterexample.

The prime-supported CRT lemma requires only
`H>=t,E(t,z,u),F(t,z,u)`. Its strengthened moduli include the complete
prime-supported part of each local range factorial; it never assumes
`H>=u_j+1`. They remain pairwise coprime, and sufficiently large CRT
lifts produce positive encoded columns. See the complete reproduced
ordinary arguments `PRIME_LIFT_PROOF.md` and `BETA_MAJORANT_PROOF.md`.

## 6. Both directions for the full equation

At a full natural zero, restore all eliminated nonnegative affine
gates. Interpret their ordinary gate equations and the endpoint to
establish `H>=1,t`. The unchanged static positivity induction licenses
all 55 actual positive-power calls. Sections 2--4 interpret them in
topological call order, including both indexed-Pell lower bounds.
The binomial/factorial macros retain their licensed arguments and
therefore give the exact shared CRT certificate. Prime-supported CRT
soundness recovers all bounded direct-source rows; the same explicitly
inherited numerical C222/refutation calibration applies.

For completeness, choose a finite calibrated direct-source certificate
and endpoints, then a bound U on its finitely many private coordinates.
Compute the new E,F,H and reconstruct its strengthened CRT columns and
index. Their positivity and the static dependency induction license
each arithmetic macro. The fresh common-bound construction in Section
4 supplies every power witness. Choose the remaining definitional
gates and apply the unchanged nonnegative affine substitutions. This
is a natural zero of the new quartic. We recompute CRT columns after
changing H, rather than keeping unjustified old encoded values.

This is an ordinary zero-existence equivalence with the same named
refutation predicate as the parent. It does not prove absence of zeros,
Con(ZFC), a new Lean theorem, or an encoded internal object-ZFC
derivation. No native coefficient tuple is used by this direct route.

## 7. Exact materialized metrics and verification

| Equation | Naturals | Quadratic rows | Quartic terms | Height |
|---|---:|---:|---:|---:|
| Frozen prime-lift affine | 3,609 | 2,949 | 15,752 | 127,285,349 |
| Frozen fixed-W affine | 3,443 | 2,838 | 15,754 | 127,302,193 |
| **Both-slack reduction affine** | **3,328** | **2,723** | **15,289** | 127,299,660 |
| Frozen prime-lift retained | 6,180 | 5,520 | 17,421 | 1,992 |
| Frozen fixed-W retained | 5,960 | 5,355 | 16,894 | 1,992 |
| **Both-slack reduction retained** | **5,739** | **5,134** | **16,230** | **1,552** |

All have exact degree four and every variable occurs. The affine point
saves 281 variables against prime-lift at its stated height tradeoff;
the retained point improves every size column. It contains 1,395
semantic coordinates and 1,933 gate coordinates. The 55 actual ordered
base/exponent atom pairs are distinct; equal-ID memoization saves no
additional graph.

The normal and optimized checkers authenticate the complete source
replacement and copied proof/auditor bytes, reconstruct both complete
SOS expansions, verify all local 22-witness/13-constraint identities,
check the actual beta-majorant/endpoint path, and run the arithmetic,
positive-input and affine-restoration audits. Finite arbitrary-bound
controls check the fresh Pell transcription. The unbounded reasoning
is in Sections 1--6. Superseded intermediate measurements are preserved
separately in `RESEARCH_HISTORY.md`; their generated files are not the
definition of this final candidate.

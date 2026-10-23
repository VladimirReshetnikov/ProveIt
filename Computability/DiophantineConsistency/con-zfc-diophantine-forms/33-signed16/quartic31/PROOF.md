# A cheaper 31-variable positive quartic

## Result

The wave-4 package `30-quartic31` gives a 31-positive-variable system of
22 quadratics in 65 charged binary operations, and a quartic sum of squares
in 130 operations. Four affine coordinate changes reduce these counts to
**61** and **126**, respectively. All 31 unknowns and all four fixed
coefficient ports remain live. The quartic has 259 symbolic monomials when
the four ports are retained as symbols, compared with the parent's 306.

This is an improvement in arithmetic presentation, not in variable count or
degree. It does not beat the separate 59-operation system, which has degree
24, or the separate 67-operation single equation, which has degree 155.
The 31-variable quartic remains useful as a low-degree equation and as input
to a nine-variable reduction. No global minimum is claimed.

Source pin: `8c6eec9d19ef80538c8e61ff6e0180040583446a`.
The parent is
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/30-quartic31/arithmetic/quartic31.json`.
Its exact bytes and original proof are retained in `upstream/`.

## Literal system

All coordinates range over the strictly positive integers:

```
J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,
N,Y,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta.
```

There are exactly 31 of them. The four fixed integer ports are
`beta,K0,MC,MF`; `MF` is the shifted mask. They must be the complete tuple
in the enclosing release's coefficient binding, with no mixing of ports.
Define the affine abbreviations

```
q=beta J+1, k=eta+zeta, H=4a+3, C=q-F-alpha, E=a-Y.
```

The 22 equations are

```
L=q^2-1,                         N=qL,
X=wq,                           Y=s(N+q),
E=XY,                           c=kY+eta,
P=E(c-eta),                      tau^2=P(P+k)+1,
D=X+ac+gamma H,                  Delta=a^2+H,
C2=c^2,                         D^2=Delta C2+1,
k=jc-V+1+hE,
jc-V=(q-F)N-CL+(MC+q MF)J,
(K0+w)C=F+z(q-1),
F2=f^2,                         V=of-c,
g=y^2-V^2,                      I=i C2,
Baux=I^2,                       Baux=Delta(F2-1),
y^2-Baux g=1.
```

Every abbreviation is affine in these 31 variables, so each residual is
quadratic. If `r1,...,r22` denote the displayed left sides minus right sides,
the single equation is

```
Q31* = r1^2 + ... + r22^2 = 0.
```

There are no variable exponents, unexpanded existential signs, divisibility
predicates, or square-root operators. All fixed exponent notation has its
ordinary polynomial meaning. The JSON circuits fully specify the arithmetic.

## Exact affine equivalence

Use a subscript `old` for the parent's coordinates. The simultaneous
substitution is

```
N_old=N+q,       E_old=a-Y,       P_old=P+k,       z_old=z+1.
```

Every other coordinate is unchanged. This is an invertible affine change
over the integers (with the fixed coefficient `beta` in `q`). The inverse
is

```
N=N_old-q,       Y=a-E_old,       P=P_old-k,       z=z_old-1.
```

Under this substitution each of the parent's 22 literal sparse residuals
is **identically equal** to the corresponding new residual, not merely
congruent modulo other equations. Thus the quartic identity

```
Q31*(new variables)=Q31(old variables expressed by the substitution)
```

holds throughout the integer polynomial ring. The finite audit proves all
22 identities while treating the four fixed coefficient ports as independent
symbols. The only extra issue is preservation of the positive domain.

### New positive zero to old positive zero

The equation `E=XY`, together with positivity of `X,Y`, shows that the
restored coordinate `E_old=a-Y=XY` is positive. The other three changed
coordinates `N_old=N+q`, `P_old=P+k`, and `z_old=z+1` are positive immediately.
The identical residuals therefore reconstruct a positive parent zero.

### Old positive zero to new positive zero

The parent's equations give

```
N_old=q(L+1),
a-E_old=sN_old,
c-eta=k(a-E_old),
P_old-k=E_old(c-eta).
```

Since `q>1` and `L=q^2-1`, the inverse gives

```
N=qL>0,
Y=sN_old>0,
P=E_old kY>0.
```

For the transport quotient, the source Pell/compiler proof supplies
`C>0`, `X=wq=2^R`, `R>3q`, and `F<q`. Hence `w>F` and
`(K0+w)C-F>0`. The parent's transport equation is equivalent to

```
(K0+w)C-F=(z_old-1)(q-1).
```

Because `q-1>0`, it follows that `z_old>=2`, so `z=z_old-1>0`.
This is exactly the transport-quotient positivity lemma used by the
upstream retained59 system, whose proof is copied in `upstream/`.
It must not be replaced by the false inference that positivity of
`z_old` alone implies positivity of `z_old-1`.

The two affine maps are inverse on the positive zero sets. Composition with
the inherited quartic/Pell/native-compiler/K215 equivalence yields the
theorem formalizable in ZFC:

```
Q31* has no positive integer zero  <=>  Con(ZFC).
```

This states an equivalence, not the truth of either side, and is not a new
end-to-end Lean or Rocq certificate.

## Where the four saved gates come from

All counts charge every binary addition, subtraction, and multiplication,
including multiplication by small integers or coefficient ports; comparisons
and reuse are free.

1. `z_old=z+1`: replacing the old transport comparison with
   `(K0+w)C=F+z(q-1)` removes one addition/subtraction.
2. `P_old=P+k`: replacing `P_old=E_old(c-eta)+k` by
   `P=E(c-eta)` removes one addition. The first norm uses `P+k`
   where the parent used `P_old-k`, at the same cost.
3. `E_old=a-Y`: the graph equation `a=E_old+sN_old` becomes
   `Y=sN_old`, removing one addition. Computing the affine expression
   `a-Y` takes the place of computing the parent's `a-E_old`.
4. `N_old=N+q`: the graph `N_old=q(L+1)` becomes `N=qL`,
   removing one addition, and packing no longer computes `N_old-q`,
   removing one subtraction. The equation `Y=s(N+q)` pays for one
   addition. The net saving is one operation.

The resulting system circuit is `61=33M+28A`. Computing 22 residuals,
their 22 squares, and 21 additions costs 65 further gates, so the quartic
circuit is `126=55M+71A`. There are no dead gates or unused inputs.

## Exact degree and nonnegative normalization

Each residual has degree exactly two. The variable `tau` occurs only as
`tau^2` in the eighth residual, so the coefficient of `tau^4` in the
quartic is exactly 1, uniformly in the coefficient ports. Its degree is
therefore exactly four.

Replacing every positive coordinate `x` by `n_x+1` gives an equation over
31 nonnegative unknowns. At all positive coordinates equal to 1, residual
5 is `a-Y-XY=-1`, independently of the four ports. Consequently the shifted
quartic has positive constant term, preserving the normalization condition
needed by the inherited nine-variable compressor. No nine-variable output
is claimed for this new quartic in this directory.

## Reproduction and attribution

Run `python3 build_and_verify.py`. No third-party Python modules are needed.
The script checks exact sparse identities against the literal parent,
exact residual degrees, the `tau^4` certificate, the normalization witness,
literal circuit semantics, operation counts, and complete liveness. It
writes `system61.json`, `quartic126.json`, `polynomials.json`, and
`CHECKS.json`.

The parent quartic construction, its source calibration, and the positive
transport shift are upstream ProveIt work. This directory contributes their
four-coordinate affine synthesis, the cheaper literal arithmetic schedule,
and an independent exact verifier. The retained parent files carry the
upstream licence in `upstream/LICENSE.ProveIt`.

Finite algebraic verification does not prove the inherited unbounded
Pell/compiler semantics or ZFC's consistency. Its role is to ensure that
this arithmetic simplification adds no new algebraic or domain gap.

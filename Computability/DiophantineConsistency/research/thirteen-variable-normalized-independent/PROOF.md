# Normalized thirteen-positive carrier:71 integer operations and degree128

Author: `/root/complemented47_review`. This proof implements ROOT's
normalization lead as a separate complete polynomial at the frozen2471
ports. The accepted69/174 and70/140 graphs, their proof, and the current
fourteen-variable page remain unchanged. Independent review and the
literal finite audit are separate receipts.

## 1. Exact retained interface

Use precisely the four complete integers beta,K,MC,MF_source from
`../phase-split-independent/PROOF.md`, SHA256
`934c7984038b578a68b1396fffdb8db71a9039b01a86455a74c8639264a1b966`,
and its finite certificate
`f6c576194bfd60d10457c6ba9c43c0b7a8537639588c4f022e7a0362b9051bef`.
They are the full L2471,d116137,clause1462,marker1004 tuple, with
58125 minimal unsigned bytes. Write MF for MF_source; this includes
exactly its one beta shift. In particular beta>=31,K>0 and
0<MC<beta<MF<2beta.

The complete thirteen-variable existence theorem is
`../thirteen-variable-independent/PROOF.md`, corrected SHA256
`d2e40a04fdc670a5f5a05d2c8e7e762e07ef559eb051e5ff6f5c82e7e3e8f6a8`.
Its entire70-row graph is
`b36b1b4fa645b772d5cafe82a0359eca264e228114cacd2fcce6da902b2eac82`;
the accompanying69-row graph is
`3400069ead0bbf7b85d382c47fdd790bc18d68d9979e049f475d4e1c52d4182f`.
The source of this new step is ROOT's separate NORMALIZED_LEAD.md,
SHA256 `50c2adcb78198e111abba88344fccabfd2a493399cf02772316418eae3ea9f57`.
The older incoming69-operation schedule is retained only through those
already authenticated predecessors. No incoming executable is run.

The independent unknowns remain the thirteen strictly positive integers

```
J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma.
```

All other symbols below are polynomial abbreviations:

```
b=beta*J, q=b+1, C=q-F-alpha,
X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta,
ell=E*k*Y, c=k*Y+eta, a=E+Y, H=4*a+3,
Delta=a^2+H, D=X+a*c+gamma*H,
R=[b*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
tau=E*n+k-R, G=(K+w)*C-F,
V=f^2*(c*T-R)-c,
y=1+4*[b*(m-V^2*G)-G],
P=tau^2-ell*(ell+k), Q=D^2-Delta*c^2,
Theta=Delta*(f^2-1), U=Theta*(V^2-y^2)+y^2,
Z=f^2-Delta*(b*i*c^2)^2.
```

The complete new single equation is

```
pbar=P*Q*U*Z-1=0.                                   (1)
```

Every exponent is a fixed nonnegative integer. No quotient, floor,
variable exponent, additional predicate or rational leaf occurs in
this polynomial. All fixed constants belong to the exact stated tuple.

## 2. Whole positive-zero-set identity

Let S=b*i*Delta*c^2. This symbol is needed here only to compare the
parent polynomial. The parent strong factor is

```
Zold=Delta*f^2-S^2
    =Delta*[f^2-Delta*(b*i*c^2)^2]
    =Delta*Z.                                       (2)
```

The parent's other factors P,Q,U and its literal signed y are exactly
those in section1. Hence in the entire integer polynomial ring,

```
p70=P*Q*U*Zold-Delta=Delta*(P*Q*U*Z-1)=Delta*pbar.   (3)
```

For every strictly positive assignment of the thirteen unknowns,
q>0,X>0,Y>0,E>0,a>0 and Delta=a^2+4*a+3>0. These inequalities hold
before assuming either equation, a sign for y/G/C/R, or any decoded
native witness. Thus cancellation in(3) proves the exact identity of
whole thirteen-coordinate positive zero sets:

```
pbar=0 if and only if p70=0.                         (4)
```

Both maps are the identity on all thirteen independent coordinates.
This is stronger than merely identifying canonical zeros. No new
negative-unit exclusion, Pell classification or divisibility assumption
is required for the normalization itself.

Composing(4) with the complete parent theorem gives both directions
at the actual2471 ports. Every positive zero of(1) is a parent zero
and therefore yields a finite syntactic ZFC refutation. Conversely,
the parent's fresh-seed construction from any such refutation supplies
thirteen positive inputs with p70=0; the same inputs have pbar=0 by(3).
The native masks, controller, binary rank, positivity and fresh Pell
seed obligations are inherited through that exact full theorem, not
through a changed-constant substitution or finite examples.

## 3. Complete literal schedule and exact degree

Starting with the complete parent70 graph, retain hi=b*i and
Dc2=Delta*c^2. Replace the two multiplication rows for S and S^2 by
three rows:

```
hi2=hi*hi,
intermediate=hi2*Dc2,
strong_term=intermediate*c^2.
```

The new strong subtraction is Z=f^2-strong_term, and the output
subtraction is product minus1. The product's strong-factor reference
is updated accordingly. The other operations are unchanged. Dc2 stays
live in the main norm Q; Delta*f^2 stays live through Theta. Every
remaining producer, each positive unknown and every fixed port must
be checked for liveness by the complete literal audit. The exact count
is71 binary operations:40 multiplications,16 additions,15 subtractions.
The source keeps only integer leaves.

For degree, put q0=beta*J, k0=eta+zeta and C0=q0-F-alpha. Total degree
counts all thirteen unknowns and treats the four ports as constants.
The complete leading forms of the unchanged three factors are

```
P0=-w^2*s^4*k0^2*q0^14,
Q0=8*gamma*w^2*s^3*k0*q0^11,
U0=-16*q0^22*k0^4*s^6*w^4*f^10*T^4*C0^2.
```

The Q calculation uses the exact entire identity
Q=(X+gamma*H)^2+2*a*c*(X+gamma*H)-H*c^2, resolving its canceled
highest terms. The new strong factor has leading form

```
Z0=-i^2*w^2*s^6*k0^4*q0^22.
```

The four exact factor degrees are22,18,52,36. Their product is

```
-128*q0^69*gamma*i^2*k0^11*w^10*s^19*f^10*T^4*C0^2.  (5)
```

It is nonzero. In particular the coefficient of
J^71*gamma*i^2*eta^11*w^10*s^19*f^10*T^4 is−128*beta^71,
which is nonzero at the actual positive beta. Thus the exact total
degree is128. Equivalently(3), the parent's exact degree140 and
Delta's degree12 give the same result in an integral polynomial ring.
The finite audit must check all gate leaders and the full form(5),
not merely an upper bound from degree propagation.

## 4. Logical and measurement boundary

Composed with the explicitly retained ordinary native and syntactic
calibration, ZFC proves that(1) has no positive integer zero iff Con(ZFC).
This is not an assertion of actual consistency or unsolvability. The
ordinary foundational contracts and absence of a fresh end-to-end
formal-kernel/internal-ZFC replay remain unchanged.

The new graph saves12 degrees against70/140 at the cost of one extra
integer multiplication. It retains thirteen positive unknowns and all
four complete2471 ports. It is an operation/degree tradeoff, not a claim
of global minimality. No displayed page, changed seed, new native tuple
or unrestricted39-variable graph is supplied by this proof. Existing
accepted sources remain frozen.

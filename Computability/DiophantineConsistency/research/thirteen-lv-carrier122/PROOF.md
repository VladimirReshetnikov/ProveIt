# Mixed-carrier thirteen-variable equations: 72/124 and 74/122

Author: `circuit_reduction`. The two equations have thirteen strictly positive
integer unknowns and the complete CURRENT2011 ports. Their entire positive
zero sets are related to their respective accepted parents by explicit inverse
polynomial witness maps. No canonical-zero restriction, additional arithmetic
hypothesis, or change to the maintained fourteen-variable page is made.

The mixed carrier itself is prior art in the prospective paragraph beginning
“The archive's companion uses” in
`../scaled-auxiliary118/THIRTEEN_VARIABLE_LEAD.md`. That note called the complete
product `(c*T-R)*V` by the letter L and predicted an unnormalized71/136 variant.
Here L names only `c*T-R`. This packet supplies current-port materialization,
complete positive-zero maps, and composition with normalization and the optional
first-norm correction. No novelty or global minimum is claimed.

## Complete equations and domain

Use all four integers `beta,K,MC,MF_source` from the accepted
`padding-staircase-independent` certificate and the matching maintained
`one-page-padding-staircase-carrier65-2011` candidate. MF means MF_source, which
already includes its single beta shift. All four integers are materialized and
checked by the separate finite audit; their total raw size is47313 bytes.
The algebraic maps below are uniform for every integer port tuple with beta>0.

The independent coordinates are, in order,

```text
J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma > 0.
```

Every following symbol is a polynomial abbreviation:

```text
b=beta*J, q=b+1, C=q-F-alpha,
X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta,
ell=E*k*Y, c=k*Y+eta, a=E+Y, H=4*a+3,
Delta=a^2+H, D=X+a*c+gamma*H,
R=[b*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
tau=E*n+k-R, G=(K+w)*C-F,
L=c*T-R, V=f^2*L-c, S=b*i*Delta*c^2,
y=1+4*[b*(m-L*V*G)-G],
P=tau^2-ell*(ell+k), Q=D^2-Delta*c^2,
Theta=Delta*(f^2-1), U=Theta*(V^2-y^2)+y^2,
Z=f^2-(b*i)^2*c^2*(Delta*c^2),
Zcorrected=f^2-(b*i)^2*c^2*(Delta*c^2+P-1).
```

The new equations are

```text
p72=P*Q*U*Z-1=0,
p74=P*Q*U*Zcorrected-1=0.
```

Their respective parents p71 and p73 have exactly the same formulas except
that their signed ordinate is `yold=1+4*[b*(m-V^2*G)-G]`. The two parents and
their current-port consistency transfers remain frozen.

## Norms obtained from either mixed equation

All coordinates are positive and beta>0, so b>0, Delta>0, c>=2 and S>=2 before
assuming an equation. The first norm P has the actual consecutive-product
shape `tau^2-(E*Y)*(E*Y+1)*k^2`, with E*Y>=2. The accepted consecutive-Pell
descent excludes P=-1 on every such assignment. Either product equation makes
P an integer unit, so P=1. The corrected and uncorrected strong factors now
agree. In particular p72 and p74 have identical positive zero sets by the
identity map, with P=1 derived separately from either product.

Delta=(a+2)^2-1 is0 or3 modulo4. Thus Q and Z cannot be-1 modulo4. Each is
an integer unit, so Q=Z=1; the remaining product factor is U=1. Consequently

```text
f^2-Delta*(b*i*c^2)^2=1,
Theta=Delta*(f^2-1)=S^2,
S^2*V^2-(S^2-1)*y^2=1.                         (1)
```

Exactly the same argument applies to the old ordinate in either parent.
The auxiliary norm in(1), with S>=2, gives `|y|<2*|V|`; it does not require
a sign for y or V. These are the accepted auxiliary estimates, applied to
the literal ordinate of the equation currently under consideration.

## Mixed-product bounds without a sign assumption

The strong norm, Delta>=1, b*i>=1 and c>=2 give

```text
f^2>=c+1,             S^2>c^2.                 (2)
```

Suppose L=0. Then V=-c and the auxiliary norm gives

```text
(S^2-1)*(y^2-c^2)=c^2-1.
```

The right side is a positive integer strictly smaller than S^2-1. An integer
multiple of S^2-1 cannot lie in that interval. Hence L≠0. Since L is an integer,
either L>=1 or L<=-1. Substitution into V=f^2*L-c and(2) gives
`sign(V)=sign(L)` and `|V|>=|L|`. It follows that

```text
|V| <= L*V <= V^2.                              (3)
```

These facts are derived from either entire positive zero, not inserted as
extra premises on the final equations.

For either A=V^2 or A=L*V, (3) gives A>=|V|>=0. If G<=-1, positivity of b,m
and the corresponding carrier identity imply

```text
y=1+4*[b*m+(1+b*A)*(-G)] >= 9+4*A > 2*|V|,
```

contradicting the auxiliary estimate. Thus G>=0 for either carrier. This
does not use a native window, alignment, divisibility, or decoded witness.

## Exact inverse maps and positivity

The abbreviations b,L,V,G and every common norm block are independent of m.
Define `d=G*(V^2-L*V)` and change only coordinate11:

```text
old to new:  m_new=m_old-d,
new to old:  m_old=m_new+d.
```

Over every commutative ring these maps are inverse, their corresponding
signed ordinates are equal, and they give the whole-polynomial identities

```text
p71(toOld(v))=p72(v),       p72(toNew(v))=p71(v),
p73(toOld(v))=p74(v),       p74(toNew(v))=p73(v).
```

They preserve the other twelve coordinates literally. On a new positive zero,
G>=0 and(3) imply d>=0, so the new-to-old map preserves positivity immediately.

On an old positive zero, if G=0 the old-to-new map changes nothing. If G>=1,
use its old carrier identity to obtain

```text
4*b*m_new = 4*b*L*V*G + 4*G + yold - 1.
```

Since `|yold|<2*|V|` and all quantities are integers,
`yold-1>=-2*|V|`. Also b>=1, G>=1 and L*V>=|V|. The displayed right side is
therefore at least `2*|V|+4>0`. Hence m_new>0. This proves both directions
on the entire positive zero sets and a bijection between corresponding zeros.
Positivity is not claimed for arbitrary inputs: at ports(3,1,1,1) and all
thirteen inputs1 the subtractive map sends m to-59984. The focused Lean checks
verify that explicit counterexample to the stronger unsupported assertion.

## Exact metric changes and retained endpoints

Starting from the accepted71-row graph, insert one multiplication
`LV=(c*T-R)*V` and change the carrier input `V^2*G` to `LV*G`. The existing
V^2 remains live in the auxiliary norm. This gives72 operations:41 products,
16 additions and15 subtractions. Starting from the accepted73-row corrected
graph gives74 operations:41 products,17 additions and16 subtractions.
The complete topology, liveness, integer leaves, full port bytes, and both
polynomial-substitution identities are checked independently by the auditor.

With `q0=beta*J`, `k0=eta+zeta`, `C0=q0-F-alpha`, the new ordinate leader is

```text
-4*q0^7*k0^2*s^2*w*f^2*T^2*C0.
```

Its exact degree is17. The complete auxiliary leader is
`-16*q0^22*k0^4*s^6*w^4*f^6*T^4*C0^2`, of degree48. The unchanged P,Q
leaders have degrees22,18. Z has degree36 and Zcorrected has degree34.
The two complete output leaders are respectively

```text
-128*q0^69*gamma*i^2*k0^11*w^10*s^19*f^6*T^4*C0^2,   degree124;
-256*q0^68*gamma*i^2*k0^11*w^9*s^19*f^6*T^4*C0^2,    degree122.
```

Their selected coefficients are `-128*beta^71` and `-256*beta^70`, nonzero
at every positive beta. The full finite audit resolves the actual main-norm
and optional corrected-coefficient cancellations and checks every gate leader.
These are separate finite metric proofs, not Lean `totalDegree` theorems.

`ThirteenLVCarrier.lean` proves both witness maps, both entire positive-zero
transfers, both current polynomials and both closed external equivalences
with the actual `DiophantineConsistency.ConZFC` predicate. It uses precisely
`CurrentWindowCarry2011.ports`. It does not prove an HA derivation or assert
consistency. The new72/124 profile improves the earlier73/126 operation and
degree pair;74/122 is a further degree/operation tradeoff. The13/71/128 and
maintained14/65/150 points remain distinct tradeoffs.

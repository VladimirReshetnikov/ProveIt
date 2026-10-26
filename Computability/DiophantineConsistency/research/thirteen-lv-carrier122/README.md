# Thirteen positive variables: mixed carrier at 72/124 and 74/122

This packet replaces the squared signed-ordinate carrier by a mixed product
at the complete current2011 coefficient tuple. The independent coordinates
remain `J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma`, all strictly positive integers.
The four fixed ports remain `beta,K,MC,MF_source`, occupying 47313 raw bytes.
The high source mask is already shifted by beta exactly once.

| Complete graph | Multiplications | Additions | Subtractions | Operations | Degree |
|---|---:|---:|---:|---:|---:|
| `polynomial72.json` | 41 | 16 | 15 | 72 | 124 |
| `polynomial.json` | 41 | 17 | 16 | 74 | 122 |

The 72/124 profile improves both operation count and degree over the earlier
73/126 checkpoint. The 74/122 profile trades two more operations for two
fewer degrees. Neither dominates the older 71/128 profile or the maintained
fourteen-variable 65/150 profile on all metrics. No global minimum is claimed.

The mixed-carrier idea predates this packet. The retained
[`THIRTEEN_VARIABLE_LEAD.md`](../scaled-auxiliary118/THIRTEEN_VARIABLE_LEAD.md)
already describes the archive companion's `(c*T-R)*V` replacement and its
prospective 71/136 profile before strong normalization/correction. That note
records the inert `ConZFC_Pell_Centers_and_Fused_Bounds_2026-10-25.zip`
source and hashes. This work credits that lead; it does not claim novelty
for the mixed product. We did not execute the archive or its code.

## Complete formulas and graph changes

Use these complete abbreviations, with `b=beta*J`:

```text
q=b+1, C=q-F-alpha
X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta
ell=E*k*Y, c=k*Y+eta
a=E+Y, H=4*a+3, Delta=a^2+H, D=X+a*c+gamma*H
R=(b*(q-F)+alpha)*(q^2-1)+(MC+q*MF_source)*J
tau=E*n+k-R
L=c*T-R, V=f^2*L-c, G=(K+w)*C-F
y=1+4*(b*(m-L*V*G)-G)
P=tau^2-ell*(ell+k), Q=D^2-Delta*c^2
Theta=Delta*(f^2-1), U=Theta*(V^2-y^2)+y^2
Z=f^2-(b*i)^2*c^2*(Delta*c^2)
Zcorrected=f^2-(b*i)^2*c^2*(Delta*c^2+P-1)
p72=P*Q*U*Z-1
p74=P*Q*U*Zcorrected-1.
```

In each parent schedule, `cTminusR` already computes `L`. Insert exactly
`LV=L*V`, and change the existing `LB=V2*G` row to `LB=LV*G`.
The `V2=V*V` row remains needed by the auxiliary factor; it cannot be deleted
or treated as a free square. Every row, all thirteen unknowns, and all four
ports are live in each complete graph. The audit also supplies unequal
modular evaluations certifying genuine polynomial dependence on each
unknown at the actual fixed ports, and on each formal port with the other
ports fixed. Those dependence witnesses are not zero-set proofs.

`polynomial72.json` is independently transformed from the frozen normalized
71-row graph, then rebound to the current2011 constants. The normalized
parent's original2471 specialization is not asserted equal to this one.
The corrected graph is transformed from the separately frozen current2011
73-row graph. No accepted parent is edited.

## Exact positive witness maps

Let `yold=1+4*(b*(m-V^2*G)-G)` and `correction=G*(V^2-L*V)`.
The polynomial maps alter only coordinate `m`:

```text
new to old: m_old=m_new+correction
old to new: m_new=m_old-correction.
```

All data used in the correction are independent of `m`, so these are
inverse maps over every commutative ring. The full literal graph with the
old carrier, evaluated after the first map, equals the full new graph;
the reverse identity holds after the second map. These are not identical
polynomials at identical coordinates. The finite auditor checks both
identities and the complete nonzero same-coordinate difference, using
independent common polynomial subexpressions. It also checks

```text
p74=p72-P*Q*U*(b*i*c)^2*(P-1).
```

The domain argument is in [PROOF.md](PROOF.md) and
`ThirteenLVCarrier.lean`, authored by `circuit_reduction`. It derives the
norm signs separately from each actual positive zero. In particular, it
does not assume `P=1`, positivity of the signed ordinate, a canonical
native witness, or positivity of the subtractive map on arbitrary inputs.
On each zero it obtains `L!=0`, `abs(V)<=L*V<=V^2`, `abs(y)<2*abs(V)` and
`G>=0`. The additive map is positive immediately. For the subtractive map,
`G=0` leaves `m` unchanged; for `G>=1` the exact ordinate identity proves
the new `m` positive. The uncorrected/corrected mixed polynomials have
the same positive zeros because each zero separately forces `P=1`.

The Lean endpoints transfer to the actual current `ConZFC` predicate.
This remains an external Lean equivalence. Neither the degree audit nor
those endpoints assert an HA derivation, an internal ZFC derivation,
actual consistency, or actual unsolvability.

## Exact degrees

Set `q0=beta*J`, `k0=eta+zeta`, and `C0=q0-F-alpha`. The common factor
leaders are

```text
P0 = -w^2*s^4*k0^2*q0^14                       (degree22)
Q0 = 8*gamma*w^2*s^3*k0*q0^11                  (degree18)
U0 = -16*q0^22*k0^4*s^6*w^4*f^6*T^4*C0^2      (degree48).
```

The two strong leaders and whole leaders are

```text
Z0 = -i^2*w^2*s^6*k0^4*q0^22                  (degree36)
Zcorrected0 = -2*i^2*w*s^6*k0^4*q0^21          (degree34)
p72_0 = -128*q0^69*gamma*i^2*k0^11*w^10*s^19*f^6*T^4*C0^2
p74_0 = -256*q0^68*gamma*i^2*k0^11*w^9*s^19*f^6*T^4*C0^2.
```

The audit propagates complete homogeneous leaders through every gate.
The main norm's leading cancellation is resolved by its full 323-term
expansion. The corrected strong coefficient has a second cancellation,
resolved by its full 353-term expansion and the exact identity

```text
Delta*c^2+P-1
 = ((2*X+1)*Y^2+H)*c^2
   +E^2*eta*(2*k*Y+eta)-E*k^2*Y+tau^2-1.
```

There are no other complete leading cancellations. Each whole leader
has 72 expanded terms. The coefficients of
`J^71*gamma*i^2*eta^11*w^10*s^19*f^6*T^4` in p72 and
`J^70*gamma*i^2*eta^11*w^9*s^19*f^6*T^4` in p74 are respectively
`-128*beta^71` and `-256*beta^70`. These are nonzero for the actual positive
beta, proving exact specialized degrees124 and122. The finite degree
calculation is not represented as a Lean `totalDegree` theorem here.

## Complete current ports and reproduction

All four complete gzip files are included in `coefficients/`. Their
decompressed unsigned big-endian values are compared against an independent
reconstruction using the entire pinned3297-entry coefficient array, not
only against hashes. With `rho=2^47` and `G_n=sum_{e=0}^{n-1}rho^e`,

```text
beta=rho^2011-1
K=rho^18+rho^1004+rho^2020+sum_e c_e*rho^(1005-e)
MC=beta-G_951-rho^960*G_26-rho^1004
MF_source=beta+8*G_917-4+(2^45-4)*rho^1005
          +rho^960*G_9+rho^987*G_8+rho^1004.
```

Here `c_e` are the complete doubled weights in the frozen
`padding-staircase-independent/coefficients.json`; all nonzero indices
in the sum satisfy `e<=1005`. The audit uses all3297 entries and pins
the corresponding native proof and certificate. It does not rerun the
machine decoder, native certifier, or old auditors as project code.

| Port | Bits | Raw bytes | Raw SHA-256 |
|---|---:|---:|---|
| beta | 94517 | 11815 | `a22ea3808ae016284c057d90f1bf2b76db1be2d34d11c0856f3315f6577d4b27` |
| K | 94941 | 11868 | `64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7` |
| MC | 94517 | 11815 | `2b5c9296e32616260e64a051c92892645b9aa1bf0bf4c0d931e464080702ca9f` |
| MF_source | 94518 | 11815 | `5c15fc24e4978b878ed531abf30b2dcfe255083372034612b759b65eee1f0c25` |

Run from the repository root:

```sh
python3 -B Computability/DiophantineConsistency/research/thirteen-lv-carrier122/audit.py
python3 -B -O Computability/DiophantineConsistency/research/thirteen-lv-carrier122/audit.py
```

The default is read-only and requires exact deterministic bytes for both
graphs and the certificate. `--write` materializes only the two graphs,
the four complete port files, and the certificate in this new directory.
Every check uses an explicit exception, so `-O` cannot disable it.
Graph mutations exercise wrong carrier inputs, missing LV/c-squared rows,
rational leaves, extra coordinates, wrong output, wrong residual sign,
and changed port metadata. Independent polynomial checks reject replacing
LV by V-squared and reversing the witness-map sign.

This finite packet is authored by `controller_certificate`, adapting its
previous corrected-strong auditor after full source rereading. The Lean
zero-set maps and ordinary proof are authored separately by
`circuit_reduction`. Independent root review is separate from either
author's checks. The maintained equation, PDF, accepted sources and Git
state are not changed by this packet.

## Frozen verification checkpoint

The first `--write`, normal, and optimized runs all passed. Normal and
optimized modes reproduced identical complete graph and certificate bytes.
All seventeen dependence witnesses for each profile already succeed with
the thirteen inputs initially1 and the selected input increased by1,
modulo1000003. This is exact evidence of dependence, not a search for zeros.
The copied gzip payloads total4230 bytes; their complete raw values total47313.

| Artifact | SHA-256 |
|---|---|
| audit.py | `38a8647f2f3851aa67756b6499af5c4c359a69b883358e12b6f4fbe368920ba2` |
| polynomial72.json | `2ac2f00f08146d61b8d98c15b3f844b0ae00330eba825f80629d0a1e48e27045` |
| polynomial.json | `b701b3c9e56f26069c69ed5ba495e2beae952d88d8c1fe2b94df0d88b1e3c09a` |
| CERTIFICATE.json | `3b4e66705173eac73939971d166b5db70be467eb85b2ef7d1dde232ed799d118` |
| PROOF.md | `0b4652adbdb5938ba52bf0865799acdc19dcbc13e23948ce16dc33c83cfd8386` |
| ThirteenLVCarrier.lean | `d64e31b377007ddd05964e29a1976c857d036d6eb919524df58c3bd8c237bd02` |
| ThirteenLVCarrierChecks.lean | `3a4301d7b4c72dbf52dc365521397219b929159a23657eaa63d6f9470ba51bdf` |

The finite author read the entire frozen predecessor auditor and both parent
graphs before adapting the code, read every new verifier line before running
it, and read both complete materialized schedules. The full ordinary proof
and Lean source/checks were read separately; this finite author did not run
Lean for this packet. The Lean author's own fresh checks and independent
root replay remain distinct evidence from these finite arithmetic checks.

# Thirteen positive variables, 73 operations, degree 126

This packet changes the strong factor of the accepted normalized thirteen-variable
polynomial. It preserves the entire strictly positive integer zero set at the
same coordinates. The new profile trades two extra integer operations for two
degrees: **13/73/126**, compared with 13/71/128. It does not dominate the latter,
claim novelty for the correction, or establish a minimum. The earlier
`ShortReducedStrong.lean` uses the same triangular correction in a different
fifteen-variable sum-of-squares finalizer.

`ThirteenCorrectedStrong.lean` proves the positive zero-set equivalence and
specializes it to the actual current2011 ports, obtaining
`no_current_positive_zero_iff_conZFC`. This is an external Lean theorem about the
actual `DiophantineConsistency.ConZFC` predicate. It is not an encoded derivation
inside ZFC. The complete arithmetic graph and its exact degree are independently
checked by the stdlib-only `audit.py`; exact degree126 is not asserted as a Lean
`totalDegree` theorem in this packet.

## Complete arithmetic formula

The independent positive integer coordinates, in order, are
`J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma`. The four fixed ports are
`beta,K,MC,MF_source`, with the source high mask already shifted once by beta.
Use the following complete abbreviations:

```text
b=beta*J, q=b+1, C=q-F-alpha
X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta
ell=E*k*Y, c=k*Y+eta
a=E+Y, H=4*a+3, Delta=a^2+H, D=X+a*c+gamma*H
R=(b*(q-F)+alpha)*(q^2-1)+(MC+q*MF_source)*J
tau=E*n+k-R
V=f^2*(c*T-R)-c, G=(K+w)*C-F
y=1+4*(b*(m-V^2*G)-G)
P=tau^2-ell*(ell+k), Q=D^2-Delta*c^2
U=Delta*(f^2-1)*(V^2-y^2)+y^2
Z=f^2-(b*i)^2*c^2*(Delta*c^2)
Zcorrected=f^2-(b*i)^2*c^2*(Delta*c^2+P-1)
p_corrected=P*Q*U*Zcorrected-1.
```

`polynomial.json` gives every one of the 73 paid binary operations. It retains
all 71 rows of the old schedule, inserts `residual_first=P-1` and
`corrected_Dc2=Dc2+residual_first`, and changes the second operand of
`intermediate=hi2*Dc2` to `corrected_Dc2`. The count is exactly
40 multiplications, 17 additions, and 16 subtractions. Every row, all thirteen
unknowns, and all four fixed integer ports are live. No division, rational leaf,
free extra norm, or additional witness is hidden in this count.

## Both zero-set directions

Let `A=(b*i*c)^2` and `p71=P*Q*U*Z-1`. The universal identity is

```text
Zcorrected=Z-A*(P-1),
p_corrected=p71-P*Q*U*A*(P-1).
```

These are different polynomials. On a positive assignment with beta>0, the
actual first norm has the form
`tau^2-(E*Y)*(E*Y+1)*k^2`. Its consecutive-product parameter is at least2;
`ConsecutivePell.norm_ne_neg_one` therefore excludes P=-1 without any equation
premise. If either product polynomial vanishes, P is an integer unit and hence
P=1. This deduction is made separately for the two polynomials. The correction
then vanishes, proving their zeros agree by the identity map on all thirteen
coordinates. No positivity of tau, rank, C, or y, and no preselected Pell norm,
native witness, mask or calibration is assumed.

The formal endpoints are `positive_zero_iff`,
`positive_polynomial_zero_iff`, `exists_positive_zero_iff`, and
`no_current_positive_zero_iff_conZFC`. The last uses the already accepted
`CurrentPositiveZero2011.no_thirteen_positive_zero_iff_conZFC.2.2` and the exact
current `CurrentMasks2011.ports CurrentKernel2011.K` tuple.

## Exact degree, with all cancellation accounted for

The strong coefficient satisfies the ring identity

```text
Delta*c^2+P-1
 = ((2*X+1)*Y^2+H)*c^2
   +E^2*eta*(2*k*Y+eta)-E*k^2*Y+tau^2-1.
```

The audit expands the entire main norm Q (323 terms) and corrected coefficient
(353 terms). It independently checks this identity and the main-norm
cancellation. It then propagates all homogeneous leaders through every literal
gate. The only complete leading cancellations are `N1` and `corrected_Dc2`;
both are resolved by the full expansions. No truncation substitutes for either
cancellation check.

With `q0=beta*J`, `k0=eta+zeta`, and `C0=q0-F-alpha`, the exact factor leaders are:

| Factor | Degree | Complete factored leader |
|---|---:|---|
| P | 22 | `-w^2*s^4*k0^2*q0^14` |
| Q | 18 | `8*gamma*w^2*s^3*k0*q0^11` |
| U | 52 | `-16*q0^22*k0^4*s^6*w^4*f^10*T^4*C0^2` |
| Zcorrected | 34 | `-2*i^2*w*s^6*k0^4*q0^21` |

Their product has the complete degree126 leader
`-256*q0^68*gamma*i^2*k0^11*w^9*s^19*f^10*T^4*C0^2`.
The certificate stores all72 expanded terms. The monomial
`J^70*gamma*i^2*eta^11*w^9*s^19*f^10*T^4` has coefficient
`-256*beta^70`, nonzero at the actual positive beta. Thus the degree bound is
attained, including after specialization of all four actual fixed ports.

## Whole current constants and reproducibility

The original normalized graph was stored with2471 ports. Its operation schedule
is reused universally, but this packet explicitly rebinds all four ports to the
accepted2011 candidate. It does not assert that the two specialized polynomials
are equal. The audit reads all3297 pinned coefficients, rebuilds each complete
current integer, and compares it byte-for-byte with the retained gzip port
files. It does not import or rerun the old native certifier or machine decoder.

| Port | Bits | Raw bytes | Raw SHA256 |
|---|---:|---:|---|
| beta | 94517 | 11815 | a22ea3808ae016284c057d90f1bf2b76db1be2d34d11c0856f3315f6577d4b27 |
| K | 94941 | 11868 | 64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7 |
| MC | 94517 | 11815 | 2b5c9296e32616260e64a051c92892645b9aa1bf0bf4c0d931e464080702ca9f |
| MF_source | 94518 | 11815 | 5c15fc24e4978b878ed531abf30b2dcfe255083372034612b759b65eee1f0c25 |

Total raw constant size is47313 bytes. The graph references the complete
materialized files; it does not replace them with hashes or omit fixed data.
The corrected scalar formula changes none of these constants.

From the repository root, run:

```bash
python Computability/DiophantineConsistency/research/thirteen-corrected-strong126/audit.py
python -O Computability/DiophantineConsistency/research/thirteen-corrected-strong126/audit.py
```

Default execution is read-only and requires exact graph and certificate byte
equality. `--write` materializes only this packet's graph/certificate. Every
gate uses an explicit exception check, so optimization does not disable checks.
Negative controls cover missing c-squared, wrong P-residual sign, wrong output
constant, rational leaves, extra unused variables, and changed port metadata;
the wrong-sign polynomial is also independently rejected algebraically.

Frozen source hashes:

- Lean main: `57729066535acf1909d30ea5de0b4b78e1ac6f1ae11a126e1c2c4526cc546efe`.
- Lean checks: `481f520df1e3ff05efc7869e9c118596e3b9967cac097527c1a7de77ddfe109f`.
- audit: `d185e03bff041eb2d581c9f0f49d8d157b0ea275be3d4d45c9c0cb9498892f6d`.
- graph: `e6deeec7f6a298f47e4247c5868e39d7d9caa6431b738ef6b99e822e7183a358`.
- certificate: `7d7b6230409776e0fc79a627cc86665f8fd45aca8d94974a6eb4204172e585a5`.

Both final Lean files freshly passed bounded direct compilation. Eleven axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound` (subsets
vary). Write, normal and optimized Python runs passed. These are author checks;
independent review is a separate receipt. No maintained equation, page, source
constant, or accepted dependency was changed.

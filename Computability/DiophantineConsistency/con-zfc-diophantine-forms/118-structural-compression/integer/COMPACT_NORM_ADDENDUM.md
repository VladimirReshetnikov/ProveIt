# Preferred compact variants: 126, 138 and 137 operations

The preferred evaluators supersede the operation counts in PROOF.md by one
operation each, while keeping the same polynomials and every proof there.

| Literal evaluator | Integer unknowns | Exact degree | Parent operations | Preferred operations |
|---|---:|---:|---:|---:|
| compact_trace13.json | 13 | 536 | 135 | **126** |
| compact_scalar12_rational.json | 12 | 1200 | 145 | **138** |
| compact_scalar12_integral.json | 12 | 1456 | 141 | **137** |

During independent review of the positive-domain companion we found a
retained **28-operation** four-root norm schedule, one operation cheaper
than the fully symmetric 29-operation identity developed in PROOF.md.
It appears in Section 1 of the pinned source

    candidates/ten-positive-zero-offset/source/ORIGINAL_PROOF.md

at commit84e16e43092614bae262ca59651cb9d77e31a255, Git blob
88ac327ed4dde68ab30c094d531f9faca28881bc. Its exact source bytes and
license are retained. We credit that schedule to the existing repository;
the contribution here is the complete adapter to the current integer
circuits, including denominator clearing and common-scale sharing.
The earlier symmetric circuits remain useful independent alternatives and
are verified alongside these preferred circuits.

## The compact schedule

For supplied z=x^2 and four radicands a,b,c,d, define

    sigma1=a+b+c,
    sigma2=ab+(a+b)c,
    sigma3=abc,
    U=z+d,
    Po=U-sigma1,
    Pe=Po^2+4(zd-sigma2),
    Ge=Pe^2+16(zd*Po^2-4*sigma3*U),
    Go=Pe*Po-16*sigma3,
    Nc(z;a,b,c,d)=Ge^2-64zd*Go^2.

Share a+b, ab, Po^2 and zd. The first three symmetric quantities take
six operations, U and Po take two, Po^2 and zd take two, Pe takes three,
Ge takes seven, Go takes three, and the output takes five: total **28**.
All constant multiplications are included.

This Nc is exactly the same norm N4 as in PROOF.md. To see it without
large expansion, start with the three-root identity

    N3(w)=[(w-sigma1)^2-4sigma2]^2-64sigma3*w.

In adjoining the fourth root, w=(x +/- sqrt(d))^2=U +/- r with
r^2=4zd. The first bracket becomes Pe +/- 2r*Po. Substitution and
collection give the two conjugate values Ge +/- 4r*Go. Their product is
Ge^2-16r^2*Go^2=Ge^2-64zd*Go^2. Thus Nc and the symmetric expression
are the same universal integer polynomial, including every degenerate
specialization. No root rationality, nonzero condition or inequality is
needed for this identity.

## Substitution into the complete equations

Use exactly the complete abbreviations, domains and fixed coefficients in
PROOF.md and its copied scalar-carrier proofs. The preferred equations are

    Nc(delta*Z^2; delta*U^2*Df,delta*U^2*Dt,
                     delta*U^2*Ag,U^2*Cy)=0,

    Nc(delta*Z^2; 9delta*S^2*Df,81delta*S^2*Dt,
                     729delta*S^2*Dg,S^2*Cy)=0,

    Nc(Z^2; 9S^2*Df,81S^2*Dt,729S^2*Dg,S^2*delta*Cy)=0,

respectively. In these displays the U in the first equation is the original
trace carrier scale; the compact norm's internal U is merely a local name
and should be renamed if expanding both displays together. Each JSON uses
unique node indices, so there is no scope ambiguity in the literal output.

For the first two equations, share delta*U^2 or delta*S^2 once before
forming the three corresponding radicands. The three outputs are
pointwise-identical to the same pinned parents as before. Exact degrees
536,1200,1456 and all parent coefficients therefore transfer unchanged.
Their operation breakdowns are respectively

- 73 multiplications,27 additions,26 subtractions;
- 86 multiplications,27 additions,25 subtractions;
- 85 multiplications,27 additions,25 subtractions.

## Independent verification and limits

Run `python3 build_compact_norms.py` to reproduce these three DAGs and
`python3 verify_symmetric_norms.py` to verify all six delivered variants.
The verifier imports neither builder. For each preferred variant it
compares every coefficient of the complete norm tail over a free
seven-variable integer polynomial ring against the actual parent tail,
in addition to exact front-prefix, liveness, count, source and coefficient
checks. All495 tail coefficients agree. Normal and optimized Python both
pass. The actual-parent coefficient diagnostics are supplementary; the
universal identities are proved exactly.

These are circuit savings for the existing integer polynomials. They do
not change the inherited calibration proof boundary, improve the number
of variables, or assert a globally minimal norm circuit.

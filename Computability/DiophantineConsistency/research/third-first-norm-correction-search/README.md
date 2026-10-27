# Bounded third-correction search: no improved candidate yet

This checkpoint explores the frozen 13/92/90 and 13/97/88 equations. It
produces no equation, Lean module, new coefficient tuple, or global lower
bound. Existing packets and displays are unchanged. All scripts here are
new standard-library-only programs, fully read before their execution;
the parent certificate is read as inert JSON, not imported as code.

## A precise bounded-degree obstruction

Use the complete definitions of the parent
[`PROOF.md`](../thirteen-second-first-norm-corrections/PROOF.md). In this
paragraph B=beta*J, k=eta+zeta, C0=B-F-alpha. The exact highest homogeneous
parts of the first and second norms are

```
P22 = -B^14 k^2 s^4 w^2,
Q18 =  8 gamma B^11 k s^3 w^2.
```

The complete degree44 leader of U88 has302 terms. Its entire component
linear in w is the following50-term polynomial:

```
-32 B^21 k^4 f^6 T^4 s^6 w (K0*C0-F)^2.
```

`obstruction.py` reconstructs that factored expression independently with
small sparse arithmetic and compares all50 coefficients to the pinned
complete leader. The unknown monomial
`J^21 alpha^2 f^6 T^4 s^6 w zeta^4` has exactly one symbolic-port
contribution, `-32 beta^21 K0^2`. It remains nonzero at the unchanged
current positive ports.

Consequently no additional correction
`A*(P-1)+B1*(Q-1)` with deg(A)<=22 and deg(B1)<=26 can lower U88 below
degree44: its degree44 component is divisible by w^2, whereas U88 has the
displayed nonzero w-linear component. Degrees count only the thirteen
unknowns; the four fixed ports have degree0. This argument does not apply
to higher-degree coefficients whose leading products cancel each other,
to a Z-1 correction, to a different norm construction, or to eliminating
a variable. It is not a global degree-minimality claim.

For arbitrary A and B1, using both corrections would still have a
noncircular positive-zero proof if a useful polynomial were found.
Either sphere `(P*Q)^2+Unew^2+Z^2=3` first forces P*Q to be an integer
unit. The accepted positive-domain exclusions P!=-1 and Q!=-1 then force
P=Q=1, before either correction is removed. Thus no sign condition on the
corrected auxiliary is needed. The obstruction concerns degree, not that
zero-set argument.

## Fully charged, deliberately incomplete regrouping

The searches use independent cuts `Zc=b*G,T,V,F2=f^2,h=f^2-1,C,R,X`.
Here Zc is only a search abbreviation and is not the strong norm Z.
Parent V^2 is an already paid leaf. Every added binary multiplication,
addition and subtraction is charged, including multiplication by constants;
constructing Zc costs one. Identical AST subexpressions are shared. The
reported total is the retained75-row parent plus the coefficient cost and
three rows for P-1, its product with the coefficient, and subtraction from U.

The complete small cut polynomials checked are

```
A90 = 16 Zc^2 T^2 V^2 h
      +32 Zc T^2 V^2 F2 C -32 Zc^2 T^2 V F2^2 R,
A88 = 16 Zc^2 T^2 V^2 h
      +64 Zc T^2 V^2 F2 C -32 T^2 V^2 F2 X C^2
      -32 Zc^2 T^2 V F2^2 R.
```

| Run | Polynomial subproblems | Best full paid count found | Limitation/result |
|---|---:|---:|---|
| `regroup.py` |391|98 for A88|Missed reversed subtraction orientation. Preserved.|
| `regroup2.py` |391|97 for A88|Recovers the known schedule; no improvement.|
| `regroup90.py` |115|93 for A90|Maximal-common-factor restriction misses the known92. Preserved.|
| `partial_regroup.py 90` |1326|92|Allows every common monomial divisor; recovers known92.|
| `partial_regroup.py 88` |2412|97|Same expanded search; recovers known97.|

Every retained AST is evaluated as a complete polynomial and checked equal
to its target. The final searches enumerate common monomial divisors,
coefficient gcd factoring, additive partitions, both subtraction
orientations, and variable Horner splits. They retain only12 candidates at
each subproblem and use a fixed monomial multiplication order. They do not
exploit every identity among parent cuts or every already computed parent
gate. Hence even the recovered92/97 counts are search results, not operation
lower bounds. In particular the preserved misses show why such a claim
would be unjustified.

## Execution and provenance

The parent complete certificate is pinned to
`b05205f7a5e40dcddf78d77fd6a170a79c4e0df45c3ba23c9bc8b68c3f44d3e5`.
The search caps are30,000 subproblems,45 seconds elapsed,60 seconds CPU,
and1.5GiB address space; the small obstruction check uses20 seconds and
512MiB. Every run terminated with exit0, well below its cap. No large full
polynomial expansion or compiler was run. Disk space remained above512MiB.

The final obstruction and both partial-factor searches were also run with
`python3 -O`; their JSON outputs are byte-identical to normal execution.
All captured error logs are empty. Original incomplete attempts and their
outputs remain present. The exact file inventory and execution scopes are
recorded in `CHECKPOINT.json`; relevant pins are:

| File | SHA-256 |
|---|---|
| `obstruction.py` |`b501ee4b661a41a6df59c53bf61e17f877756780d32ac466e233b44f6305386b`|
| `OBSTRUCTION.json` |`044afa962a67fce10b267b80a01d42a94a3c08122ece1d03217739e0b6dbc356`|
| `partial_regroup.py` |`ce385f175c8f95bc8acad702eef7ccf2eeb03ef1b62dfb1988204fcdaac6d160`|
| `PARTIAL90.json` |`dd9afb5034dffbf2fea70d0377aeb52a0ac9251d5be769c8cdcc18d7f4c6282a`|
| `PARTIAL88.json` |`fd89aa047af32b4de61241ecfdcfcdfdf82f48e20260955cb98c501b7349a796`|

No new candidate is proposed at this checkpoint. A separate subsequent
probe may examine higher-degree syzygies; that possibility is expressly
outside the bounded obstruction above.

# Current2011 integer-leaf 66-operation, degree-138 candidate

This candidate keeps the exact current2011 four **integer** ports and 14
strictly positive integer coordinates of the maintained 65/150 graph. It
has 66 live binary operations (38 multiplications, 16 additions, 12
subtractions) and exact total degree 138. It trades one extra integer-leaf
operation for reducing degree by 12; it does not replace the maintained
equation/PDF or establish a global minimum.

The graph retains the parent's first 51 rows through `V`. With `c2=c²`
and `Dc2=Delta*c²` already available, its new shared tail computes

```
i2 = i*i
i2Dc2 = i2*Dc2
strongTerm = i2Dc2*c2
Z = f² - strongTerm
auxCoefficient = Delta*strongTerm
Na = auxCoefficient*(V²-y²) + y²
new66 = N0*N1*Na*Nt*Z - 1.
```

Here `strongTerm = Delta*(i*c²)²`, and the parent's auxiliary square
`(i*Delta*c²)²` is exactly `Delta*strongTerm`. Therefore the **entire**
parent 65-row polynomial equals `Delta * new66` as a polynomial over every
commutative ring. The checker verifies that ring identity on independent
prefix symbols and verifies the exact shared prefix and complete new tail.
For positive beta and positive witnesses, `Delta=(a+2)²-1>0`, so the two
integer equations have exactly the same positive zeros with the identity
witness map. This argument uses no division, sign choice, Pell norm or
canonical-witness restriction.

The complete degree-138 leading form is computed from the exact component
leaders in the independently reproduced historical 67/106 certificate.
The checker confirms the 67/106 graph has the identical prefix and relevant
strong/square-gap cuts. The new auxiliary factor has degree 62; the five
factor degrees are 22, 18, 62, 2 and 34. The resulting 56-term leader
contains the unique fixed-port monomial coefficient `-8*beta^80` on
`J^80*T^2*eta^13*f^4*gamma*i^4*s^23*w^10*z`; actual beta is positive, so
specializing the ports cannot cancel it. This establishes exact degree 138
as an external finite check, not a Lean `totalDegree` theorem.

The underlying parent no-zero/iPRA endpoint is separately checked, but an
all-model zero bridge and internal iPRA transfer **for this new syntax are
not yet checked**. The source, graph, exact ring identity, degree and port
bytes are independently reviewable; no Lean check is claimed here.

From the repository root, run the read-only checker:

```
python3 -I -S -B Computability/DiophantineConsistency/research/current2011-unscaled66/check.py
```

The checker exited 0 without invoking Lean. `build.py` refuses to overwrite
an existing graph. It reads the pinned current2011 parent; the original
four integer port files total 47,313 raw bytes and are authenticated by
their parent metadata.

| Artifact | SHA-256 |
| --- | --- |
| `build.py` | `3787bf64aa76cc1f20fb9d4581d79509211658376d26e4d56a4c1f405050af68` |
| `polynomial.json` | `bf9e05905fe84f74edade75ba7d373bd6955aa035867af89a6026d9a21719e75` |
| `check.py` | `49be2acadbf63e44e04bbe75f0d3dc8c3e566fa57ef529ae0d5397f8cc5c94f5` |
| `result.json` | `4712b4c1e5213cff886d96f48e08cd68cee59055029fa8fb4e18d0b2f10c1d52` |
| `outer-terminal.json` | `ede299f578e43719e4e673307fd95b7626a05298b8e96e717f25746ec03234f3` |

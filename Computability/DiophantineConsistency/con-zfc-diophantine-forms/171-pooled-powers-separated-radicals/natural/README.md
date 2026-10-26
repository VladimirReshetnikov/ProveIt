# Four fewer natural coordinates: 202-variable quartic

All variables independently range over **N={0,1,2,...}**. Every delivered
polynomial is the sum of the literal squared quadratic residuals in its
`equation.json`; `expanded_polynomial.json` contains every coefficient.

| Selected endpoint | Variables | Rows | Monomials | Height |
|---|---:|---:|---:|---:|
| `natural202` | **202** | 154 | 9,818 | 239,204,765 |
| `natural202_lowheight` | **202** | 154 | 12,706 | **31,145,294** |
| `natural203` | 203 | 155 | 6,834 | 228,943,870 |
| `natural204` | 204 | 156 | 6,756 | 225,656,347 |

The inherited principal endpoint had 206 variables, 158 rows, 8,210 monomials
and height 130,686,376. The dimension reduction is genuine; the table makes
the competing support/height costs explicit. No global optimality is claimed.

## New mathematics

1. Share three shifted quadratic syntax wires with one natural gate; share
   one affine factorial multiple: three coordinates saved.
2. Replace a modulus and three q-power quotients by a three-coordinate
   **natural** aggregate: one more coordinate saved.
3. Double the existing lower Pell frame without adding a coordinate. The
   additive frame budget controls cleared inverse-power errors and repairs
   the predecessor orientation lost by deleting a power-output row.

`PROOF.md` gives the complete ordinary argument, including sign recovery,
noncircular power authentication, natural old-quotient restoration, cofinal
completeness and the inherited calibration boundary. `report_section.tex`
is the typeset report section. The full parent is retained under `inherited/`.

Relative to that explicit C222/ZF/ZFC calibration, a natural zero exists
exactly when the fixed effective ZFC presentation has a finite syntactic
refutation. Thus ZFC proves the no-natural-zero sentence equivalent to
`Con(ZFC)`. This is not a consistency proof or a new complete proof-assistant
certificate.

## Reproduce

Python 3.10+ and its standard library suffice, offline:

```bash
python3 -B verify.py --rebuild
python3 -B -O verify.py --rebuild
```

The verifier checks source pins; all source substitutions and deletions;
complete quadratic rows and quartic coefficients; the formal error identity;
literal additive frame bounds; retained predecessor incidences; natural
restoration identities; reversible integer row shears; and printed TeX
parsed back to its exact polynomials. It also replays the complete inherited
finite verification. These checks do not prove an unbounded semantic theorem.

For a smaller new-stage audit: `python3 -B check.py --rebuild`.
To rebuild all ten endpoint coefficient/certificate directories elsewhere:
`python3 -B build.py --output /tmp/natural21-rebuild`.

Every selected directory also contains `residuals.txt`, `residuals.tex`,
`variables.tsv`, `operations.json`, and `row_basis_certificate.json`.
The intermediate directories record the semantic transformation certificates
before optional row shears. All row shears have explicit inverse operations
and leave the coordinates and natural domains unchanged.

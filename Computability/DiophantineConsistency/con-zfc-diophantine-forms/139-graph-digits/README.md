# Smaller explicit Diophantine equations for Con(ZFC)

Prepared for Vladimir Reshetnikov and the ProveIt project, 24 October 2026.

This package supplies literal equations, ordinary mathematical proofs,
reconstruction programs and separately written exact checkers. Each equation,
in its stated domain, has a zero if and only if there is a finite ZFC
refutation. The equivalence is provable in ZFC by composing the new reductions
with the explicitly identified inherited ProveIt calibration.

Start with **report.pdf**, whose editable source is **report.tex**. The report
prints all 175 residuals of the principal natural equation and the complete
compact coefficient recipe and register program. The graph expansions and all
other literal equations are in the component directories.

## Results

Here N means {0,1,2,...}; positive integers and unrestricted integers are
different witness domains. Height is the largest absolute collected coefficient.

| Artifact | Domain | Variables | Degree | Collected monomials | Height |
| --- | --- | ---: | ---: | ---: | ---: |
| `graph/equations/unit951` | Z | 951 | 4 | 56,916 | 1 |
| `graph/equations/unit984` | Z | 984 | 4 | 30,076 | 1 |
| `graph/equations/unit1050` | Z | 1,050 | 4 | 21,766 | 1 |
| `graph/equations/matched1137` | Z | 1,137 | 4 | 23,105 | 1 |
| `direct/equations/natural226` | N | 226 | 4 | 10,314 | 87,839,583 |
| `direct/equations/natural227` | N | 227 | 4 | 7,905 | 87,839,583 |

Every graph polynomial has constant one, every nonzero coefficient is +1 or
-1, and every declared variable occurs. `unit984` is a balanced starting
point; `unit951` has the fewest variables within this delivered height-one
set and `unit1050` has its fewest monomials.

The compact directory adds complete polynomials in **ten strictly positive
integers**, with **87 binary operations / degree 323** and **88 operations /
degree 318**. Their four large fixed coefficients are present as compressed
integer payloads and have a complete finite reconstruction. These four numbers
are constants, not additional unknowns. The support is not expanded.

`direct/equations/integer678.json` gives the unrestricted-integer degree-eight
companion of natural226 using the surjective substitution
`z = a*a + b*b + c*(c+1)` in each natural coordinate.

## Main new ideas

1. **Check the products actually present in an incidence energy.** A global
   four-cycle-free factor condition forbids harmless coincidences. We instead
   collect every coefficient of the actual graph energy, pair opposite source
   occurrences, and identify compatible copies of the same logical variable.
   A certificate checks every proposed identification and the integral tree
   flow needed for the reverse map.
2. **Replace two-copy equality witnesses by a four-term quartic.**
   `a^4+b^4-a^3*b-a*b^3 = (a-b)^2*(a^2+a*b+b^2)` is nonnegative and vanishes
   precisely when `a=b`. The replacement is accepted only when the entire
   collected polynomial still has height one. The report proves a narrow
   two-variable optimality statement for this gadget.
3. **Pool actual low-digit budgets.** Eleven modular remainder bounds fall
   into four common-denominator groups. Their canonical low binomial digits
   have enough spare radix capacity to share a bound. A natural fused Pell
   row simultaneously bounds and authenticates the required indices. The
   unbounded estimates and witness order are proved, not inferred from tests.
4. **Center the compact Pell carrier.** Two polynomial shears lower the exact
   degree of the 85-operation parent. Positivity is proved in both directions,
   including both decoded radical-sign branches; a formal substitution alone
   would not suffice for the strictly positive domain.

On exactly the signed442 source used by package 127, the graph compiler reduces
2,215 variables / 30,468 terms to 1,137 / 23,105. Thus the new compiler itself
saves 48.7% of the variables and 24.2% of the terms. The first three graph
profiles use the newer signed324 source. Natural226 improves the corresponding
natural233 parent in variables, residual count, support and height. Natural227
uses fewer variables and terms than natural234 but slightly increases height.
The compact equations are new tradeoff points between existing 85/328 and
89/288 equations, not simultaneous improvements over both.

## Verify and reconstruct

Python 3.12.14 is the tested runtime. All finite mathematical checks use the
standard library and require no network access. From this directory:

```sh
python3 -B verify_all.py --rebuild
python3 -B -O verify_all.py
```

The first command checks every component, independently reconstructs the
changed direct rows and compact algebra, rebinds the printed appendices to the
literal JSON, and rebuilds mathematical data in temporary directories or memory.
The second exercises the checks with Python assertions disabled. Component
checks use explicit exceptions for required validations. Mutation controls
must be rejected. See `verification/` for the delivered run receipts.

If present, `MANIFEST.sha256` is checked before running any component. It seals
the release bytes; it is neither an external signature nor a proof certificate.
Extra local build files do not invalidate it. To inspect only this seal:

```sh
python3 -B verify_all.py --manifest-only
```

To keep a fresh receipt without modifying this sealed release:

```sh
python3 -B verify_all.py --rebuild --receipt /tmp/conzfc-verification.json
```

The graph and direct rebuilds reproduce their mathematical JSON byte for byte.
Compact rebuilds compare every circuit field other than compression hashes,
and compare all uncompressed coefficient bytes exactly; gzip headers or streams
can vary across Python/zlib versions. The receipts also report whether the
delivered compressed bytes and circuit JSON were reproduced exactly.

To rebuild the report using a normal pdfLaTeX installation:

```sh
./build_report.sh
```

This regenerates `report_inputs/` directly from the equations and compiles the
report three times. A newly built PDF may have different metadata or font bytes;
this does not change an equation. Preserve the delivered directory if its
release manifest is to remain valid.

## Proof scope and provenance

The comparison and inherited sources are pinned to ProveIt commit
`1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`, including the recently integrated
packages 127–133. `PROVENANCE.json` and the component source ledgers identify
the original files by Git blob and SHA-256 hashes.

The graph transformation proves an explicit bijection of integer zero sets for
any correctly checked source. The direct arithmetic reductions prove
existential equivalence by canonical witness reconstruction. The compact
shears give bijections of the respective positive zero sets. The endpoint
linking the sources to finite refutations is inherited and explicitly cited.

No global simplicity minimum, proof of Con(ZFC), worldwide priority claim,
new end-to-end proof-assistant development, or external human review is claimed.
The immediate logical interface files are included for inspection; their full
transitive formal dependency closures were not rebuilt. These are ordinary
proofs formalizable in ZFC, accompanied by exact finite artifact checks.

## Layout and integration

- `report.tex`, `report.pdf`, `report_inputs/`: main exposition and literal appendices.
- `graph/`: four complete height-one quartics, certificates, builders and reviews.
- `direct/`: natural226/227, integer678, arithmetic proofs and exact checkers.
- `compact/`: 87/323 and 88/318 circuits, all four coefficients and proofs.
- `verify_all.py`: one entry point for the finite release checks.
- `verification/`: fresh normal/optimized receipts and PDF review record.
- `PROVENANCE.json`, `NOTICE.md`, `LICENSE`, `MANIFEST.sha256`: source and release metadata.

The folder can be copied into a new ProveIt contribution directory without
renaming an existing numbered package. Verification leaves the delivered
equations unchanged; the report rebuild regenerates the listed derived files.

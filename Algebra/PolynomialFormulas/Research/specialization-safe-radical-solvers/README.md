# Specialization-Safe Radical Solvers

**Exact Bad Characteristics for Subset-Sum Resolvents, a Fourier–Kummer Atlas,
and a Global Obstruction**

Research prepared for Vladimir Reshetnikov, September 2026.

## Read the article

- `article.pdf`: compiled 29-page research article with full arguments and bibliography.
- `article.tex`: self-contained LaTeX source; no separate bibliography or figure files required.

Repository snapshot inspected:
`VladimirReshetnikov/ProveIt` at
`e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9`.

The starting point is the polynomial-formula project, especially its existing
arbitrary-degree Fourier reconstruction and its documented branch-sensitive
invariant-recovery boundary. This archive does not modify the repository.

## Main mathematical results

Theorem 3.3 gives an exact cyclotomic-resultant criterion for characteristics
in which equal-cardinality subset sums of irreducible prime-degree roots can
collide. Theorem 4.1 evaluates it completely for quintic pairs and septic pairs
and triples: the bad characteristics are respectively `{5}`, `{2,7}`, and
`{2,7,29}`. All listed characteristics have separable irreducible witnesses.

Theorem 5.1 gives the exact characteristic-29 resolvent of `X^7-t`:

    (Y^7-12t)^2 (Y^7-t) (Y^7-17t) (Y^7-28t).

Theorem 11.1 strengthens this to a complete classification: in characteristic
29, a monic irreducible septic has colliding triple sums exactly when it is
`(X-eta)^7-b`. Such a polynomial has cyclic Galois group. Noncyclic septics
therefore remain safe in that characteristic.

Theorem 11.2 classifies characteristic-two collisions: pair collisions and
triple collisions are equivalent, and occur exactly for translated
polynomials `Z^7+a Z^3+b Z+d`, with `d != 0`. Their root configuration is an
affine translate of a three-dimensional F_2-space with zero removed.
The group GL_3(F_2), of order 168 and nonsolvable, is realizable.

Theorem 7.2 constructs separating subset invariants in every characteristic
with a finite hitting-set bound (1191 distinct parameters for septic triples).
Theorem 8.1 reconstructs the entire root tuple from one coherent p-th radical
on each nonzero Fourier chart. Theorem 10.1 realizes every nonempty Fourier
support using irreducible rational polynomials with full affine Galois group.
Theorem 12.3 computes the Picard group of the cyclic distinct-root
configuration quotient as Z/pZ; Theorem 12.1 rules out a single global regular
Kummer coordinate.

The article includes a concrete repository integration plan and nine proposed
follow-on research questions.

## What is and is not claimed

The classical Fourier, Galois, resultant, additive-polynomial, and descent
frameworks are not claimed as new. The classifications, examples, and
synthesis are proved in the article; priority over the entire literature has
not been established. The published-paper comparison is deliberately narrow:
repeated factors invalidate an unrestricted *distinct-factor* interpretation,
not every assertion about radical solvability in that paper.

No new Lean or Rocq proof was compiled. Written proofs establish the general
theorems. Exact finite calculations support the small-degree norm tables and
examples. The executable checks are not a substitute for a proof-assistant
kernel, peer review, or a full dependency audit of the existing repository.
The one-radical chart theorem assumes the intermediate-field invariant data;
a fast coefficient-only solver computing all those data is a further task.

## Reproduce the exact checks

Python 3.10 or later is required. The recorded run used Python 3.13.5 and
SymPy 1.14.0. Do not run Python with optimization (`-O`): assertions are part
of the checks, and both scripts reject optimized mode.

```sh
python -m pip install -r requirements.txt
python verify_results.py --out certificates
python audit_certificates.py \
  --cert certificates/cyclotomic_norm_certificates.json \
  --out certificates/independent_audit_report.json
```

`verify_results.py` checks:

- 850 exact cyclotomic resultants and 29 independent integer determinants;
- four finite-field witness families and the repaired characteristic-29 vectors;
- all 78 nonempty supports in degrees five and seven, including 224 pivot
  charts and 10,208 reconstructed root entries across every branch;
- six exact worked minimal polynomials, four affine septic factor patterns,
  and 1,400 finite-field character-root patterns used in the rigidity analysis.

The independent `audit_certificates.py` uses **only the Python standard
library**. It regenerates the affine orbits and multiplication matrices,
checks determinants by fraction-free Bareiss elimination, verifies complete
coverage of the 850 pairs, and checks the resulting exceptional prime sets.
It does not trust the claimed matrices, orbit sizes, or norms in the JSON file.

The JSON and CSV files in `certificates/` are machine-readable inputs and
recorded outputs. They include all 29 multiplication matrices, orbit
representatives and sizes, finite-field coefficients, and passing reports.

## Compile the PDF

A normal TeX Live installation with the packages used by the source suffices.
The document uses embedded Latin Modern fonts; no font files are distributed.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Repeated passes resolve the table of contents, theorem references, and
bibliographic links. The supplied PDF was compiled and rendered for visual
inspection. Its mathematical notation and tables are vector text, not images.

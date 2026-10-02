# Arithmetic van Kampen Certificates

**Quartic equations, exact filling area, and optimal proof-DAG compression**

Research report prepared for Vladimir Reshetnikov, October 2, 2026.

## Start here

Read `arithmetic_van_kampen.pdf`. Its editable source is the self-contained
`arithmetic_van_kampen.tex` (bibliography included; no separate BibTeX run).

The main results are the fixed-itinerary compiler (8m−4 integer witnesses),
the all-label area-budget compiler ((2s+13)m−4 witnesses for s relators),
the proof-DAG compiler, and the exact k+ell product-gate optimum for the
boundary [a^(2^k), b^(2^ell)] in <a,b | [a,b]>. The last construction has
expanded relator area 2^(k+ell) but uses 8(k+ell)−4 arithmetic witnesses when
k+ell >= 1. The leaf-only case uses none.

All polynomial degrees are **at most four**. The counts refer to these
literal compilers, not to a minimum over all Diophantine representations.
The area or circuit shape is external compiler data: this is **not** one
fixed-arity polynomial with an unbounded number of quantified variables.

## Files

- `arithmetic_van_kampen.pdf`: complete report with proofs and research agenda.
- `arithmetic_van_kampen.tex`: editable LaTeX source, including references.
- `code/van_kampen.py`: exact matrix routines, Sanov decoder, symbolic budget,
  itinerary, and generic DAG compilers, and optimal dyadic grid construction.
- `code/verify.py`: deterministic exact-arithmetic tests and negative cases.
- `examples/commutator_budget_1.json`: complete sparse one-budget compiler
  with 11 existential integer variables and 13 quadratic residuals.
- `examples/grid_1_1.json`: complete sparse shared grid compiler with 12
  variables and 16 quadratic residuals; output boundary has area four.
- `examples/grid_1_1_witness.json`: all boundary and auxiliary integer values
  of a satisfying assignment for the grid example.
- `verification/receipt.json`: actual test result and exact test counts.
- `verification/render_check.json`: PDF production and inspection checks.
- `SOURCES.md`: dependency, provenance, and novelty boundary.
- `SHA256SUMS.txt`: integrity hashes of the other package files.

## Reproduce the mathematics-related tests

Python 3.10 or later is required (tested with 3.13.5).

```sh
python -m pip install -r requirements.txt
python code/verify.py --receipt verification/receipt.json
```

The main test run checks 13,121 reduced words, all 83,521 chart tuples in
[-8,8]^4 (417 are integer points of the chart), 3,615 valid area certificates,
10,845 corrupted certificates, 441 dyadic grid circuits, symbolic ledgers
and positive zeros, and a large grid with expanded area 2^200. See the
receipt for the full ledger. No floating-point tolerances are used.

## Export a polynomial

```sh
python code/van_kampen.py budget 1 --relator abAB \
  --output examples/commutator_budget_1.json
python code/van_kampen.py grid 1 1 --output examples/grid_1_1.json
```

Words use a,A,b,B, where uppercase denotes an inverse. JSON coefficients
are exact integers. Each residual is a list of pairs `[exponent_vector,
coefficient]`; exponent-vector order is `parameters + variables`. The final
polynomial is exactly the sum of the squares of every listed residual.
Matrix entry names in JSON use zero-based indices; the article uses the usual one-based mathematical indices. All parameters and witnesses are integers. There is no hidden matrix inverse,
variable exponentiation, or solver call in the specification.

`compile_itinerary([...])` and `compile_dag(nodes, relators)` are available
through the Python API. The latter validates topological order, leaf labels,
reachability, and membership of fixed conjugating matrices in the Sanov group.
No addition-chain optimizer or general Diophantine solver is implemented.

## Build the PDF

A normal TeX Live or MiKTeX installation with pdfLaTeX and the packages listed
in the source is sufficient. No custom fonts or external images are needed.

```sh
pdflatex -interaction=nonstopmode -halt-on-error arithmetic_van_kampen.tex
pdflatex -interaction=nonstopmode -halt-on-error arithmetic_van_kampen.tex
pdflatex -interaction=nonstopmode -halt-on-error arithmetic_van_kampen.tex
```

The third pass stabilizes the contents and cross-references after pagination
changes. Font binaries are not part of this package.

## Trust and scope

The report supplies written proofs and executed finite tests. **No new Lean
or Rocq proof was built or checked.** The included tests are not a replacement
for the proofs and are not an independent external audit.

Sanov's chart, the bounded-conjugator lemma, undecidable finite presentations,
two-generator embeddings, and MRDP are classical inputs, explicitly cited.
Historical priority for the compiler synthesis and circuit formulation is not
established. The work does not claim a universal arithmetic-operation record,
a fully instantiated universal group program, or a finite-fold/single-fold
MRDP breakthrough. Native witness fibers are generally infinite.

Repository comparison is pinned to:
`c58206ca101d4744a015a0f0104646109357d943`.
The original repository was read, not modified.

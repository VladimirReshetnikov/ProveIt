# Diophantine Laws of Probabilistic Computation

**Optimal normalization budgets, unique quartic certificates, and quantum computational substrates**  
Research manuscript prepared for Vladimir Reshetnikov, 30 September 2026.

## Start here

`article.pdf` is the complete article. `article.tex` is its self-contained LaTeX source, including the bibliography. The article supplies ordinary mathematical proofs, worked examples, the relation to ProveIt's MRDP interface, a verification account, and twelve proposed research questions.

The main explicit result is Theorem 5.1. Given a finite rational history of strictly positive probability vectors and an initial accumulated mass, it compiles optimal feasibility into a single quartic integer polynomial. There are exactly

    5*N*m + m + 4*N + 3

natural witness variables and

    5*N*m + m + 6*N + 4

squared residuals. A valid feasible input has exactly one natural witness tuple. The horizon N and number of labels m are external compiler parameters, not unbounded runtime variables in one fixed-arity single-fold universal polynomial.

## Mathematical contents

The article proves the exact normalization condition

    delta * product_s max_i(p[s-1,i] / p[s,i]) <= 1.

It gives the canonical minimal cumulative masses, the finite quartic compiler, a sharp balanced binary total-variation bound, and an operator version involving max-relative entropy. It also proves an exact classification of normalized two-label probabilities: with any fixed success floor below one they are precisely the weakly computable reals in [0,1], while almost-sure two-label return permits precisely computable probabilities.

For effective terminal output laws, a fixed quartic zero set represents a prefix-free set of weighted events. Event membership is projected over arithmetic witnesses; the formula does not count witnesses. Strict unconditional probability comparisons are existential Diophantine, whereas general strict conditional comparisons are Sigma^0_2-complete, even with a success floor arbitrarily near one.

The quantum section supplies explicit integer arithmetic for H, T, S, X, and CNOT, and two exact density-matrix budget examples, including a genuinely noncommuting cycle. The final sections discuss other effective computational substrates and the next formalization targets.

## Files

- `article.tex`, `article.pdf`: full manuscript.
- `code/normalization.py`: exact rational optimum, canonical assignment, numeric residual evaluator, and symbolic compiler.
- `code/quantum_exact.py`: exact four-integer amplitudes over Q(sqrt(2), i), exact probability signs, and an exponential-size reference state vector.
- `code/prefix_allocator.py`: deterministic labeled Kraft allocation for dyadic increments.
- `code/verify.py`: reproducible exhaustive, symbolic, sampled, and exact-arithmetic checks.
- `artifacts/verification.json`: actual test outcomes, counts, versions, and limitations.
- `artifacts/normalization_quartic_N2_m2.json`: parameter order, witness order, residual equations, and complete example assignment.
- `artifacts/normalization_quartic_N2_m2.txt`: expanded quartic polynomial for that instance.
- `artifacts/HTH_prefix_allocation.json`: the finite 12-stage prefix allocation for the irrational HTH output law.
- `source_manifest.json`: repository snapshot and bibliographic source identities.
- `requirements.txt`, `Makefile`: execution and rebuilding aids.

## Running the checks

Use Python 3.10 or newer. The supplied run used Python 3.13.5 and SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

Run this from the archive root. The script regenerates the JSON/text artifacts and prints the verification report. Randomized cases use the fixed seed 20260930. It makes no network requests. There is no spreadsheet, notebook, external dataset, or Wolfram dependency.

A minimal API example, from the archive root:

```python
import sys
sys.path.insert(0, "code")
from normalization import optimal_budget, make_assignment, numeric_residuals, compile_system

rows = [[1, 1], [2, 1], [1, 1]]
maximum_initial_mass, pivots, factors = optimal_budget(rows)
assert str(maximum_initial_mass) == "1/2"
assert pivots == [1, 0]  # zero-based: second coordinate, then first
assignment = make_assignment(rows, 1, 2)
assert all(value >= 0 for value in assignment.values())
assert all(r == 0 for r in numeric_residuals(assignment, 2, 2))
system = compile_system(2, 2)
assert len(system.witnesses) == 33
assert len(system.residuals) == 38
quartic = system.polynomial
```

The mathematical article uses coordinate indices 1,...,m; the implementation uses 0,...,m-1. Both select the earliest maximizing coordinate. The source preserves unreduced rational products to avoid noncanonical witnesses.

For large N and m, work with the residual circuit rather than expanding the polynomial: expansion can consume substantial memory. The quantum evaluator is likewise a small-instance checker, not an efficient classical quantum simulator. It restricts its input to at most 16 qubits.

## Building the PDF

A conventional pdfLaTeX installation with Latin Modern, AMS, geometry, microtype, booktabs, enumitem, fancyhdr, and hyperref is sufficient. No separate bibliography file or image is needed.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

A third pass is harmless after substantial edits to the contents or references. Alternatively, run `make pdf`. The supplied PDF was built and visually inspected with Poppler-rendered pages. No font files are distributed separately.

## Verification and claim boundaries

The finite tests support the implementation, not the general theorems by themselves. The article contains the general proofs. In particular:

* No new Lean or Rocq proof was compiled, and no new proof-assistant axiom audit was run. The formalization section is a plan.
* The full universal MRDP polynomial for output-law representation is **not** expanded by this software. The generated polynomial is the finite normalization certificate only.
* No general finite-fold or single-fold MRDP conjecture is assumed or settled.
* The prefix formula sums weights of distinct projected events, not polynomial solutions.
* The high-success realization theorem makes a nonuniform choice of a sufficiently late small-variation tail. Its uniform greedy construction starts only after suitable data are supplied.
* The operator theorem concerns accumulation of returned subnormalized ensembles, not arbitrary unitary state trajectories.
* Conditional-comparison complexity claims use explicitly floor-guaranteeing program families, or are stated as promise claims. They do not silently add an undecidable semantic validation problem.
* The article does not establish historical priority for every derived consequence, nor advertise the established MRDP, Kraft, weak-computability, or max-relative-entropy ingredients as new.

All principal feasibility, norm, polynomial, and matrix computations use exact arithmetic. The small quadratic-field sign cross-check additionally uses high-precision Decimal as an independent comparison oracle. The binary sharpness-limit diagnostics use floating point and are explicitly labeled illustrative. They are separate from the exact symbolic identities and mathematical proof.

## ProveIt snapshot

The source inspected was the public repository at commit

    f608f1cb3c5be8a736df1328c01b293aabfccf4e

The most important inspected interface is

    Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean

The manuscript does not rely on blanket acceptance of unrelated claims elsewhere in the repository. Pinned source URLs and primary literature are recorded in the article and `source_manifest.json`.

# Diophantine certificates for the consistency of ZFC

Pinned ProveIt revision: `cdd582bec13f908df3711fa9e05d1ddac368a5db`.

## Deliverables

- `diophantine_zfc.pdf` and `.tex`: the main mathematical construction, proof, all coefficient formulas, explicit low-degree alternative, limits, and research questions.
- `direct_stack_core.pdf` and `.tex`: a smaller polynomial local transition relation for the twelve-rule numerical calculus, with a complete finite-path proof. This is a future compiler target, not itself a fixed-arity history encoding.
- `evidence/`: pinned sources, newly authored checkers, literal arithmetic circuits, explicit coefficient recipes, expanded quadratic residuals, and audit receipts.

## Main results

1. Fifteen strictly positive unknowns, six polynomial equations, and a 61-operation shared circuit (34 multiplications, 27 additions/subtractions).
2. A single factored polynomial in the same fifteen positive unknowns: 67 operations (39 multiplications, 28 additions/subtractions), exact total degree 155.
3. A lower-degree alternative: 25 quadratic equations in 34 positive unknowns. Their sum of squared residuals is one explicit quartic of exact degree 4.
4. An archived retained-index fallback: 18 positive unknowns, nine equations, 61 operations, SOS degree 68. It uses the different historical fixed-input coefficient ordering.

For each final main construction, the mathematical proof establishes in ZFC that nonexistence of solutions is equivalent to syntactic `Con(ZFC)`. It does NOT establish nonexistence itself. There is no global minimality claim.

The final inputless constants are `Bm1`, `Kconstant`, `MC`, and the source-side `MF = MF_native + B - 1`. The first window is Start and the second is the forbidden valid `(7,...,7)` window, not End. This ordering is part of the coefficient definition. Do not substitute the historical fixed-input `Kconstant`.

## Exact object files

- `evidence/diophantine_zfc_review/start_only_polynomial67.json`
- `evidence/diophantine_zfc_review/start_only_system61.json`
- `evidence/diophantine_zfc_encoding/start_only_quartic34.json`
- `evidence/diophantine_zfc_compiler/start_only_constants.py`
- `evidence/diophantine_zfc_compiler/start_only_expression_dag.json`
- `evidence/diophantine_zfc_audit/START_ONLY_AUDIT.md`
- `evidence/diophantine_zfc_compiler/INDEPENDENT_AUDIT.md`
- `evidence/diophantine_zfc_core/METATHEORY.md`

Every fixed coefficient is specified by bounded sums, powers and a total predicate on `4366^9` windows. These integers have NOT been expanded numerically. The definition never waits for K215 to halt. The original machine's 430 literal actions are included and independently bound to the formal dense/native tables.

The 35-variable `noinput_quadratic_reduced.json` is included only as an intermediate exact elimination certificate used by the independent 34-variable checker, not as the recommended final low-degree result. The constructive-compiler fallback note describes unfinished work and is not a third completed polynomial.

## Reproduce the bounded checks

Run from any working directory with normal Python 3.10 or newer:

```
python3 /path/to/diophantine_zfc/checks/reproduce.py
```

No third-party Python packages are required for the released checks. Do NOT use `-O`, `-OO`, or `PYTHONOPTIMIZE`; some helpers rely on assertions and the top-level reproducer rejects optimized execution. The reproducer verifies the package manifest and pinned Git blobs, copies evidence to a temporary directory, and runs only specifically named newly authored checkers. It does not modify the release receipts. To record its summary, pass `--receipt /path/to/new-receipt.json`.

The checks cover the machine-table binding, total folded machine and bounded prefix cases, independently generated toy helices, native compiler geometry, arithmetic DAGs, exact coefficient identities, diagnostic degrees, and every quadratic elimination. Synthetic coefficients are diagnostic test values, not the actual huge compiler output. These finite tests do not prove unbounded nonhalting or substitute for the mathematical compiler/Pell/ZFC endpoint arguments.

No received repository Python, Lean, or Rocq source was executed. Upstream `.py` files under `evidence/diophantine_zfc_review/Papers__...` are included as inert pinned source snapshots only. Do not confuse them with the newly authored explicitly named verification scripts.

## Rebuild the documents

On a normal TeX Live installation with AMS math, geometry, booktabs, longtable, enumitem, hyperref, and xurl:

```
pdflatex -interaction=nonstopmode -halt-on-error diophantine_zfc.tex
pdflatex -interaction=nonstopmode -halt-on-error diophantine_zfc.tex
pdflatex -interaction=nonstopmode -halt-on-error direct_stack_core.tex
pdflatex -interaction=nonstopmode -halt-on-error direct_stack_core.tex
```

The provided PDFs were rendered and every page visually inspected. PDF bytes may differ on another TeX installation, while the mathematical source remains identical.

## Verification boundary

This release supplies ordinary mathematical proofs and independently rerunnable finite checks. It does not supply a newly compiled end-to-end Lean/Rocq certificate or an internally encoded ZFC proof object. Repository proof-assistant source and prior build records are identified as imported evidence. The main report explains why the particular mathematical argument is formalizable in ZFC without assuming a transitive or omega-model.

All primary domains are strictly positive integers. Replacing each port by `n+1` yields a nonnegative-integer formulation without changing the variable count or degree. Replacing it by `1+a^2+b^2+c^2+d^2` yields an unrestricted-integer formulation, changing the count and degree. Simply allowing signed values at the original positive ports is unsound.

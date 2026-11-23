# Propositional logic in intuitionistic primitive recursive arithmetic

Research package prepared for Vladimir Reshetnikov, 22 November 2026.

## Start here

Read `propositional_logic_ipra.pdf`. Its 64 numbered results have developed
human-readable constructive proofs, with primitive recursive constructions,
finite bounds, and a detailed Lean formalization path. The appendix maps
the source topics to the proved statements. The numbered-result inventory
is also available as `theorem_inventory.csv` and `theorem_inventory.json`.

The principal results are:

- Classical soundness and completeness, with an actual primitive recursive
  proof-or-countervaluation construction.
- Intuitionistic completeness through a finite table of `m * 2^m` sequents,
  with an IPC proof or a finite Kripke countermodel having at most `2^m` worlds.
- Finite Heyting algebra completeness and disjunction extraction under Harrop
  assumptions.
- Hilbert/natural-deduction translations, analytic tableaux, and classical
  cut elimination by reconstructing a cut-free proof.
- DNF, CNF, NNF, Shannon expansion, Boolean bases, algebraic normal form,
  finite Boolean algebra, prime implicants, and bounded minimization.
- Tseitin conversion, complete resolution, DPLL, Horn least models, 2-SAT,
  and constructive SAT/3-SAT NP-completeness for explicit clocked verifiers.
- Boolean forgetting, uniform interpolation, Craig interpolation and finite
  Beth definability.
- Glivenko's theorem with finite hypotheses, negative translation,
  equivalence of classical schemes, and explicit countermodels to their IPC
  derivability.

The infinite compactness discussion is a boundary analysis: it proves a
finite coding reduction to a path-selection problem, and does not claim
an infinite-path existence principle in iPRA.

## Verification status

The PDF is compiled from the supplied LaTeX. The Python reference suite was
executed successfully, including exported proof/countermodel JSON replay.
See `code/VERIFICATION.md` and `code/validation_results.json` for exact scope
and counts. Tests are implementation evidence, not universal proof.

**The Lean sources are uncompiled proof candidates and an implementation
plan.** No Lean toolchain was available in the producing environment. The
large object-level `Prf PRAAx` derivations are not yet implemented. Eight
short object-logic constructor proofs are provided as candidates, together
with literal closed sentence templates for the two completeness endpoints.
No theorem is represented as an axiom to make an incomplete formalization
appear complete.

## Contents

- `report.tex`, `sections/*.tex`: complete editable LaTeX sources.
- `propositional_logic_ipra.pdf`: compiled report.
- `code/proplogic.py`: dependency-free reference algorithms and checkers.
- `code/validate.py`: exhaustive small-instance checks and negative regressions.
- `code/demo.py`, `code/demo_certificates.json`: four complete portable examples.
- `lean/Propositional.lean`: readable syntax and soundness proof candidates.
- `lean/ObjectExamples.lean`: actual ProveIt object-logic proof candidates and
  numerical endpoint sentence templates.
- `lean/FormalizationPlan.md`: definitions, invariants, upstream interfaces,
  and explicit completion obligations.
- `artifacts/repository_audit.json`: source revision, exact inspected paths
  and Git blob IDs.
- `artifacts/validation_summary.json`: final build/verification record.
- `theorem_inventory.csv`, `theorem_inventory.json`: numbered results and status.
- `SHA256SUMS`: hashes of the delivered files other than the checksum file itself.

## Reproduce

Python 3.10 or newer suffices; no third-party Python dependencies are needed
for the reference algorithms.

```bash
python3 code/validate.py
python3 code/demo.py
python3 build_report.py
```

The report build requires pdfLaTeX with standard AMS, geometry, table,
hyperref, microtype, enumitem and fancyhdr packages. The build script can
bootstrap a missing format and font-map database locally when the complete
TeX distribution files are already installed; it never downloads packages.

For the Lean metatheory candidate, use an installed Lean 4 environment and
read `lean/README.md`. To check `ObjectExamples.lean`, put the package into
the pinned ProveIt workspace or supply its Lake search path. The source
revision is:

`803d951d15834da5571e26d1f39988d921b29760`

The inspected upstream dependency inventory names Lean 4.32.0. No successful
Lean run is asserted by this package. Repository dependencies are referenced,
not vendored; the proof report and Python programs are self-contained.

## Conventions that matter

Classical propositional logic is the object of constructive metamathematics.
A Boolean truth table does not assert unrestricted arithmetic excluded middle.
All large finite tables have primitive recursive bounds. A numerical Gödel
code is not treated as the bit length of its encoded formula. Tseitin
equivalence uses auxiliary variables; interpolation here is finite and
Boolean. The IPC proof-tree bound allows the explicitly derived cut rule,
while the separate LK result removes classical cuts by semantic rebuilding.

The three-scheme Hilbert completeness result uses the declared language with
bottom and implication and negation defined as implication to bottom; it
does not silently identify that grammar with every historical primitive-
negation presentation.

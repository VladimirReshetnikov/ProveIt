# Abstract and continuous mathematics through explicit presentations in iPRA

Research package prepared for **Vladimir Reshetnikov**, 20 November 2026.

Start with the **41-page `report.pdf`**. Its editable source is **`report.tex`**, with the
complete arguments in `sections/` and the bibliography in `references.tex`.
The package develops a common framework for represented continuous objects
and applies it to category theory, compact metric model theory, function-space
topology, infinite-dimensional coercive equations, a weak elliptic boundary
problem, and complex analytic approximation.

## Main mathematical contributions

1. **Completion with explicit demands.** A dense evaluator with a supplied
   joint modulus extends to regular names. The report proves independence of
   names, product compatibility, and change of dense presentation when an
   approximate inverse selector is supplied.
2. **Continuous model theory through finite observations.** Finite metric
   nets approximate values of fixed formulas built using min/max,
   complementation, and alternating infimum/supremum quantifiers. The proof
   preserves quantifier order and introduces no extra error factor from
   quantifier depth. A net is not assumed to be a finite submodel. An
   alternating minimax example has value `3 - 2*sqrt(2)` and an explicitly
   approximated optimizer.
3. **Quantitative function-space topology.** Tent weights give a continuous
   partition of unity with a derived positive denominator bound. They yield
   finite continuous approximants with an explicit entropy bound, a
   quantitative converse, and guarded gluing estimates. The approximants lie
   in the ambient function space; choosing representatives within an arbitrary
   family remains a separate problem.
4. **A constructive coercive-operator solver.** Strong approximation data and
   positive coercivity produce a contraction gap, precision demand, and
   explicit iteration clock. Comparing two finite runs proves that their
   outputs form one coherent solution name. The report also proves residual
   certification and stability estimates.
5. **A variable-coefficient Dirichlet problem.** In the completion of rational
   zero-boundary polynomials with the energy inner product, the report
   explicitly constructs the operator and load vector for
   `-(a*u')' = f`, with positive coefficient bounds. This produces a weak
   solution together with energy and uniform error bounds. The construction
   does not appeal to an unspecified Riesz representation algorithm.
6. **Complex derivatives with an explicit radius gap.** A coefficient bound
   `|a_n| R^n <= M` and a smaller radius `r < R` give geometric tails for every
   derivative up to a requested order. Finite coefficient observations select
   polynomial approximants with a proved `C^J` error and an explicit list-size
   bound.

The report also proves precise boundaries: quantitative total boundedness
does not by itself supply effective subsequence selection; weak Hilbert data
do not generally determine a computable strong norm name; approximate formula
values do not decide exact zero truth; and a qualitative analyticity assertion
does not replace radius and majorant data.

## Exact trust boundary

The report gives full human-readable mathematical arguments and an explicit
route to first-order intuitionistic primitive recursive arithmetic. **The new
main analytic theorems have not yet been compiled into proof values of type
`Prf PRAAx`.** The remaining object-language work is identified, with actual
denominator-cleared invariants and existing repository interfaces, in the
formalization section and `lean/OBJECT_LANGUAGE_PLAN.md`.

The supplied Lean project contains **19 completely proved host Lean lemmas**,
checked with **Lean 4.32.0**. They include positive-formula transfer, finite
evaluation correctness, the perturbed-contraction invariant, and the complete
scalar solver schedule. There is no `sorry` and no newly declared axiom.
These are ordinary Lean theorems, rather than newly constructed iPRA
derivations.

The axiom audit is explicit. `positive_transfer` has no axiom dependencies.
The finite evaluator uses `propext` and `Quot.sound`. The rational arithmetic
proofs inherit `propext`, `Classical.choice`, and `Quot.sound` from Lean's
standard `Rat` library. The archive therefore does not describe the entire
host development as axiom-free or choice-free. The intended object-iPRA
implementation clears denominators and uses the displayed quantifier-free
induction invariants.

The Python programs are **finite exact-arithmetic demonstrations**. Their
pass/fail comparisons use rational or integer arithmetic; decimal summaries
are only for display. Passing these checks validates the implementations and
selected constants, not the universal mathematical theorems. Actual analytic
norms are not identified with rational numbers: the checked scalar budget
uses a rational majorant whose connection to the norm requires the separate
analytic argument.

## Artifact map

| Path | Contents |
|---|---|
| `report.pdf` | Complete research report, including proofs, limitations, source review, and formalization route. |
| `report.tex`, `sections/`, `references.tex` | Complete editable LaTeX sources. |
| `lean/QuantitativeKernel.lean` | The 19 checked host Lean lemmas and all their project definitions. |
| `lean/Audit.lean`, `lean/Examples.lean`, `lean/verification.log` | Axiom reports, checked examples, and actual successful replay output. |
| `lean/OBJECT_LANGUAGE_PLAN.md` | Precise coding, object formulas, induction invariants, finite two-run coherence proof, and implementation order. |
| `lean/README.md`, `lean/PROVENANCE.json` | Detailed formal status, compiler identity, and inspected repository source identities. |
| `code/compact_logic.py` | Finite continuous-formula evaluator and alternating minimax checks. |
| `code/topology_demo.py` | Tent interpolation, quantization, clipping, and guarded gluing demonstrations. |
| `code/hilbert_solver.py` | Infinite diagonal Hilbert example through finite support, polynomial identities, and variable-coefficient PDE iteration. |
| `code/complex_jets.py` | Finite geometric bounds, exact geometric-function derivative checks, and noisy coefficient rounding checks. |
| `evidence/` | Source audit, per-program JSON results, integration record, and document build/inspection evidence. |
| `evidence/claims_status.json` | Claim-by-claim hypotheses, conclusions, proof status, and remaining formalization work. |
| `evidence/source_manifest.json` | Immutable URLs and Git blob identities for the 39 upstream sources in the recorded review. |
| `MANIFEST.sha256` | Integrity hashes of all other files in the archive. |
| `verify.py`, `build_pdf.py`, `Makefile` | Reproduction entry points. |

All project source dependencies of the standalone Lean development are
included. It imports only the pinned Lean distribution's standard library;
it does not require Mathlib or a ProveIt checkout. The future object-language
integration plan refers separately to the inspected ProveIt modules.

## Reproduce the finite demonstrations

Run commands from the package directory. The four programs use only Python's
standard library; the exact tested Python version is recorded in
`evidence/integration_checks.json`.

```bash
python3 verify.py
```

Equivalent Makefile target:

```bash
make examples
```

The verifier runs all four programs, regenerates their JSON evidence, checks
their successful exit status and reported result, and writes
`evidence/integration_checks.json` with source/output hashes and elapsed
times. Run Python without `-O`, since the demonstrations use assertions.

Individual runs are:

```bash
python3 code/compact_logic.py --output evidence/compact_logic_checks.json
python3 code/topology_demo.py --output evidence/topology_checks.json
python3 code/hilbert_solver.py --pde-max-n 3 --output evidence/hilbert_checks.json
python3 code/complex_jets.py --output evidence/complex_checks.json
```

The full finite-net cardinality bounds can be enormous. The examples compute
selected approximants and verify the relevant inequalities without trying to
enumerate every member of those theoretical covers.

## Replay Lean

With the pinned Lean toolchain available through Elan:

```bash
make lean
```

Or enter `lean/` and run:

```bash
bash replay.sh
```

For a standalone Lean distribution, from the package directory:

```bash
LEAN_LAKE_BIN=/absolute/path/to/lean-4.32.0-linux/bin/lake make lean
```

The replay prints the compiler version, builds `QuantitativeKernel`, prints
the axiom reports, and checks the examples. Toolchain installation is
separate. Generated `.lake/` files are disposable and are not needed in the
delivered archive.

## Rebuild the PDF

Install pdfLaTeX/TeX Live with AMS packages, Latin Modern, geometry, microtype,
booktabs, enumitem, xurl, hyperref, fancyhdr, and listings, then run:

```bash
python3 build_pdf.py
```

Equivalent target:

```bash
make pdf
```

The script runs three LaTeX passes and records build evidence. It includes a
fallback for a minimal Debian-style installation whose format or font-map
files have not been configured. It rejects undefined references, overfull
boxes, and missing-character warnings. Visual page inspection is a separate
validation step; a successful compiler exit alone does not perform it.

To run the demonstrations, Lean replay, and PDF build together:

```bash
make verify
```

## Source snapshot

Repository review was pinned to:

```text
VladimirReshetnikov/ProveIt
5f3be02388442f16487d2dc5c2529961dd783d2b
```

[Open the inspected iPRA directory at that commit](https://github.com/VladimirReshetnikov/ProveIt/tree/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic).

The repository was read and not modified. `evidence/source_manifest.json`,
`evidence/repository_audit.md`, `evidence/category_model_source_audit.md`, the
report bibliography, and `lean/PROVENANCE.json` identify the inspected source
paths and distinguish existing object-iPRA proofs from external metatheorems
and older unverified research packets. The ledger records the scope of each
inspection; this is not an audit of the entire repository.

# Coupled Computation and Refinement in iPRA

Research packet prepared for Vladimir Reshetnikov, 19 November 2026.

Read `ipra_coupled_refinement.pdf` for the complete human-readable report.
Its complete LaTeX source is `ipra_coupled_refinement.tex` with the included
`paper/` chapters. Repository comparisons are pinned to ProveIt commit
`3ee850b4c2d650cf01263823fd5415963747c5d0`.

## Main results

1. A finite nonnegative matrix certificate produces a convergence clock,
   regular sampler, uniqueness modulus and posterior error enclosures for
   coupled approximate rational actions.
2. Finite matrix powers produce positive weights and Neumann supersolutions.
   Finite Neumann sums also produce an inverse name near the identity.
3. Polynomial coefficient bounds produce action contracts; an explicit
   multivariate radius calculation produces local charts from rational
   regular base-point data.
4. Bounded-delay coordinate updates have an explicit clock under finite
   update-coverage and delay certificates.
5. A commutation defect between finite models yields a coherence estimate
   after division by the contraction gap. Finite telescoping then constructs
   named observations of a growing-dimensional object.
6. A complete example constructs the unique solution in the unit cube of

       x_i = 1/(4(i+1)) + x_i^2/8 + x_(i+1)/8.

   A coordinate query uses only i+k+3 coordinates and an explicitly bounded finite number of
   dyadic operations. A separate bisection construction gives a second
   bounded branch in `[6,8]`, proving that the region restriction matters.

## Verification status

- `lean/AffineBounds.lean`: **18 proved theorems compiled with Lean 4.32.0**,
  importing `Std` only. All printed axiom dependencies are subsets of
  `propext` and `Quot.sound`; no `sorryAx` or `Classical.choice` appears.
- The `*Blueprint.lean` modules: **typechecked definitions and theorem
  targets**. The target propositions have not been proved. No `axiom` or
  `sorry` asserts them.
- `lean/ObjectAdapter.lean`: **uncompiled integration outline** targeting
  the actual ProveIt `Prf PRAAx` API. It requires genuine object-theory
  proof values, and does not turn host-Lean theorems into iPRA proofs.
- `code/`: exact finite reference computations using Python standard-library
  rational arithmetic. They check implementation details and examples;
  they are not universal proofs or an iPRA proof checker.
- The report supplies complete human arguments and a detailed QF-induction
  translation plan. **The complete application-level object-iPRA Lean export
  is not claimed finished.**

## Reproduce

```sh
python3 code/run_checks.py
python3 code/approximate_actions.py
python3 code/upper_branch_reference.py --output validation/upper_branch_checks.json
bash lean/build.sh /absolute/path/to/lean
bash build_pdf.sh
```

The first command runs 24 unittest methods and regenerates the exact data
tables. The second checks the approximate-action and delayed-update examples.
The third checks the explicit upper branch using rational bisection.
The Lean script compiles the arithmetic proofs and blueprint definitions,
and writes a combined validation log. It deliberately excludes the repository
adapter. The PDF build requires `latexmk`, `pdflatex` and standard LaTeX
packages, including AMS mathematics, Latin Modern, microtype and hyperref.

For object-level integration, use the pinned ProveIt revision and its normal
Lake providers, implement the rational/finite-vector frontend and arithmetic
proof fields described in the report, then check the resulting `Prf PRAAx`
endpoints and their axiom reports. The repository source and external Lean
toolchain are not bundled in this packet.

## Layout

- `ipra_coupled_refinement.tex`, `paper/`: complete report source.
- `ipra_coupled_refinement.pdf`: compiled report.
- `lean/`: proved arithmetic, typechecked blueprints and object export outline.
- `code/`: exact algorithms, tests and reproducible sample data.
- `validation/`: actual check results and an independent mathematical review.
- `sources/repository_sources.json`: pinned source provenance and citation map.

The report credits existing scalar contraction, chart and ODE results and
does not claim that arbitrary cyclic proofs, singular branches, or the general
Faltings/Siegel and prime-distribution difficulties are resolved.

# TAPIR-iPRA

**Typed Arithmetic Proof Intermediate Representation for intuitionistic
primitive recursive arithmetic**

This research package develops a proof-producing last-mile framework for the
current `VladimirReshetnikov/ProveIt` iPRA repository.  It was prepared against
commit `58627ed89814ba122e1f0f012f1aba103cda267b` on 2026-11-16.

## Main contribution

A theorem-specific finite argument is specialized at Lean elaboration time to
concrete `PR`, `PTm`, and `Fm` syntax.  It is represented by a typed
`Plan Γ φ`.  A structural interpreter compiles every plan to the literal
ordinary judgment `Γ ⊢[PRAAx] φ`.

A sequential `Schedule R outs` is a topological ordering of local proof nodes.
A new node may use earlier outputs and explicit residual producer hypotheses
`R`.  By induction on the schedule and `Prf.trans`, every output is compiled to
a plan from `R` alone.  Supplying object proofs of the residuals closes the
final theorem.

The report also develops:

- local / observed / named certificate escape analysis;
- bounded witness naming through the repository's checked
  `BoundedReflection.bounded_choice` theorem;
- an arity-polymorphic generalization of checked least search and bounded
  reflection;
- compositional reflected formulas for fixed bounded logic;
- clocked trace and measure-decreasing termination patterns;
- finite presentations of algebraic, analytic, geometric, probabilistic, and
  quotient-like concepts;
- conditional complete enumeration from explicit height/code bounds;
- a 20-item difficulty audit and dependency-ordered Lean roadmap.

## Formal status

This distinction is essential:

- Existing ProveIt declarations cited in the report are inherited checked
  dependencies at the pinned commit.
- The new generic mathematics is fully argued in the report.
- `lean/TAPIR/Kernel.lean` and `Schedule.lean` are no-placeholder source
  candidates, but were **not elaborated** because no Lean/Lake executable was
  available in the artifact runtime.
- Other Lean files are explicit blueprints with visible `sorry` milestones.
- Python tests validate finite host algorithms only.  They are **not** an iPRA
  proof checker and are outside the logical trust base.
- Deep producers such as general Diophantine height bounds, convergence
  moduli, separation gaps, and effective constants remain explicit residuals.

This archive claims no new Lean-kernel-checked theorem.

## Contents

- `paper/tapir_ipra_framework.tex` and `paper/sections/` - complete LaTeX.
- `paper/tapir_ipra_framework.pdf` - compiled report.
- `lean/TAPIR/` - Lean source candidates and blueprints.
- `lean/FORMALIZATION_PLAN.md` - route to checked integration.
- `reference/` - exact host algorithms and unit tests.
- `examples/demo_contract.json` - generated contract/schedule example.
- `schema/tapir_plan.schema.json` - exchange schema.
- `metadata/` - status, source audit, theorem ledger, difficulty matrix, claims,
  and integration map.
- `validation/` - test, PDF, font, and static-scan reports.

## Reproduce

```bash
./build.sh
```

Or run the principal pieces separately:

```bash
PYTHONPATH=reference python3 -m unittest -v reference/test_tapir_reference.py
PYTHONPATH=reference python3 reference/generate_demo.py
cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error tapir_ipra_framework.tex
```

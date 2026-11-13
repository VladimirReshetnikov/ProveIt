# Source-only witness-bound client for the Pell blueprint

The Pell recursion's zero clause is a substitution of Foundation's `pairDef`; its successor clause contains two **unbounded** projection witnesses. Existing source provides `wb_pairDef`, `wb_pi₁Def`, `wb_pi₂Def` and bounds each projection by the encoded previous state. The inert `PellBlueprintWB.lean.src` proposes a zero-clause `WB` proof, two projection-bound lemmas, and a conditional successor-clause client. It has not been elaborated or compiled.

The generic `wb_auto` tactic handles named graphs when supplied their `WB` premises and handles the conjunction/substitution structure. Its source does **not** automatically provide bounds for arbitrary unbounded existentials. Therefore the proposed successor proof uses `wb_exs_term` twice and retains two explicit **unproved extraction premises**. It does not claim the successor clause is already proved.

## Contexts and the two missing extractions

The literal successor source is

```text
out previous index b. ∃ x y,
  pi1(x,previous) ∧ pi2(y,previous)
  ∧ pair(out,(b+2)x+(b+1)(b+3)y,x+(b+2)y).
```

Once x is being bounded, the remaining outer environment is `[out,previous,index,b]`, so the natural bound term is `#1`. Once x has been introduced and y is being bounded, the environment is `[x,out,previous,index,b]`, so the bound is `#2`. These refer to the same `previous` value. The draft's `FirstBound` and `SecondBound` require the corresponding semantic bodies to imply those inequalities. The two proposed projection lemmas use `pi₁_defined.defined`/`pi₂_defined.defined` and the source lemmas `pi₁_le_self`/`pi₂_le_self`; a follow-up must connect the embedded graph conjuncts of the exact quoted successor body to those lemmas.

`succInner_wb` attempts the quantifier-free-at-top body using the three reusable graph `WB` facts. `succ_wb_of_bounds` attempts to match the literal blueprint successor definition to the two existential closures of that body and applies `wb_exs_term` at the stated indices. Its two extraction facts are explicit theorem parameters. The `change` step that expects quotation-generated syntactic equality, `wb_auto` behavior, graph interpretation, local `Iopen`/`PA⁻` instances, all tactics and the axiom reports are untested; their correctness is not implied by the source-level context analysis.

A candidate-PRA model may supply the arithmetic reduct and open-induction/PA-minus instances through the existing machinery. Even after a successful proof of both clause premises, applying `wb_resultDef` would require the separately drafted, likewise unelaborated paired-value majorant and coherent provider selection. Its result is a model-level `WB` property; it is not automatically a uniform primitive-recursive code for every nested witness of the period formula or a derivation in iPRA.

The checker pins the Pell blueprint, calculus, projection facts and inert draft. It checks source shapes and the two expected indices, and exhausts 10,000 standard-natural unpairing controls. This does not inspect a Lean-generated AST or prove the model lemmas. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-pell-blueprint-wb-draft/check.py | cmp - research/ordinary13-pell-blueprint-wb-draft/receipt.json
```

No Lean, build, staging, axiom report, or iPRA result was produced.

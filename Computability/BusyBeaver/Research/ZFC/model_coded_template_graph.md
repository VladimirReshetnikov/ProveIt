# Represented substitution into fixed proof templates

[`ModelCodedTemplateGraph`](../../../../Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/ModelCodedTemplateGraph.lean)
assigns a fixed parameter-free arithmetic graph to each standard source
formula with a predicate placeholder. In every IΣ1 model the graph is total
on all raw matrix codes. At a well-formed matrix code, its output is exactly
the translated formula produced by the
[finite template compiler](model_coded_core_compiler.md).

The inserted matrix and its free-variable labels may be nonstandard. The
source formula and placeholder arity remain ordinary finite syntax. The
arithmetic graph is defined before introducing the model: ordinary arithmetic
atoms use fixed natural codes, placeholder atoms use the represented
substitution operation, and logical constructors use their represented
coding operations. Separate cast lemmas connect these fixed numerals with
the internally quoted terms, argument vectors and atoms. The module supplies
both Σ1 and Δ1 graphs, with unique output even at invalid raw matrix inputs.

For a fixed standard proof `d : templatePeano arity ⊢! σ`, it also proves an
actual IΣ1 theorem, and hence a PA theorem, of this form:

```text
∀ s, WellFormedMatrix(arity, s) →
  ∃ y, TemplateGraph(σ, y, s) ∧ Provable_PA(y).
```

The sentence is fixed ordinary arithmetic syntax and quantifies over every
internal matrix. Its proof uses the existing compiler's accepted internal PA
proof witness, then arithmetic completeness. It does not assert that PA's
conclusion is true in an IΣ1 model. `templatePeano` is ordinary PA lifted to
the placeholder language; its induction axioms contain only the original
arithmetic symbols.

The result provides a reusable fixed-template component. It does not yet
translate arbitrary internally coded source formulas or proofs, or provide
the syntax-sensitive set-theory and constructibility proof selectors needed
for the machine's PA consistency equivalence.

The [verification](results/model-coded-template-graph-verification.json)
freshly checks six local modules and four audits, with twenty-two axiom
reports and thirty-seven callers. The new graph contributes thirteen reports
and seventeen callers with no warnings. The earlier modules retain ten style
warnings. All axiom reports use only the three standard Lean axioms. The
[independent review](results/model-coded-template-graph-review.json) checks
the fixed graph, quoted constants, internal matrix scope, and PA endpoints.
Existing pinned dependency objects are reused; no full dependency rebuild
is claimed.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_model_coded_template_graph.py \
  --sources Logic/PeanoArithmetic/BoundedConsistency/Lean \
  --dependency-root /path/to/built/dependency-checkout \
  --lean /path/to/lean-4.32.0/bin/lean \
  --hygiene-audit Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/ModelCodedPredicateHygieneAudit.lean \
  --core-audit Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/ModelCodedCoreCompilerAudit.lean \
  --peano-audit Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/ModelCodedPeanoCoreAudit.lean \
  --template-graph-audit Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/ModelCodedTemplateGraphAudit.lean \
  --output /outside/new-empty-template-graph-check
```

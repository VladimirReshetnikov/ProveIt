# Natural-79 factor units at `w=0`: source-only proposal

`Natural79ZeroWUnits.lean` proposes a graph-specific step toward the reviewed
[79-operation zero transfer](../ordinary14-natural-forced-w79/README.md).
It applies to a model `V` satisfying `IΣ₁`, a literal 79 zero, and `v 6=0`.
The source and all its imports are **unelaborated**; no Lean process or axiom
report was run, and its tactic scripts, elaboration and provider requirements
remain unverified. This is not an iPRA theorem or a physical graph/byte/PDF
binding.

The proposed `product_of_zero` extracts the five signed factors' product one
from the literal graph, adapting the existing 74-graph signed-pair pattern.
`first_eval_at_w_zero` proposes the exact difference-ring cut `F0=r²` for
arbitrary integer ports. Hence its signed pair cannot represent −1: the
square is nonnegative. `units_of_zero_w_zero` combines this with the existing
`product5_positive` theorem and the three explicit hypotheses that the main,
auxiliary and strong signed factors do not have residue −1 modulo four. Its
conclusion lists all five positive signed units, including the unrestricted
guard. It assumes **no positive w, beta, J, gamma, K0, or other port bound**.

The separate proposed `restricted_residues_of_shapes` uses the existing
source-only 74 generic `main_ne`, `aux_ne` and `strong_ne` lemmas, but takes
as explicit hypotheses three expression-pattern equalities for the **79**
graph. Those shape equalities are not proved in this packet; do not treat the
residue hypotheses as discharged. In particular, the statement does not yet
prove positivity of J or w, establish the divisibility contradiction, or
connect the 79 graph to its parent endpoint. The source imports the generic
residue draft as well as the graph draft; both need to be elaborated in a
coherent provider chain. Its three `#print axioms` lines are unexecuted.

The deterministic checker pins the sources and 79 JSON, checks the relevant
first-factor and product DAG rows and proposed signatures, exhausts the
three generic modulo-four factor patterns, and runs 300 finite arbitrary-port
controls at `w=0`. These checks supplement the exact algebraic reasoning;
they do not establish Lean type checking, the missing graph pattern
bindings, a model theorem, axiom closure, or iPRA derivability.

An [independent source and mathematical review](../../reviews/ordinary14-natural79-zero-w-unit-independent/README.md)
checks the first-factor cut and the explicit residue assumptions without
elaborating the model statements.

Run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-natural79-zero-w-unit-draft/check_source.py | cmp - research/ordinary14-natural79-zero-w-unit-draft/result.json
```

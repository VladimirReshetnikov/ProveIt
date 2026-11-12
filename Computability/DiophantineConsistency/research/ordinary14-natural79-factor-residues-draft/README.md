# Literal 79 factor residues and zero-w unit client: source proposal

This packet proposes the graph-pattern step left explicit in the
[zero-w unit draft](../ordinary14-natural79-zero-w-unit-draft/README.md).
Both files here and all their dependencies are **unelaborated source-only
proposals**. No Lean proof, axiom report, iPRA derivation or physical
coefficient/PDF binding is established.

`Natural79ResidueShapes.lean` reproduces the 79 graph's let block to expose
six intermediate expression atoms. It proposes three literal `rfl` cuts
identifying the main, auxiliary and strong factors with the generic patterns
already used by `FactorResidues74Draft.main_ne`, `aux_ne` and `strong_ne`.
The proposed `restricted_residues` client uses those pattern lemmas for
arbitrary integer ports and arbitrary model valuations; it needs no `w>0`,
`gamma>0` or port positivity assumption. The copied let block and these `rfl`
claims may be expensive to elaborate, and none has been tested in Lean.

`Natural79ConcreteUnits.lean` proposes combining those three exclusions with
`Natural79ZeroWUnitsDraft.units_of_zero_w_zero`. Its stated premises are only
a literal 79 zero and `w=0` in the existing `IΣ₁` model interface. Its
conclusion is that all five factor signed pairs represent +1. This is a
proposed source composition, not yet a checked model theorem. In particular,
it does not itself establish the later J-positivity, main-norm divisibility,
`w>0`, parent zero transfer or iPRA endpoint. The two `#print axioms` commands
in this packet have not been executed.

An [independent source review](../../reviews/ordinary14-natural79-factor-residues-independent/README.md)
checks the literal factor trees and the proposed unit-client assumptions;
it does not elaborate the `rfl` cuts or model statements.

The deterministic checker pins the two proposed modules, the source 79 graph,
its JSON, and the two dependency drafts. It verifies the copied let block and
three corresponding full JSON expression trees against the generic factor
patterns. It also checks selected client calls. This is syntactic evidence:
it does not prove that Lean's terms or `rfl` tactics elaborate, that the
provider chain is coherent, or that the external JSON is formally bound to
the Lean expression.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-natural79-factor-residues-draft/check_source.py | cmp - research/ordinary14-natural79-factor-residues-draft/result.json
```

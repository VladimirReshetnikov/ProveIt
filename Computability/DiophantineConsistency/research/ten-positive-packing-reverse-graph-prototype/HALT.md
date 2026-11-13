# Halt to a symbolic-port 80-graph zero

`TenPositiveHaltReverseGraph.halt_zero_of_model_ports` proves that a halt of
the represented machine yields a positive zero of the selected 80-operation
Lean graph in every supported IΣ₁ model, assuming the four stated model port
equalities. In particular, the second port must equal `paramKernel rho` in the
model. The proof obtains one packing and the associated `SeedRelations` tuple
from `CompactHaltFirstSeed.halt_first_seed`, derives phase and size from the
same packing, and applies `packing_seed_zero`.

This is the reverse direction only. It does not by itself prove an internal
iPRA statement or identify the symbolic second port with the different K0
coefficient in the retained 80 JSON/PDF proposal. The exact external
JSON/PDF-to-Lean correspondence remains open.

The accepted guarded check is `observations/halt-attempt01/`. It produced
`/tmp/halt-reverse-graph-7ku3x6_a/HaltReverseGraph.olean`, SHA-256
`f66996ade1c7634045981deb8296819176b12dbdf648aaa00c394abfa8d3b3ba`.
Source SHA-256 is `c652353778e96098e7ca96f5bc0687221aecfc2dc0e3d8c7c1e121b5dc54f636`;
runner SHA-256 is `1f0eb946baa7444c89bf4eb8583493380630bcb39d3f847dbc97ce5054b7fd5e`.
The runner records and checks every direct source import's selected path and
hash before and after Lean, with resource samples. Its standard Lean axioms
are recorded in the captured output; no `sorryAx` was reported. Historical
transitive source/object, package and dynamic dependency limitations remain.

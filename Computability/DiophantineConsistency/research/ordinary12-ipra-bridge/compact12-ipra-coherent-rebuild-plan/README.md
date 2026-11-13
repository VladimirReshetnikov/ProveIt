# Source-pinned preflight for a coherent compact12/iPRA endpoint

The compact symbolic positive-zero ↔ model-halt theorem and the generic
positive-model-to-iPRA adapter were checked against different provider
closures. They cannot simply be imported together: the selected nine-variable
and compact halt providers have 96 shared relative file paths, 67 with
different bytes. This is a provider provenance conflict, not by itself a
mathematical contradiction.

This read-only preflight pins the exact current source bytes and declared
project imports for the 441-module source closure of `IPRAExpressionNative`,
`HAExpressionAssembly` and `AdaptiveEquationSyntax2011`; it also pins the
positive adapter and symbolic model-equivalence sources. It hashes all live
files in the selected nine-variable, compact halt, outer-seed and compact-word
provider roots before and after scanning. The three compact roots have no
conflicting common files. Full file hashes, resolved paths, pairwise conflict
lists, source imports and proposed ordered source closures are retained in
[`scan.json`](scan.json) and [`pins.json`](pins.json).

For this observation:

- Building the endpoint's stopped source-import closure from the selected
  compact union would require **425** project modules absent from that union.
- Keeping the nine-variable endpoint base and selecting compact objects at its
  conflicting project-module paths affects 75 of the 441 endpoint-source
  modules: 15 are conflicting selected modules and 60 further modules depend
  on them in the pinned source graph. This makes a selective rebuild on the
  nine-variable side a promising *smaller starting point*.
- These counts concern the endpoint source closure only. They do not include
  the full compact graph/halt suffix, its top-level clients, the final bridge,
  or any extra modules revealed by exact Lean dependency resolution.

The 60-module figure is **not** a proof that a 60-module rebuild will work or
that its source files match the historical provider objects. Before building,
a guarded runner must choose one coherent namespace/overlay, inventory and
compare every actual overlapping path and companion across **all** selected
roots, pin source/object provenance, rebuild every affected dependent in
actual dependency order, guard all inputs and outputs, and stop on a conflict
or unexplained failure. The existing top-level versus namespaced signed-
transport collision must also remain resolved. Package, dynamic dependencies,
Lean's exact import resolution and source-to-object ancestry are not certified
by this static scan.

The normal scan exited 0 with all four provider inventories unchanged;
`scan.py` SHA-256 is
`e7c13cb5d3371fe0708086f5724fde88ed91390a22a046e29e82fa8113708387`,
`pins.json` SHA-256 is
`69e58c487a271bd520c371f796f72dcccd8d025105b0909d5a1e425785d39a6d`, and
`scan.json` SHA-256 is
`a2a217da82e4e330393bd308983c523bace6357813f296f202ad57bfac0a2efa`.
The scanner performs no Lean compilation and establishes no object-level
proof. An exact all-model bridge for the fixed symbolic expression and the
positive-domain adapter have separate checked evidence; a coherent compilation
is needed before they can be applied together.

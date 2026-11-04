# Same-zero uniform reduced projection

`Trace74UniformProjectionGraph.graph_reduced` binds the variable-parameter
all-ring projection reduction to a **single** positive 74-operation graph
valuation. For any model index `r ≥ 2` supplied with that valuation's main
Pell ordinate, it writes `K = 2^r = 4·2^(r−2)` internally and derives the
reduced divisibility in the model's difference ring. The result does not
require the index to be odd.

The theorem assumes the main-ordinate identity; it does not produce the
index, prove the additional near-diagonal window, establish the strict
height inequality, eliminate any zero, prove the 74/75 reverse guard, or
give an iPRA endpoint. It holds in models of `IΣ₁`; the Lean metatheory axioms
listed below are not object-theory axioms.

The author check used the provider order in the [all-ring reduction
record](../trace74-uniform-projection-reduction-draft/README.md), with `/tmp`
prepended to `LEAN_PATH`. Lean 4.32.0 was invoked with `timeout 120`,
`-M3000 -j1 -DElab.async=false`, this directory as `--root`, and output
`/tmp/Trace74UniformProjectionGraph.olean`. Tool session 39193 exited 0 and
reported `[propext, Classical.choice, Quot.sound]` for the theorem.

* Source SHA-256: `c870b567e252d705645fa135b5923a3bd26249b87bf027c6207a5326fc022ea3`.
* Output object SHA-256: `e7e72f7339c7f5c2d876b82c0ac4ed84aac32a0c9a01b80291e52904eb4cc92c`.
* Imported `Trace74UniformProjectionReduction.olean` SHA-256:
  `6a0cc98e1ec41e57cd816d3234c52e6d3e4cfbe06785227cc72f281614fc5f70`.
* Imported `Trace74GraphProduct.olean` SHA-256:
  `b8c14f9e1a8a0ae3d0328ca707f208eb4b94cb3bee5c30e3d519a4361455fad3`.

The direct inputs were hashed, but this check did not authenticate the
complete transitive provider or package ancestry and is not an independent
replay. An earlier author run, session 92010, exited 1: rewriting the index
on both sides changed an exponent on the right. The accepted source uses a
separately established index equality instead.

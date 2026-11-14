# Fixed Σ₁ graphs for PA194 source operation codes

The preceding packages prove the existence of finite candidate-PRA codes whose
standard evaluations compute PA194 source formula shift, formula depth,
sequent depth, annotated LK budget evaluation, and universal-rule search.
This package chooses one code for each operation once, by classical choice,
and uses `PA194CodeGraph.graph` to define a fixed parameter-free Σ₁ formula for
each chosen code.

The five `*_defined` theorems prove that in **every** candidate-PRA model whose
arithmetic reduct satisfies IΣ₁, each graph defines the model's interpretation
of its chosen code on **all** model inputs. The five `*_standard` equations
identify standard natural-number evaluations with the corresponding source
operations.

The composition was checked against an ordered source overlay and the separately
checked graph-development cache. The source-code bridge modules were rebuilt
against the same audited project `PRAFiniteFunctionCodes` objects used by the
graph cache, avoiding mixed object versions. The printed model and standard
results report `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
The full two-chain standalone script has not yet been replayed.

The chosen code trees and graph formulas are existential/classically chosen,
not printed or computationally extracted. **The model-graph theorems identify
only the actual model interpretation of each code.** They do not establish that
this interpretation agrees with the intended source-syntax operation on
nonstandard inputs, internalize the full compiler, or prove either PA194
machine/Con(PA) implication.

To rebuild from the repository root, set `IPRA_FOUNDATION_OVERLAY` to the
audited current Foundation object overlay and `IPRA_LEAN_OVERLAY` to the pinned
audited project object overlay, then run
`bash Computability/BusyBeaver/Research/PA/pa194-source-code-graphs/check.sh`.
The script builds its two prerequisite chains into separate tmpfs directories
and recompiles the shared bridge modules against the graph chain's single
project overlay.

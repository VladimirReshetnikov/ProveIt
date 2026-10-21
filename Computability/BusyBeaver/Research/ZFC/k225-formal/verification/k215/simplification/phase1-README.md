# Shorter checked K215 proofs

The exact 215-state machine and all endpoint statements are unchanged. The
simplified proofs pass incremental kernel checks against the
[original full-build baseline](../README.md) at `613f9cf28a`.

| Proof source | Before | After | Reduction |
| --- | ---: | ---: | ---: |
| [Lean dominated implication](../../../../../../Lean/BusyBeaver/ZFC/DomRho8.lean) | 689,857 bytes | 135,417 bytes | 80.4% |
| [Lean AX routine](../../../../../../Lean/BusyBeaver/ZFC/L2AxiomsPerm.lean) | 202,222 bytes | 10,091 bytes | 95.0% |
| [Rocq dominated implication](../../../rocq/rocq-extension/coq/215/DomRho8.v) | 921,691 bytes | 23,678 bytes | 97.4% |

The implication certificate reuses exact substitution instances of earlier
proved schemas and retains only the final theorem's dependencies: 674 of the
original 3,728 nodes. Lean checks the retained proofs directly; Rocq checks 780
instructions using a small interpreter with a generic soundness proof. Both
optimizers are untrusted proof producers.

The AX routine now composes existing macro contracts with one induction over a
156-entry word. A finite kernel check binds the word to the literal program;
symbolic evaluation proves the same complete register-state effect.

[Root iteration](../../../../../../Lean/BusyBeaver/ZFC/RMDagIteration.lean) and
[program transfer](../../../../../../Lean/BusyBeaver/ZFC/Dag219Bisim.lean) share their induction arguments.
Separating the program bisimulation from its legacy seed endpoint reduces the
current K215 import closure from 204 to 201 project modules. The legacy facade
and all four root interfaces remain available. The existing selection contract
also shortens `EnumPerm.gen_contract`.

The [Lean endpoint check](lean/README.md) validates all 201 current modules plus
14 additional legacy dependencies, then compiles both typed endpoint clients.
All ten axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`;
the clients have zero warnings. The
[Rocq check](rocq/README.md) recompiles all seven affected modules, obtains four
closed endpoint reports, and recursively checks the changed dominated-rule
module. These checks reuse hash-bound baseline objects; they are not new full
closure replays.

Local details and exact generation checks are retained for the
[Lean certificate](lean-rho8/README.md), [AX word](ax-word/README.md), and
[Rocq certificate](rocq/README.md). The original machine, certificates, attribution,
full-build receipts and failed-attempt history remain available. No axiom,
admission, or weaker theorem statement was introduced.

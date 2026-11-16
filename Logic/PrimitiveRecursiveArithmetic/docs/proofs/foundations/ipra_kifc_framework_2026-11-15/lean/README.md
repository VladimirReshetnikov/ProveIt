# KIFC Lean outline

The modules target the APIs inspected at ProveIt commit
`8649990597d73657bde480b6c389de7f85bc0cb0`.

- `KIFC/KernelCore.lean`: proof-producing local rules, implication contracts,
  proof schedules, and the exact `IPRA.ind` loop-certificate wrapper.
- `KIFC/BooleanBlueprint.lean`: reflected Boolean interface and bounded-fold
  contracts.
- `KIFC/SearchBlueprint.lean`: least bounded search proof contract.
- `KIFC/RelationalBlueprint.lean`: viability and stable-observer interfaces.
- `KIFC/GraphBlueprint.lean`: metalevel node kinds and kernel-facing compiled
  graph object.
- `KIFC/Examples.lean`: adapters for checked two-square and Heron derivations.
- `KIFC/Checks.lean`: intended axiom audit.

The environment used to create this artifact does not include Lean. These files
were therefore not compiled here. They contain no intentional `sorry`; the
blueprint modules expose structures and documented theorem targets instead of
postulating missing soundness axioms.

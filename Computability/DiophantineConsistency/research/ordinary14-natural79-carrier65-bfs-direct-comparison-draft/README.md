# Proposed direct natural-79 / Carrier65 no-zero comparison

This is an **unelaborated source draft**, not a completed iPRA proof. It
compares the natural-79 endpoint's `expression` at the compact symbolic ports
with `IPRACarrier65BFS943.expression` at the direct-BFS943 ports. The latter
is the 14-positive-variable Carrier65 syntax with its positive variables
encoded as natural variables through `positiveShift`. The endpoints use
different expressions and coefficient ports: this draft does not identify
their valuations, polynomials, coefficients, or external files. In particular, the
direct-BFS943 ports differ from the current displayed 2011 Carrier65 ports.
Sharing the Carrier65 graph does not prove equivalence to the historical
normalized quote or bind this statement to the physical page.

The source declarations selected for composition both state a native-theory
biconditional with exactly the same target:

```
nativeNoZero Natural79EndpointDraft.expression
  ↔ ∼mappedNativeRefutation embedding
nativeNoZero (positiveShift IPRACarrier65BFS943.expression)
  ↔ ∼mappedNativeRefutation embedding
```

These are object-language formulas claimed provable in `nativeTheory`; the
arrows displayed above summarize the `🡘` connective and are not Lean source.
`native_of_endpoints` makes both object-theory proof assumptions explicit and
proposes composing their two directions, with no common-port assumption.
`native_equivalence` applies the two endpoint declarations; its validity is
therefore conditional on those exact imports elaborating without unintended
axioms. The standard and equality-only reference variants use the existing
conversion declarations.

The draft additionally composes the natural-79 endpoint with
`IPRABoundedRhoZFC.zfcEquiv`, the same mapped Foundation consistency
translation used by the selected Carrier65 endpoint. It includes native,
standard and reference versions of that proposed translated comparison. This
common target does not itself bind the symbolic ports to the physical
`equation.pdf` coefficient bytes; the direct-BFS Carrier65 source explicitly
identifies those calibration checks as external.

The [196-module natural-79 overlay](../ordinary14-natural79-corrected-reflection-overlay/README.md)
is not materialized or built, and the Carrier65 source and its upstream
providers also require independent verification for this use. The simple
checker pins the relevant source statements and draft, checks the displayed
shared target and explicit positive shift, and records all seven unexecuted
axiom-report commands. It does not parse or elaborate Lean, validate imports,
check theorem or axiom dependencies, prove the endpoint assumptions or
establish a physical file binding.

An [independent source review](../../reviews/ordinary14-natural79-carrier65-bfs-comparison-independent/README.md)
checks the revised namespace opening, endpoint targets and composition
directions without elaborating the draft.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-carrier65-bfs-direct-comparison-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-carrier65-bfs-direct-comparison-draft/receipt.json
```

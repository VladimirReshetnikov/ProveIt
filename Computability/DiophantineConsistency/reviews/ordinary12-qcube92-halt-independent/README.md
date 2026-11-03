# Independent review of the 92-operation fixed-port halt-model theorem

The accepted Lean source proves three related statements in every model `V`
of `IΣ₁`, including nonstandard witnesses:

- The fixed-symbolic-port 92-expression has a zero at strictly positive
  coordinates if and only if there is `T : V` with
  `ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0`.
- The same model predicate is equivalent to a zero after the positive shift
  `x ↦ x+1` in every coordinate.
- The shifted theorem also holds with the four closed Lean byte recipes,
  using the checked `byteP_eq` equality.

The proof supplies the beta-positivity hypothesis from `CompactFixedBeta.bounds`,
composes the namespaced positive-zero bridge with the existing fixed-symbolic
model theorem, and uses the model's natural predecessor property for the
reverse shift. The 92-operation count refers to the unshifted positive graph;
additional coordinate shifts are not included. The result is a model-level
machine-run equivalence, not a Lean proof that iPRA proves consistency
equivalence. Its Lean byte recipes are not a theorem interpreting coefficient
files or a PDF.

The accepted author run exited zero with empty stderr and no warning or
`sorryAx`. All four named axiom reports contain only the Lean metatheory
axioms `[propext, Classical.choice, Quot.sound]`. The source, retained source
and runner snapshots, tool binary, logs and output object match the receipt.
Three recorded samples saw at most one Lean process and at least 18,524,376
KiB available memory; this is not continuous monitoring.

The independent checker rehashed all 1,291 currently selected union files,
including their symlink targets, before and after its other checks. The union
is exactly the earlier 1,288-object model selection plus `QCube92`,
`QCube92Model`, and `QCube92NamespacedExistence`; the old top-level binding
and existence modules are absent. It verifies the source-declared imports
and their selected hashes, and reruns the two read-only serialized-ancestry
reviews. It also rechecks the retained nonzero preflight exits and their
respective tail-overlap, extra-provider, and wrapper errors, as well as the
later failed duplicate-module Lean import. Those earlier observations are
failures, not evidence of a successful proof.

Run `python3 -I -S -B check.py` from this directory, or pass its path from
another directory. The captured review exited zero with empty stderr; see
`observations/stdout`. It relies on the retained absolute `/tmp` providers
and output objects, and no Lean process was started during this review.

This is an inspection of a single author kernel run and its selected-project
records, not a fresh independent Lean replay. Package-transitive and dynamic
imports and complete historical source-to-object ancestry remain inherited.
The JSON/Lean graph, external coefficient data, and any PDF remain outside
Lean's file semantics. The coherent internal iPRA endpoint remains open.

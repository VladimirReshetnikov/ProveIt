# Lean status

The Lean files in this directory are **formalization blueprints** targeted at
ProveIt's checked `ConciseIPRA` API. They were not compiled in this artifact
environment because no Lean executable or dependency closure was installed.

What is explicit:

- the complete trace-system data structure;
- term application helpers for arities 1--3;
- `BaseFm`, `StepFm`, `FinalFm`, `InvP`, `InvRunFm`, and `ResultFm`;
- the `TraceProofs` object-derivation interface;
- a detailed reduction of `traceReflection` to the already compiled
  `primitiveRecursionAt` theorem in the repository;
- demand, layered-relation, stable-observation, and shrinking module targets;
- two complete object-calculus cut combinators (`stableOfIndependent` and
  `stableOfLocalProof`).

Visible `sorry` placeholders mark the exact implementation gaps. No claim is
made that these files are kernel checked.

Recommended integration order:

1. Promote the checked `ObjectIteration.lean` and `ObjectObservation.lean`
   combinators into a common `ConciseIPRA.Finitary` namespace.
2. Compile `TraceReflectionRoadmap.lean` after replacing the central `sorry`
   with the `primitiveRecursionAt` adapter proof.
3. Implement canonical Boolean, pair, bounded-list, and rational libraries.
4. Complete folds/search, demand schedules, and path codes.
5. Complete relational and stable-observable endpoints.
6. Run `lake build`, source scans, and `#print axioms` on every public theorem.

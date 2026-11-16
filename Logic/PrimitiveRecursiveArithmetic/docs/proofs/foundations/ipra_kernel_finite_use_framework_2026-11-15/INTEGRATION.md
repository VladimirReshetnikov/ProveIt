# Repository integration notes

Recommended destination:

```text
Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/
  ipra_kernel_finite_use_framework_2026-11-15/
```

For long-term reuse, the two generic Lean modules could later move into a small
shared library under `Logic/PrimitiveRecursiveArithmetic/`, but only after they
compile against the canonical ConciseIPRA project and their names are aligned
with existing modules such as `ObjectObservation.lean` and
`ObjectCategory.lean`.

The package deliberately does not duplicate ConciseIPRA source files.  During
integration, resolve `import ConciseIPRA.PR` and
`import ConciseIPRA.NativeBiInterpretation` from the repository itself.

A sensible merge sequence is:

1. add the packet unchanged as an auditable research artifact;
2. compile `lean/KernelCompiler.lean` and commit any interface-only fixes;
3. compare its loop/stability lemmas with `ipra_stable_observables` and keep one
   canonical version;
4. replace the schematic `contractDAGReflection : True` in the earlier
   contract-compiler blueprint by a reference to `ProofBuild` plus generated
   schedules;
5. migrate theorem packets one at a time, filling the obligation records and
   recording genuine blockers as boundary formulas.

No upstream files were modified by this delivery.

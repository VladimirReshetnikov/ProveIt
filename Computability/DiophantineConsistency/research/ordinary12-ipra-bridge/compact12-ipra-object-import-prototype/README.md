# Serialized-import metadata probe

The bounded single-object diagnostic in `observations/attempt01` used
`Lean.readModuleData` on the compact-selected
`AdaptiveEquationSyntax2011.olean`. It exited 0 in 2.03 seconds and printed
these actual direct import entries:

```
Init
Init
DiophantineConsistency.CurrentKernelData2011
DiophantineConsistency.NaturalExpressionSemiring
```

The helper source and target object hashes were unchanged across that
invocation. The exact source, output and command receipt are retained. This
is a metadata diagnostic, not a Lean theorem, source-to-object audit or proof
that the 59-module integration rebuild cone is complete. The previous, larger
`import Lean` probe stalled and was interrupted; its evidence is retained in
the neighboring integration-build packet.

`scan.py` and `ReadObjectImports.lean` are a **draft, unrun** follow-on for a
bounded batched inventory of the pinned 441 endpoint objects. They attempt to
compare serialized project imports with pinned source imports, retain their
union in the dependency analysis, reject imports outside the pinned closure,
and detect newly affected nine-base objects that the current prepared overlay
did not omit. The script also checks the pinned overlay, source and object
hashes before and after use. It has not been executed, independently reviewed,
or shown to compute a complete Lean module closure; it must not be represented
as successful preflight or as permission to start the integration build.

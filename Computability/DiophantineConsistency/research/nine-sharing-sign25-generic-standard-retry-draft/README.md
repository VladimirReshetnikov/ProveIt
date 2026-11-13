# Generic standard endpoint namespace retry

The prior generic module failed because its imports do not provide the
`AdaptiveEquationSyntax2011` namespace, causing its combined `open` command
to fail before `mappedNativeRefutation` could resolve. This source-only retry
removes the two unneeded `AdaptiveEquationSyntax2011` and `ModelDifferenceRing`
opens from that module. The concrete specialization and translated sources
are otherwise unchanged. This is a minimal name-resolution repair; Lean has
not checked the retry, and later stages may expose further errors or resource
limits. Guarded preflight and independent review are required before a run.

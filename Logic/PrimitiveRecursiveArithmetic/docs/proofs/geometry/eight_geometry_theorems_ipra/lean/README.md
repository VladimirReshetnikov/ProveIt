# Lean artifacts

`FieldCertificates.lean` is a Mathlib-oriented collection of the compact
commutative-ring identities used by the report. It is intended as Layer B of
the formalization after adding geometric wrappers.

`IPRAFormalizationPlan.lean` targets the existing ProveIt library and checks
the names of the `PRAAx`/`TeqAx` bi-interpretation bridge. Copy it into a
checkout of ProveIt or add this directory as a source directory, then build
with the repository-pinned toolchain:

```text
leanprover/lean4:v4.32.0
mathlib v4.32.0
```

Suggested commands from the ProveIt root after integrating the files:

```bash
lake env lean path/to/FieldCertificates.lean
lake env lean path/to/IPRAFormalizationPlan.lean
```

These files were not build-tested in the delivery environment because Lean was
not installed there. They contain no `sorry` or `admit`, but they remain an
outline until checked against the pinned repository and connected to explicit
`PRAAx` derivations.

# Checked finite core

Run with Lean 4.32.0:

```sh
lean FiniteCore.lean
```

Or, with Elan and Lake installed, run `lake build` in this directory. The
project has no external package dependencies; it uses the standard library
bundled with Lean.

`FiniteCore.lean` contains checked host-Lean proofs of the finite
denominator-cleared error recurrence, a Boolean certificate implication,
finite iteration composition, and a finite Neumann residual identity.
`build.log` records the version, successful compilation, and kernel
dependencies. The file has no `sorry` placeholders and declares no axioms.

The complete implicit function theorem and a full object-iPRA derivation
remain the formalization work described in `BLUEPRINT.md`. Compilation of
the finite core should not be read as completion of those larger tasks.

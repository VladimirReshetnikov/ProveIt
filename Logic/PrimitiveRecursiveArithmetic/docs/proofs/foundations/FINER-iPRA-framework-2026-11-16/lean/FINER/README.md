# FINER Lean sources

These files target the pinned ProveIt API at commit
`64bc0e997df6b8dbdf43f5ac9b3d9f74b4047ee5`.

- `KernelWrappers.lean` contains only small wrappers around existing checked
  structural rules and is intended to elaborate once placed in the ProveIt
  Lake package.
- `TraceBlueprint.lean` states the intended one-induction trace kernel.
- The other files are **source-oriented blueprints**. Every unfinished proof is
  a visible `sorry`. They have not been compiler-checked in this artifact and
  are not claimed to be iPRA derivations.
- `CompilerBlueprint.lean` makes the final composition theorem concrete: once a
  generated package contains object-language acceptance and soundness proofs,
  the public theorem is just simultaneous cut.

Follow `../FORMALIZATION_PLAN.md` in dependency order. Do not publish a theorem
as verified until its final type is literally `Prf PRAAx ...`, the module has
no `sorry`, and the repository axiom audit has been run.

# Scope of the Lean verification

`TransferCore.lean` contains seven elementary lemmas used in the report. It compiled successfully with Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`; the actual output is `../validation/lean_core.log`.

The lemmas certify the general polynomial Bézout identity, absence of a common filter root, filter reconstruction, hinge convexity, weighted hinge convexity, finite positive-ramp convexity, and rank-loss algebra. Their printed dependency lists use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`, as needed).

They do **not** formalize the complete Mellin or moment arguments, the class-group census, the full upstream GRH development, or a new RH statement. There are no `sorry` placeholders or new axioms in this file.

With elan and Lake installed:

```sh
lake update
lake exe cache get
lake env lean TransferCore.lean
```

These preparation commands require network access. The compilation recorded in the delivered log used an already installed copy of the same pinned toolchain and Mathlib cache, via `LEAN_PATH`; it did not fetch a new dependency set. The supplied Lake project is a portable way to recreate that environment.

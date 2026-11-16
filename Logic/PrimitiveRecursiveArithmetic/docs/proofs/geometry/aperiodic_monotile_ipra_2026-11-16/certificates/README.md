# Certificate files

- `hat_data.json` contains the closed polygon and area constants.  It is checked by the
  Python verifier.
- `substitution_rules.json` contains the 29 placement recipe, child selections,
  substitution matrix, and spectral identities.  Type counts, the matrix, and the
  characteristic polynomial are checked by the verifier; the exact affine construction
  is executed for six generations.
- `coupling_certificate.json` is a structured specification of the finite-torus proof
  obligations.  It is **not** a complete enumerated local-case certificate.  The strip,
  alignment, and weak-to-strong lemmas are proved at the human level in the report and
  remain explicit Lean milestones.

The archive therefore separates closed computational evidence from the uniform theorems
that still need kernel formalization.

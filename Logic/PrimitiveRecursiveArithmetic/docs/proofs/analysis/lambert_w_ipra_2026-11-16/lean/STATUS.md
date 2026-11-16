# Formalization status

- `LambertWHostBlueprint.lean`: host-level definitions and theorem interfaces;
  contains `sorry` placeholders.
- `LambertWObjectBlueprint.lean`: object-language proof graph using the actual
  ProveIt names `PR`, `PTm`, `PRAAx`, `PRA.qfInd`, `NFm.ofPRA`, and
  `pra_iff_native`; contains `sorry` placeholders.
- No `axiom` declarations are introduced.
- The files were not compiled because no Lean/Lake executable was present in
  the artifact environment.
- The paper gives the mathematical proofs and the implementation order needed
  to discharge the placeholders.

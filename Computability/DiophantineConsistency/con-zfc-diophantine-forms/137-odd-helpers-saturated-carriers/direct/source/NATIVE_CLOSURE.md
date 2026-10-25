# Selected ordinary proof closure

This directory retains the mathematical dependencies actually used by the
new direct branch. It is not a reproduction of every historical manifest
or a claim to bundle the entire Lean build graph.

- UNIFIED_PRODUCT_PROOF.md: full square-output factorial fixed point,
  reciprocal CRT product, range decoding, and finite-refutation equivalence.
- DIRECT125_PROOF.md: exact residue-one reparametrization, weighted interval
  sign argument, signed Pell lowerings, and source calibration boundary.
- COFINAL_131_PROOF.md: cofinal square horizon, consecutive-product beta
  modulus and self-sized radix, with complete soundness and completeness.
- native_closure/architecture/proofs/FACTORIAL_CARRIER_PROOF.md: complete
  pairwise-coprime label weights, beta adjacency, unordered Horn-flow
  soundness, finite proof-tree padding and constructive completeness.
- native_closure/architecture/proofs/HYBRID_PROOF.md and
  DERIVED_LABEL_RANGE_PROOF.md: complete prime-power range and local/label
  majorant arguments, including explicit constants.
- native_closure/SHELL_ENCODING_PROOF.md: injective square-shell syntax
  recoding and preservation of the calibrated numerical calculus.
- native_closure/architecture/proofs/inherited/calculus.tex: explicit
  numerical C222 rules and the exact named calibration interfaces.
- native_closure/architecture/proofs/inherited/primitives.tex, crt.tex and
  ../shared_powers.md: ordinary arithmetic/Pell graph lemmas.
- native_closure/architecture/proofs/inherited/calibration/: authentic
  named Lean interface sources, calibration pins and ordinary flow proof.

The square-shell source is interpreted through its injective recoding to
the displayed C222 calculus, not by identifying its literal numerical
constructor coefficients with the older Cantor encoding.

The unchanged formal interfaces are KEndpoint.c222_iff_zf_refutation and
ConstructibleChoice.zf_refutation_iff_zfc_refutation. Their mathematical
calibration is inherited; no new end-to-end Lean certificate is asserted.
The final equivalence is an ordinary argument formalizable in ZFC.

SOURCE131_MANIFEST.json is retained as historical provenance only. Some
paths advertised by that historical archive are not in its repository
snapshot; this selected closure does not rely on those missing files.
The complete arguments needed here are in the concrete files above, and
the actual delivered file hashes, not that historical inventory, are the
binding in ../SOURCE_PINS.json.

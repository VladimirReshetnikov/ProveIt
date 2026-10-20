# Formalism-side research artifacts

The final 220-state decoder candidate preserves the original K221 theory. These files document independent formalism-side investigations, not additional assumptions in its calibration.

- `theory_findings.md` and `membership_quantifier_fusion_findings.md`: supplementary uniform proofs, native-code details, and descriptions of rejected logical/source routes. References to predecessor paths identify retained upstream provenance; exploratory machine files are not release candidates.
- `final_formalism_assessment.md`: complete mathematical proofs and exact scopes, including the full sorted-domain countermodel after deleting rho1 and the relative full-theory obstruction to deriving rho6 after its T replacement.
- `check_quantifier_fusion_countermodel.py`: Python standard-library checker for the entire four-element Boolean algebra. Run `python3 check_quantifier_fusion_countermodel.py`; it writes `quantifier_fusion_countermodel.json` beside itself. The checker rejects Python optimization because assertions are proof checks.
- `quantifier_fusion_countermodel.json`: recorded finite algebra result. This algebra does not model K; it refutes only the claimed standalone logical derivation.
- `formalism_source_experiments.json`: small retained measurements and postfix words for rejected source layouts. There are no verified candidate machines among these experiments.
- `check_source_reassociations.py`: independent standard-library checker for the actual two source rotations. Supply `--baseline`, `--seed`, `--final`, and `--output` JSON paths. It reconstructs both trees, checks all factor boundaries, and compares the entire guarded CFG.
- `source_reassociation_review.json`: source hashes and successful independent reassociation receipt.
- `weak_rotation_review.md`: independent proof of the source reassociation criterion and audit of the two actual winning rotations. Both actual rotations satisfy the stronger fully closed criterion.

The full sorted-domain model is established by the uniform mathematical construction in the report. It is not presented as an exhaustively enumerated finite model: it has countably many separate finite coordinate domains, with rapidly growing sizes.

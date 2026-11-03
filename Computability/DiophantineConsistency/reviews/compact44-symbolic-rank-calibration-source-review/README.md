# Source review: symbolic compact44 rank calibration

Reviewed commit `eb3daec9fb`. The final theorem
`CompactActualRankCalibration.symbolic_rank_calibration` is stated for the
actual model cast `(paramKernel rho : V)`. It retains the two hypotheses
`2*(590069*581197) < 581197^m` and `581197^e ≤ 581197^m`, as well as the
IΣ₁-model instances. For arbitrary model `R0`, it yields a Σ₁-definable
Boolean selector, the explicit positive and no-wrap support bounds, and the
stated congruence. Its equality transport from the checked alias uses
`kernelAlias_eq` in the correct direction; the separate alias unit theorem
supplies the modular inverse required by the generic controller theorem.

This is abstract calibration for the defined symbolic `Gamma` and `bsum`.
The theorem does not establish that the support positions are physically
safe dummy cells, that `Gamma` equals the packed-rank variation, that the
selector can be applied to a particular compact word, or that a graph zero
or iPRA derivation exists. The two hypotheses are explicit in this theorem;
a later chosen-power specialization must be assessed on its own evidence.
Retained coefficient bytes and display binding are separate.

[`audit.py`](audit.py) independently reconstructs the **entire** adapted
controller source from the prior source using the stated import and namespace
changes. It compares the bodies of `triangle`, `triangle_double`,
`triangle_succ`, and `le_triangle` with the original Cantor source and checks
the shared IOpen model context. The excluded `triangle_mono` is not used by
the controller source. It also checks the four prior unit objects, four
calibration source snapshots, compiler logs and output objects, and the
final theorem's axiom report. The adapted controller log has exactly the two
documented unused-section-variable and unused-variable warnings; the other
three stages are warning-free. The normal audit exited 0, and optimized
Python was rejected.

This is a single-author incremental build and a point-in-time source/artifact
review, not a paired Lean replay or a fresh transitive provider audit. The
runner recorded dependency listings but did not continuously freeze the
provider; package, project-transitive, dynamic and between-check ancestry is
inherited. The original `/tmp` objects are required to repeat object checks.

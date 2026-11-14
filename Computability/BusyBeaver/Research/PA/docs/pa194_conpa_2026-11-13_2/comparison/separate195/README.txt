Intermediate separate190 machine with 195 working states
=========================================================
This is a newly verified comparison point, not the main result. The main
result is ../../pa194/pa194.tm with 194 working states.

This machine has 67 AX readers and six compatible folds. It shows why
minimizing reader count alone is insufficient: PA194 uses 68 readers but
eight compatible folds. Both execute the exact same separate190 macro word.

Run: python build_verify.py
The builder needs only Python standard-library modules and the vendored
references. It checks all 4,780 primitive contracts on raw and folded tables.
Its ordinary logical calibration is the same separate-calculus and original
ten-entry command argument in ../../mathematics/pa194_calibration.tex.

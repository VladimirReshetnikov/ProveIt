# Sparse-source ten-integer consistency equations

The entry points are `METRICS.json` for all evaluator tradeoffs,
`VERIFICATION.json` for exact finite receipts, `SOURCE_AND_TAIL_PROOF.md`
for the source contract and dependency boundary, and `section.tex` for a
complete report-ready formula and proof section.

Run `python3 build_integer.py`, then `python3 verify_integer.py`.
Python and SymPy are required for the independent verifier. No upstream
Python script is imported or executed. Inputs are sibling sparse-packing
certificates and the sibling complete coherent coefficient tuple.

The ten-integer universal reduction is Sun's result. This package applies
it with a new sparse-support source, interior padding, shared homogeneous
source evaluation, and exact algebraic factoring. No smaller integer
variable count or globally minimal polynomial is claimed.

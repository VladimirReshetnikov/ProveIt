# Ten positive variables, degree 246

The complete equation is `equation.json`: ten strictly positive integer
inputs, 121 binary arithmetic operations, and exact total degree 246.
It uses the complete original compact44 tuple in `coefficients/`.

Read `PROOF.md` for the ordinary equivalence with finite syntactic ZFC
refutation, relative to the same source61/native/controller calibration
as the frozen parent. No new Lean/Rocq or internal-ZFC certificate is
claimed. This is a degree/cost tradeoff against the parent's 97-operation,
degree-254 equation, not a global simplicity result.

The new ingredient is the explicit polynomial center obtained by weighting
the fused radical by `8(X+1)^3` and taking two polynomial correction terms.
The exact center defect has weighted degree 34 instead of the old 42.
One coefficient proves the final degree without a genericity assumption:

    [J^116 x^29 i^10 Y^57 eta^32 F^2] N = -7*2^14*beta^116.

Run `python3 build_verify.py` to rebuild the graph and repeat 151 checks.
Python's standard library is sufficient. All finite checks passed in
normal and optimized mode; the mathematical proof is separate.

Files:

- `equation.json`: literal graph, paid counts, inputs, fixed ports.
- `PROOF.md`: full formulas, positive bounds, soundness, completeness,
  exact global degree, and inherited proof boundary.
- `build_verify.py`: builder, graph/constant checks, independent formula
  evaluations, exact center certificates, and degree transcription tests.
- `sparse_polynomials.py`: small exact coefficient-arithmetic engine.
- `center_defect.json`: all 52 terms of the exact local center defect.
- `RESULTS.json`: all check results.
- `source/`: pinned original graph and its ordinary source proof.
- `coefficients/`: the four coherent actual coefficients and binding.
- `LICENSE.UPSTREAM`: original repository license.

Frozen source: ProveIt `f4d8db99e060339f3306a04d507c35bc1d0d68c5`,
`Computability/DiophantineConsistency/candidates/ten-positive-gap-fusion`.
Polynomial-part centering itself is already used elsewhere in ProveIt;
the new claim is this concrete application and lower-degree equation.

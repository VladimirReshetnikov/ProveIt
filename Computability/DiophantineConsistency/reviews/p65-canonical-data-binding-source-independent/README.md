# Independent source review of the package-65 halt-side assembly

The reviewed theorem is `P65CanonicalHaltConverse.halt_positive_zero`, source
SHA-256 `3563e1fe528271f1bfebc38d83e810651d54a5adb702f02a4791d2d0e0863f74`.
This is a source review, not an additional Lean compilation or independent
verification of the imported object files.

For an `ORingStructure` model of IΣ₁ and an arbitrary internal `T`, the stated
assumption is that the first projection of `ArithmeticMachineRun215.run T` is
zero. The conclusion gives one `Fin 14 → V` tuple, all of whose coordinates are
strictly positive, and whose package-65 output is an `InternalZero` at exactly
`CompactSymbolicPortProjections.portsInt (paramKernel rho)`. There are no
additional rank-equality or port-equality hypotheses in the theorem statement.

The same `v14` is used for positivity, all five residuals, and the final output.
In graph coordinate order it is

`![j, Fv, αv, z, f, delta a * i, auxT, Xv - q, Y, τ - (ell + sY), eta, zeta, y - auxw, gammaOld + t4 - wX]`.

The `fin_cases` proof lists a strict positivity proof for each of those fourteen
entries. In particular, it separately proves positivity of `j`, `Xv - q`,
`delta a * i`, and each truncated subtraction. The residual proof applies
`P65ConverseAlgebra.residuals_zero` to `w := fun j => ι (v14 j)` and verifies
its hypotheses for that same valuation; the final `P65Graph.zero_iff` consumes
the resulting five residual zeros at `v14`. The graph's `output_eq` states that
its output is their sum of squares. The port projections `cp0` through `cp3`
and the graph register equalities connect the actual four ports and rank to the
halt-data construction; the source introduces no free replacement ports in
the conclusion.

The two external shim comparison scripts were run independently with isolated
Python and both returned success. The graph shim (SHA-256
`83e122b6ce29a9f9eeee5538ac0a8dff4962f470baef8f532e095fd0ed4399e1`)
matches the current canonical graph after the documented import replacements;
the arithmetic shim (SHA-256
`b80e2933eb70db9341898a8cb7cc44be7296d78892dbcb5e72362bcc5346e890`)
matches its canonical source after its documented import replacements. This
checks source text, not that the captured provider objects were rebuilt from
the current canonical dependency tree. The previously reviewed algebra packet
has SHA-256 `23d74ea1c92ec8d008069256719360ef2900639e8f89f5844a6ccd063a06566a`;
the positivity companion has SHA-256
`bfcecea98a254434a6bacd611e39fa99f0ef19857b5fd2150fdeae44c907802c`.

No correspondence defect was found in this source review. Its result is
conditional on the captured-provider Lean check and the source/object and
external-payload boundaries documented by the author. This model direction
alone does not establish the reverse direction, an iPRA proof of equivalence,
or the identity of this graph with the equation displayed in the PDF.

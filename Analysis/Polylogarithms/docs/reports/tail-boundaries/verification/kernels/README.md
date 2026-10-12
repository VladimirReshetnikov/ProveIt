# Bilinear and shifted-kernel verification

Run `python verification/kernels/verify_kernels.py` from the bundle root, or
run the script by absolute path. `--exact-only` omits numerical diagnostics.
The result files are written beside the script.

The exact suite checks the two cancellation equations symbolically, 144
rational finite-cutoff identities with arbitrary initial values, all 3,125
length-five divisor strings with multiplicities between −2 and 2, 72 rational
cutoff formulas for the two kernels, both rank determinant identities, and
four explicit evaluations. The arbitrary initial values deliberately do not
assume any claimed infinite sum.

The numerical suite checks 21 identities at 50 decimal digits. It compares
digamma/polygamma expressions with ordinary Laplace integrals, evaluates both
finite shifted kernels and Hermitian tails, compares the Gamma–Hurwitz
primitives with quadrature, and checks the exact rectangular upper endpoint.
The recorded largest absolute discrepancy is below 5.346e−51. These are
floating-point diagnostics, not interval-certified bounds.

The article gives the all-parameter algebraic and convergence proofs.

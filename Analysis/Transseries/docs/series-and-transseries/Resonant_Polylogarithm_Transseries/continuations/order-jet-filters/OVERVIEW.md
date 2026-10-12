# Order-jet filters: intake reconciliation, 12 October 2026

These are scope and finite-replay findings. The delivered article is the sole
base of this continuation and is preserved with all proofs, qualifications,
code, PDF and supplied records. Independent review of the complete analytic
package and canonical incorporation remain separate work.

## Relationship to the current sources

The parent `Resonant_Polylogarithm_Transseries/article.tex:231` already states
“Lattice kernel and exact lateral completion.” Its `thm:Gamma-kernel` at
line 357 assumes positive integer order. The new article differentiates that
completion into a polynomial evaluation dictionary at -log(n) +/- i*pi.
Its joint ideal and minimum degree 2N follow from conjugate pairs of distinct
roots. The separate degree costs depend on integer and half-integer resonance;
they must not be substituted for the simultaneous bound. The coefficient-field
restriction for algebraically normalized filters remains part of the statement.

The zero-order digamma/Borel kernel has its own continuation argument; it is
not obtained merely by removing the parent's positive-order hypothesis.
The exact zero-jump order curve retains a nonzero physical completion.
The global real inverse and its convergent small/large endpoint charts are
different assertions: neither the sufficient complex disks nor real monotonicity
proves an exact global complex inverse radius. The arithmetic inverse-average
defect specializes the existing nonlinear inverse transport mechanism.

The delivery could not inspect three older incoming archives. Those archives
now have preserved homes: the Lambert order-jet continuation under
`Mellin_Borel_Completion_q_Gamma_Critical_Reversion/continuations/lambert-order-jets/`,
the quadratic boundary-transfer continuation under
`Quadratic_Polylogarithm_Feedback_Boundary_Completion/continuations/critical-boundary-transfer/`,
and `Resonant_Lambert_Inverse_Transseries/`.
Their filed articles treat a q-factorial/double-pole family, quadratic-feedback
boundary inversion and a symmetric double-Lambert inverse, respectively.
Those models differ from the present F_s(x)=-Li_s(-exp(x)) order-filter problem.
This resolves the placement comparison, not every possible identity overlap
or a worldwide novelty claim. The existing canonical Lambert inverse results
retain their own stronger continuation scope. No established printed theorem
is retracted by this intake.

## Fresh replay

All six default verification groups pass on an isolated copy: 165 exact
assertions and 46 numerical assertions at 70 working decimal digits, with
Python 3.13.14, SymPy 1.14.0 and mpmath 1.3.0. Fresh group JSON and the captured
run are in `intake-verification/`; the delivered `data/` remains unchanged.
The numerical evidence uses the independent regularized integral as reference
where supplied, but is still floating-point evidence, not an interval proof.

For a fresh copy outside the repository, run:

```sh
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python code/verify.py --output-dir replay
```

Choose a new output directory on repeated runs. The authored PDF is preserved
without rebuilding; no collective manuscript was edited in this reconciliation.

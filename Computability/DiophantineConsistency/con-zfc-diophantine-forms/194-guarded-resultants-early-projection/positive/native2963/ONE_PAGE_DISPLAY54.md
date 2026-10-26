# The printed compact54 coefficient display

`OnePageDisplay54.lean` binds the coefficient formulas printed in
`candidates/one-page/equation.tex` to the native finite-data interfaces.

* `auxiliaryPhi_eq` proves the displayed geometric blocks equal the literal
  auxiliary-entry polynomial. The selector part uses the printed signed
  coefficients and the checked arithmetic ranks from `OnePageTuple54`.
* `target_factor` proves the finite Laurent refactoring
  `r^T * sum(c_e * (1/r)^e) = sum(c_e * r^(T-e))`, under `r != 0` and `e <= T`.
  Actual selector ranks are below 457; auxiliary positions are at most 1807.
* `displayedK_eq` proves the complete printed rational expression equals
  `NativeStencil54.rawWord r` for every nonzero natural radix.
* `support_recipe` identifies the printed interval union exactly. The ordinary
  subtraction defining `displayedMC` equals the actual nonnegative low port
  at `r = 2^89`, using its checked exact-subtraction identity.
* `mu_eq`, `displayedBeta_eq`, and `displayedMF_source` identify the other
  printed constants. The fourth source coefficient adds beta to the native
  high mask exactly once.

All powers remain symbolic; no proof expands the 434054-bit native kernel.
The generic geometric fraction identity has its necessary `x != 1`
hypothesis. The PDF itself defines `G` as a finite sum, including at `x = 1`.

`Lean/checks/OnePageDisplay54.lean` checks the universal identities and audits
thirteen public declarations. These identities bind the printed coefficients;
native tableau calibration and the internal object-ZFC consistency theorem
remain separate proof obligations.

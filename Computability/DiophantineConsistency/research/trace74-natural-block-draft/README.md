# Natural four-block bridge (unchecked draft)

The all-ring four-block identity is already checked. This draft proposes a
bridge to the natural-number block equation required by saturation, assuming
that the signed rank has a specified natural representative, `0<C<=q`,
`F<q`, `HP*J>=1`, and `q=beta*J+1`. The assumptions are individual bounds:
the desired reverse guard `F+C<q` is not assumed.

The first Lean attempt exited 1 because the source did not import the
model-arithmetic namespace; it accepted no theorem. Its exact source, runner,
logs, result and separately observed outer exit are in `observations/attempt01`.
The current source adds the missing `ArithmeticSaturation` import and the
runner pins its direct object; this revision has not been checked. In
particular, this draft does not show that a positive 74 graph zero supplies
any natural representative or range assumptions, the population bounds, the
guard, or the iPRA equivalence.

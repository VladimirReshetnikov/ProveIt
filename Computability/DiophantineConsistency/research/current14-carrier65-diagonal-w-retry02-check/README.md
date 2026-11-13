# Actual diagonal W coefficient: closed-goal retry

Outer session 42490 exited 0: the actual axis W coefficient −2 and exact
degree 2 compiled at arbitrary ports. The [independent terminal audit](../../reviews/current14-carrier65-diagonal-w-retry02-terminal-independent/)
passed; one unused-simp warning and no `sorryAx` were reported. The retry adds
`rfl` to close the concrete if-true coefficient goal remaining after the
preceding proof. The no-Lean preflight and [independent prelaunch review](../../reviews/current14-carrier65-diagonal-w-retry02-prelaunch-independent/)
passed. Both audited prior failures and
missing objects, direct providers and limits are pinned. The intended result
is actual diagonal W coefficient −2 and degree 2, not a whole-axis theorem.

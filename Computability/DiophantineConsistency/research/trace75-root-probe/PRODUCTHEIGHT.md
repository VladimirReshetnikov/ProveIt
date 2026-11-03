# Arithmetic-only small-product recovery

`Trace75ProductHeight.equality_of_height` proves in every IΣ₁ model that,
for positive `b`, the combination of `b*(X+t)*(t*X+1)<H` and the signed
divisibility `H ∣ b*(X−t)*(t*X+1)` implies `X=t`. It derives this using
the strict magnitude bound and positive factors; it does not cancel `b`
modulo `H`. The generic theorem has no graph, halt or iPRA conclusion.

This rebuild removes the earlier `Direct80GraphProduct` import and keeps
the other import and both theorem bodies unchanged apart from the namespace.
`run-productheight.py`, `observations/productheight-attempt01/`: Lean exit 0,
no warning/error; object
`/tmp/trace75-productheight-dj1cseev/Trace75ProductHeight.olean`, SHA-256
`53fc07fe56761edc1a8769bb96c350c4e845e99f8914bc4ccd2d698ed7944b49`.
The direct provider is pinned; full transitive/package ancestry is inherited.

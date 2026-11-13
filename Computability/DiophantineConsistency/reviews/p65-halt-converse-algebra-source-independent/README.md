# Independent source review: P65 halt-side residual algebra

The reviewed source `P65ConverseAlgebra.lean` has SHA-256
`23d74ea1c92ec8d008069256719360ef2900639e8f89f5844a6ccd063a06566a`.
The five algebraic implications match the displayed hypotheses: `A0`
uses `Y=q³ sy` and `r+ell+sy=tau`; the main residual uses `M=S q`,
`k=R+1+M t4`, `X=q tx`, and `gamma+tx=gamma0+t4`; `At` is exactly the
transport premise; `Aa` follows from `V=wa`, `yy=wa+u` and the stated
auxiliary norm; and `As` is the supplied strong equation.

The canonical graph source SHA-256 is
`78a40f3bab902668e739e0068407808d094780409a002326f9dd745c53656338`;
the shim source SHA-256 is
`83e122b6ce29a9f9eeee5538ac0a8dff4962f470baef8f532e095fd0ed4399e1`.
The separately rerun `check-shim.py` (SHA-256
`e5a5d8ee95532e2c5531d39b815d0923f1c7089fc46e7adf8dea8380dcdc68f7`)
exited zero, confirming the compared bodies are byte-identical after the
three import replacements.

This is a source and external-byte review, not a canonical-source Lean
replay. It does not establish that the premises are inhabited, the positive
coordinate witnesses exist, the strong-input scaling has been constructed,
or an iPRA endpoint follows. Provider and transitive/package ancestry are
outside this review.

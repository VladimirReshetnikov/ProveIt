# Halt-side algebra for the package-65 converse

`P65ConverseAlgebra.residuals_zero` proves over an arbitrary commutative
ring that all five package-65 graph residuals vanish under explicit
first-root, main-root, transport, strong-norm, auxiliary-norm, rank,
coordinate and carrier equations. These equations are the algebraic shape
of the canonical halt-side data used by `P72Converse`; this theorem does
**not** construct such data, prove their positivity, or state a halting or
iPRA equivalence.

In particular, P65's strong input is not simply the canonical ordinary
`i`: if the canonical norm is `f²−1=Delta*(i*c²)²`, then P65's required
input is `Delta*i`, so `(Delta*i*c²)²=Delta*(f²−1)`. The current theorem
takes the final strong equation as a premise; no witness mapping is yet
claimed. The first-root choice uses `r=tau−(ell+sy)`, and the transport
quotient is carried by the separate positive coordinate `z`. The main
carrier equation uses `k=R+1+M*t4`, `X=q*tx`, and
`gamma+tx=gamma0+t4`.

The current canonical `P65Graph.lean` depends on a promoted `Compact44`
module unavailable in this captured provider. `P65GraphShim.lean` uses
three direct imports instead; its entire remaining body is byte-identical
to the pinned canonical source. `check-shim.py` verifies this exact source
comparison, but it is an external byte check, not a clean build of the
canonical module. The checker SHA-pins both files and rejects optimized
Python.

Lean 4.32.0 compiled the shim in actual session 85743, exit 0, and then
compiled `P65ConverseAlgebra.lean` in actual session 97720, exit 0 without
warnings. The assembly theorem reports only `[propext, Quot.sound]`; the
shim reports only `propext`, `Classical.choice`, `Quot.sound` as applicable.
The first assembly attempt failed because `M` was not rewritten to `S*q`
inside one hypothesis and was rejected. Both checks used captured
providers: `LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`,
`timeout 120`, `-M3000 -j1 -DElab.async=false` and this directory as
`--root`, producing `/tmp/P65GraphShim.olean` and
`/tmp/P65ConverseAlgebra.olean`.

```text
canonical P65Graph.lean         78a40f3bab902668e739e0068407808d094780409a002326f9dd745c53656338
P65GraphShim.lean               83e122b6ce29a9f9eeee5538ac0a8dff4962f470baef8f532e095fd0ed4399e1
P65GraphShim.olean              7bd2902eeffa586418aedef1aded667be68d32c0aeb6f3946a09d277db3dc19c
P65ConverseAlgebra.lean         23d74ea1c92ec8d008069256719360ef2900639e8f89f5844a6ccd063a06566a
P65ConverseAlgebra.olean        609392439dd1fd47ac947fd380be490e9f8a43a33ca80c6b842db0116c33bac7
```

Captured provider, search-path, source-to-object and transitive/package
ancestry are not independently authenticated. Next is the model-level
canonical halt-data construction and positivity proof, followed by a
canonical-source iPRA endpoint and clean replay.

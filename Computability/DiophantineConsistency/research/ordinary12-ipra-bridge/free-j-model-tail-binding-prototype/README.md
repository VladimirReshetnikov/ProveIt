# Natural auxiliary seed to the exact free-J ordinary factor

`ordinary_unit_of_model_auxiliary_seed` proves that the actual free-J graph's
third signed factor represents `+1` at a specified valuation in any `IΣ₁`
model. It assumes the following model-natural seed equations and inequalities:

```
1≤f,  w≤y,
a=XY+Y,  c=(η+ζ)Y+η,  Δ=(a+1)(a+3),
f²=1+Δ(ic²)²,  f²cT=w+c+f²R,
(Δic²)²w²+y²=1+(Δic²)²y².
```

The same graph valuation must bind slots 3, 4, 5, 6, 8, 9 and 10 to
`f−1,T,X,Y,η,ζ,Δi+(y−w)`, respectively, and the actual graph `rankExpr` must
evaluate to `ι(R)` in the model difference ring. The proof checks the exact
graph `Q`, `d`, `V`, and `n` shapes by reflexivity, derives `V=ι(w)`, maps the
natural seed equations into the difference ring, and applies the checked
normalized-to-ordinary tail bridge.

The subtraction in slot 10 is essential: the auxiliary norm gives the tail
witness `u=y−w`. The former candidate `Δi+w` is not justified by this
argument. The theorem assumes `w≤y`, the stated equations, the valuation and
rank binding; it does not construct them or prove a positive graph solution,
fixed-port calibration, or an iPRA proof.

Bounded single-author attempt 01 exited 0 in 7.951 seconds with no warnings or
`sorryAx`. Source SHA-256 was
`09b25e8f5494eae73b7987d63b27b5621234698e878a7fba725bf0b85810f611`;
object `/tmp/free-j-model-tail-binding-author-59thxrcy/FreeJModelTailBinding.olean`
had SHA-256
`a4532585b5bcce9987bf50f3b62ea3dc23907b15c4e5d9f9f68c52cce1594be2`.
All three selected provider overlaps matched; 1,181 live provider files and
direct/named transitive bridge object companions were unchanged. This is not an
independent replay or a full audit of inherited provider, package-transitive,
or dynamic ancestry. Lean reports `propext`, `Classical.choice`, and
`Quot.sound` as metatheoretic dependencies.

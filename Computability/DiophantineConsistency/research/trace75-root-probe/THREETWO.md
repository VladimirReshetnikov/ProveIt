# Trace75 main-three / first-two algebra

`Trace75ThreeTwo.graph_three_two_algebra` is checked in every `IΣ₁` model for
arbitrary natural ports with beta positive and a positive trace75 valuation
whose Lean ring value is zero. Given an explicit first-ordinate index `n` and
the explicit main-ordinate-at-three hypothesis, it derives `n=2` and

```
k = 8*X*Y² + 4,
c+1 = 4*(A+1)²,
ι(eta) + 4*ι(Y)²*(ι(X)*(2*ι(Y)-ι(X)-2)-1)
  = 4*ι(Y)*(2*ι(X)+1)+3.
```

`A=X*Y+Y`; `ι` is the embedding into the model's difference ring. The third
identity is the paper's factored n=2 eta equation, with signed intermediate
subtractions in that ring. The theorem does not exclude the main index-three
hypothesis or assert the gap/positivity conclusions needed to do so; no halt,
trace74 guard, iPRA, or Lean file-binding theorem follows.

Accepted source `Trace75ThreeTwo.lean` SHA-256
`67534c9068fd8152f18387c946c8eed4c451747c03eb7cc5dd55bd7a81625f33`;
`run-threetwo.py` accepted `observations/threetwo-attempt01/`, object
`/tmp/trace75-threetwo-v00ksoob/Trace75ThreeTwo.olean` SHA-256
`c6526cbc36bbc37365527ea028d25e46e514bca5461ef2a803e3d489725f7053`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
Selected direct providers are pinned; transitive project/package, historical
source/object and dynamic ancestry remain inherited.

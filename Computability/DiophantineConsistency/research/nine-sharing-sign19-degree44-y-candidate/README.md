# Sign19 degree-44 Y elimination: external candidate

This external source-only candidate removes the old sign20 Y coordinate at
index 15 using its positive row

```
Y = (v8 + 1) * (beta * (v1 + 1) + 1)^3.
```

Substitution into the other 10 residuals and reindexing yields 19 natural
witnesses and leaves the distinguished input coordinate zero unchanged. For
natural inputs and nonnegative beta the replacement is natural; reverse
coordinate recovery and all residual transfers remain to be proved in the
relevant models. The sign20 symbolic iPRA endpoint has passed independent
terminal audit; this sign19 transformation has no Lean bridge, expression or
endpoint.

The retained residuals have syntactic total degree at most 22. Specialize
v1=v8=v9=v11=t and all other witnesses to zero; the N0 coefficient of t^22
is exactly `-beta^14` in `Z[t,beta]`. The square-sum's t^44 coefficient is a
sum of integer squares at least beta^28, so its exact external fixed-port
degree is 44 when beta is nonzero. The retained beta bytes decode as a
positive unsigned big-endian integer, with their inherited hashes checked;
this is not a Lean interpretation or byte-binding theorem.

Run from this directory:

```
python3 -I -S -B build.py --check
python3 -I -S -B check.py
```

The author checker verifies the AST substitution, degree witness, port hashes
and finite natural-lift controls. Finite controls are not an all-model proof.
This variable/degree tradeoff is external evidence only: no Lean degree,
Lean/JSON binding, iPRA endpoint, or nine-variable reduction is asserted.
The [independent external audit](../../reviews/nine-sharing-sign19-external-independent/README.md)
passed; the candidate packet is frozen.

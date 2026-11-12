# Residue main balance: fact-level q divides 3X draft

This source proposes a model-arithmetic projection step from an **explicit
oriented main balance** and exact-index decomposition. No declaration or
provider has been elaborated by Lean. The theorem does not assume Bézout and
does not conclude that X is a q-power or that `q∣X`.

For model naturals `q,X,Y,c,k,R,gamma,main,s,w`, the hypotheses are
`q>0`, `s>0`, `Y=q*(q*q)*s`,

```
k = R+1+4*(X*Y*Y)*w,
a = X*Y+Y, H = 3+4*a, U = Y*q*q,
U*main + H*k = U*(X+a*c) + H*(U*gamma+X*Y*q+R+1).
```

The proof proposal works in the model's signed difference ring. It rewrites
the balance to obtain `U ∣ H*X*(Y*q)`, cancels the positive factor `Y*q` to
get `q∣H*X`, uses `H=3+4Y(X+1)` and `q∣Y` to get signed `q∣3X`, and calls
`Trace75IntegralTransport.natural_dvd_of_signed` to reflect the final result
to model naturals. No unproved coprimality cancellation is hidden.

The actual graph must still supply the oriented **residue-adjusted** main
balance, the exact index decomposition, positivity, represented ports and
all casts in one model. The source-only exact-index and main-congruence drafts
are candidates for those inputs, not authenticated compiled providers. This
packet makes no claim about a fixed compact K, physical port/PDF bytes,
power recovery, parent calibration, an internal iPRA endpoint, or a global
minimal equation.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue-three-projection-model-draft/check.py | cmp - research/ordinary13-residue-three-projection-model-draft/receipt.json
```

The bounded read-only check pins the source interfaces and controls the exact
ring certificates on finite signed integers. It never invokes Lean or stages
artifacts, and it does not establish the unbounded model theorem.

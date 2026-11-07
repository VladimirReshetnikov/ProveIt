# Local divisibility obstruction in the sign26 Nt row

This source-pinned, external check shows that coordinate `v4` occurs in the displayed 26-witness seed only in residual `Nt`. With `a=beta*(v1+1)`, `q=a+1`, `n=v2+1`, `t=v3+1` and `H=K0+v9+1`, the audited seed has `Nt=H*(q−n−t)−n−a*v4`. Thus simply dropping `v4` and the Nt equation discards a divisibility condition.

For any integers `beta≥2` and `K0≥0`, set `v1=v2=v3=0`, choose a positive integer `h` with `beta*h≥K0+1`, and set `v9=beta*h−K0−1≥0`. The actual source Nt polynomial then has the exact identity

`Nt = beta*(h*(beta−1)−v4)−1`.

It is congruent to −1 modulo beta for every integer v4 and therefore cannot vanish. Such an h always exists, for example `h=ceil((K0+1)/beta)`. The checker verifies the source occurrence and exact formal integer-polynomial identity, as well as finite arithmetic controls. These controls do not replace the general modular argument.

This is **only a local obstruction to discarding Nt**: it does not assert that any of the other 16 residuals vanish under these choices, rule out reusing a quotient from other constraints, establish a full-system counterexample or prove a 25-witness lower bound. No Lean theorem or model endpoint is claimed.

An [independent review](../../reviews/nine-sharing-sign26-nt-divisibility-independent/README.md) checked the identity with degree-bounded interpolation and confirmed its local scope.

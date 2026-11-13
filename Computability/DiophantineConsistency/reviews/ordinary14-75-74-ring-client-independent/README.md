# Independent review: 75→74 guard-shift ring client

**PASS at source and exact ring-algebra scope.** The literal graph DAGs show
that the four restricted factors F0, F1, Fa and Fs are identical and omit
slot h. The shared rows give `b=J*beta`, `q=1+b`, `qF=q−F`,
`C=qF−alpha`, and `X=q*w`. The 75 guard is
`1+C*(X+K)−F−b*h`; the 74 guard at the updated h+1 is the same polynomial.
The checker verifies that identity by sparse integer-polynomial arithmetic,
verifies both literal product outputs, and exercises 600 independent full
assignments over rings modulo 4, 12 and 17. It reproduces the author receipt.

The source statements have the correct direction: updating slot 13 by one
preserves all four restricted factors and the guard, hence the complete output.
This is a proposed source proof over arbitrary commutative rings; `simp`,
`ring`, output rewriting and the graph imports have **not** been elaborated.
It does not prove positivity of the reverse coordinate, obtain any factor
units from a zero, bind a model provider, prove the iPRA endpoint, or establish
physical-byte/PDF binding. No Lean run was performed.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary14-75-74-ring-client-independent/check.py | cmp - reviews/ordinary14-75-74-ring-client-independent/observation.json
```

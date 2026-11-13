# Nonsquare free input under q-cube and transport constraints

Replacing the shared multiplication `f*f` by a free positive input `h` would
save an operation, but the two norm equations do not by themselves force `h`
to be a square. This example strengthens the separate small-parameter
[obstruction](../p64-free-square-obstruction/README.md): it also satisfies the
actual q-cube coordinate relations and positive transport equation at the
smallest possible `q`.

Take

```
q=3, beta=2, J=F=alpha=w=s=z=1, K0=2,
Y=q³*s=27, X=w*q=3, a=Y*(X+1)=108,
Delta=a²+4a+3=12099.
```

Define `(g,c)` by `(g+c*sqrt(Delta))=(110+sqrt(Delta))^12099`, and put

```
eta=15,   k=(c-eta)/27,   zeta=k-eta,
i=1,      h=1+c⁴/Delta.
```

The bounded exact verifier checks that these are integers with positive
`k,zeta`, that `c≡15 mod 27`, and that `Delta` divides `c⁴`. It verifies

```
g² = 1+Delta*c²
Delta*(h-1) = i²*c⁴
c = k*Y+eta
(K0+w)*(q-F-alpha)-F-z*(q-1) = 0.
```

It also checks `h≡6 mod 7`; since the square residues modulo 7 are
`0,1,2,4`, `h` is not a square. This shows that recovering a square `h` needs
more than these two norms, transport and q-cube parameter relations.

**This is not a graph zero or a counterexample to an existential equivalence.**
In particular, the verifier does not establish the graph's main residual
`M=0`, the first norm, or the auxiliary-unit residual. The scalar main Pell
norm alone is weaker than the full `M=0` relation, which also depends on rank
and witness alignment.

An [independent review](../../reviews/p64-free-square-q3-independent/README.md)
recomputed the Pell power by binary exponentiation and certified nonsquareness
using an exact integer square root. It retains the same partial-constraint
scope.

[`check.py`](check.py) uses 12,099 exact Pell iterations, aborts if the
Pell operands exceed 100,000 bits or the fourth power exceeds 400,000 bits,
and certifies nonsquareness modulo 7 without a large square-root operation.
It rejects optimized Python. Its [recorded output](result.json) was produced
with exit 0. Reproduce from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-free-square-q3-obstruction/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `d5abfe97f4a1716bde015d03d41366024e28057239dc4dab12d6a2ec2dc41e6a` |
| `result.json` | `a4c258b0884732c708936ddd3220fd8348334493b769ad6820c0a7eaf4f40a0b` |

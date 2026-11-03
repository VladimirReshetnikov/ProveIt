# Trace75 adjacent Pell quotient

`Trace75Adjacent.graph_adjacent` joins the actual trace75 K2 root extraction
to the existing internal adjacent-Pell descent. In every `IΣ₁` model, for
arbitrary natural ports with `0 < beta` and strictly positive witnesses,
a zero of the Lean trace75 ring value in the model's difference ring produces
one coherent tuple of positive `tau,f0,V0,y` and a natural `Z0` such that

```
E = tau²,     1 + Delta*U²*E = f0²,
V_register² = ι(V0²),    Z_register² = ι(Z0²),
Z0 = (M*tau*f0)*y,    Q*V0² = 1 + (Q-1)*y².
```

Here `Delta,U,E,M,Q` are the explicit actual trace75 model values defined in
the source; `V_register,Z_register` are the signed difference-ring graph
registers, and the final subtraction is model natural truncated subtraction,
with its positivity established in the proof. This is a necessary condition
for a zero, not a converse, machine halt theorem, trace74 guard, iPRA result,
or formal binding from the JSON/constant bytes.

Accepted source `Trace75Adjacent.lean` SHA-256
`de87a2684decba1bac16e9dd9d41df45ca53f25fd17bf21e3ee12c8a7afb067c`;
`run-adjacent.py` accepted `observations/adjacent-attempt01/`, object
`/tmp/trace75-adjacent-4nlbt6ev/Trace75Adjacent.olean` SHA-256
`f8b22b6107778dd98a51e6aa356d8190a0be377c811bceeff43dfcd1b19f17ea`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
Direct selected imports and the adjacent descent providers are pinned with
resource sampling and the 8-GiB/two-Lean guard. The selected namespace overlay
comes from the first applicable producer root; package, project-transitive,
dynamic and historical source/object ancestry remain inherited, without a
complete selected-closure audit or independent replay.

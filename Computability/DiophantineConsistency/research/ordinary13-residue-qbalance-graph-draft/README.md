# Actual residue graph: conditional oriented q-balance

These are **unelaborated source drafts**, not Lean-verified theorems or an
iPRA endpoint. `ResidueQBalance` proposes a natural model calculation from
an oriented actual-root balance and exact index decomposition. Write

```
a = X*Y+Y, H=3+4*a, U=Y*q², Y=q³*s,
k=R+1+4*X*Y²*w, W=4*X*q*s*w.
```

Substitution yields `4*X*Y²*w=U*W`. Cancel the common nonnegative
`H*(R+1)` from the oriented balance, then cancel the **positive** factor
`q*Y`, to obtain

```
q*(main+H*W) = q*(X+a*c+H*gamma)+H*X.
```

No q∣X, sign assumption on a difference, coprimality or Bézout premise is
used. The first source states positivity of q and Y explicitly. The graph
source proposes to obtain them, the positive actual main root and the exact
index witness from the existing source-only 13/90 clients. Here
`s=v 7+1`, `X=v 6`, `gamma=v 12`, eta=`v 9+1`, and
zeta=`v 10+1`; the same `w` returned by the index client appears in W.
Its explicit assumptions are graph zero, J/beta/X positivity, the positive-C
inequality and rank window.

The optional `actual_power_of_pell_coordinates` client takes the derived
balance as an input **together with** the recurrence first ordinate at the
paired index and both main x/y coordinates for the **same main**. The other
inputs are `q≥46`, `X>0`, `q∣3X`, `13≤n` and `2n=R+1`. It proposes to
apply the previous sign-free growth and power-recovery client; it makes the
rewrite `a=Y*(X+1)` explicit. In particular, the exact-index client's n must
be identified with the first-ordinate index, and the positive main returned by
orientation must be tied to the x-coordinate by the actual graph norm. Those
bindings are not supplied here. Nor are the fixed compact-port model casts,
q≥46 bound, complete provider compatibility, graph-to-endpoint bridges,
axiom inspection, or an eta-zero extension. All inherited graph and model
source obligations remain open.

From `Computability/DiophantineConsistency`, run
`python3 -I -S -B research/ordinary13-residue-qbalance-graph-draft/check.py`.
This pins the input source bytes and verifies finite integer polynomial
identities, index wiring and explicit witness syntax. It does not run Lean.

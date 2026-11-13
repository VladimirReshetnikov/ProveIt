# Independent review: conditional reverse graph construction

`TenPositiveScaledReverseGraph.graph_zero_of_source` is a semantic theorem in an arbitrary `ORingStructure V` satisfying `IΣ₁`. It quantifies over a natural parameter tuple `p : Fin 4 → ℕ`, a model valuation `v : Fin 10 → V`, and model values `r,eta,zeta,t`. It assumes all ten source coordinates positive, `0<(p 0:V)`, and `0<r`; the mask and transport equations

```text
v 1+v 2 < q p v
((p 1:V)+v 5)*(q p v-v 1-v 2) = v 1+b p v*t
```

where subtraction is the natural-model subtraction; the rank/phase/power/size facts

```text
rankNat p v=2*r+1     (2*r+1)%4=3
X p v=Exp.exp (2*r+1)     72*r<X p v+1;
```

positive input `eta,zeta`; and both explicit unscaled Pell interval equations

```text
ycoord (2*r+1) (Y p v*(X p v+1)) =
  2*ycoord (r+1) (2*(X p v*Y p v*Y p v-1)+1)*Y p v+eta
2*ycoord (r+1) (2*(X p v*Y p v*Y p v-1)+1)=eta+zeta.
```

The first unscaled ordinate parameter above has no trailing `-1`; this is distinct from the scaled ordinate parameter in the construction. These are premises, not consequences established by this declaration. In particular it does **not** assume a 90-graph zero or prove that one supplies them. There is no numerical pin on `p 1`, but it remains constrained by the displayed transport premise; the conclusion uses the same full tuple `p`.

The precise exported conclusion is

```text
∃ w : Fin 10 → V,
  (∀ j, 0<w j) ∧ InternalZero (graph (integerPorts p)).output w.
```

The proof constructs the witness as `![v 0,v 1,v 2,i,T,v 5,v 6,n,eta',zeta']`, with `i,T,n,eta',zeta'` among one application of `reverse_data`; the fresh scaled interval witnesses are not asserted equal to the source `eta,zeta`. It preserves the source q, X, Y, rank and transport inputs, binds the 80 graph E, A, Q, V, Z fields to the coherent data, and applies the exact graph output-parts theorem. **The current theorem signature does not export equalities between w and the retained coordinates.** Those properties are facts about the witness constructed in the source proof and would need a strengthened conclusion if a downstream theorem needs to use them directly.

This is a conditional model-level 80-graph existence theorem for an arbitrary `p 1` satisfying transport. It is not an unconditional 90-to-80 graph implication, machine halt equivalence, binding to external JSON/PDF coefficients, or a syntactic iPRA proof. The known external K0-byte distinction is not resolved by this theorem.

`check.py` examines the accepted `observations/graph-attempt09/terminal.json`, current/copy source, runner, logs and output object, and independently checks the first resolved object for each of the five source-direct imports against the runner's explicit pins. The imported reverse-data, graph output-parts and scaled-start hashes match the independently reviewed packets. All exact paths and hashes are in `check-output.txt`. The accepted source has no `sorry` or `admit`, and the log reports `[propext, Classical.choice, Quot.sound]` with no error, warning or `sorryAx`. Earlier failed scratch attempts, some containing `sorry`, are not accepted evidence. Accepted object SHA `b9c5f5fd35821e237cb3995b0dd34311b552147c26f2b0d58ad0c82e23d4c107`; source SHA `4e08225410c6070945b0f21e9dcc3b0471d4f6d69802f3472851cc42687c5925`.

No Lean replay was performed. The direct-import receipt does not establish all transitive selection, source-object ancestry, package or dynamic-library provenance.

# Independent review of the 76 independent-`y` argument

This read-only review inspected the paper argument in
[`p64-qcube76-independent-y-analysis`](../../research/p64-qcube76-independent-y-analysis/README.md)
at SHA-256 `a78f6014d6fe80f5ff355ade32295f4f703db4e4b769ed0fe1c91f06a49d2574`.
No Lean theorem or zero witness was produced in this review.

The main-root theorem's positive-beta and `F≤q` hypotheses are supplied by
the transport equation on a positive zero, and the `q³ | Y` hypothesis by
the lifted witness `Y=q³s`. Given its natural root `g`, the square-window
argument correctly excludes `2≤c<2(a+2)`; together with `c≥3` it implies
`Delta<c²`. Combining that bound with the strong norm yields `f²>c+1` as
stated.

From the auxiliary norm and `y>0`, the proposed reverse map has `V²≤y²`.
Equality reduces the possible obstruction to `V=y=1`, which would imply
`f² | c+1`, contradicting `f²>c+1`. For the forward map, if old `V+e=0`,
the same norm would force `A*V²=1` despite `A≥2`; choosing its positive
absolute value therefore preserves the square. Existing `P72Aux.ι_absdiff_sq`
may help construct that square in the model difference ring, but its use,
the required positive natural witness, and all graph-specific residual
bindings still need explicit Lean proofs.

The review assumes the imported model theorems and their stated hypotheses;
it does not independently replay their dependencies, prove the resulting
same-zero equivalence, establish an iPRA endpoint, or authenticate external
coefficient and display bindings. The reviewer authored the separate graph
candidate, so this is independent of the *argument author* but not an
independent audit of the graph builder.

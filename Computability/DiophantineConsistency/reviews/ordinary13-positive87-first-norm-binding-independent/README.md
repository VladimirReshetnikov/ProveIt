# Independent source review: positive 87 first-norm binding

This reviews `research/ordinary13-positive87-first-norm-binding-draft/`
against the exact 87 graph, the unscaling transfer and signed quotient source.
No Lean, builds, staging or provider replay was performed. The receipt pins
those sources and reproduces the author's checker output.

The literal graph has natural witness coordinates J at 0, Y at 7, r at 8,
eta at 9 and zeta at 10; the source takes the four ports as natural `p` and
casts the **same** p to integer graph ports. Set `b=J*(p 0)`,
`h=(1+b)*((1+b)*(1+b))`, `k=eta+zeta` and
`ell=X*Y*(Y*k)`. The receipt checks the exact named first-root rows, the
returned graph fields, and computes their root and first-residual expressions
as polynomials in the free ring with the actual signed Bt as an opaque field:

```
Z = h*b*(ell+k+r-k*Bt)+Y*b-h*Bt,
A0 = Z²-(h*b)²*(1+ell*(ell+k)).
```

The graph's `ell=(X*Y)*(Y*k)` equals the displayed natural expression by
associativity. These algebraic checks do not validate source cast reduction
or Lean's `simp`/`ring` scripts.

The proposed `cut_of_zero` first extracts A0=0 from the actual 87 output's
four squares, then supplies the same graph root, Bt and natural radicand
`1+ell*(ell+k)` to `ScaledFirstCut`. `forward_norm_binding` chooses beta as
`(p 0 : V)` and cites `P72Root.cast_port` for the exact integer-to-model port
cast. Its source statement is `ForwardNormBinding (intPorts p)` for an
arbitrary *natural* port tuple p. The subsequent proposed
`forward_graph_cut` applies the existing conditional unscaling client. The
quotient helper's signature needs positive Y and the scaled signed norm; it
does not require beta to be strictly positive. A natural tuple and beta cast
remain essential to this particular source binding.

This client is a proposed discharge of the **87→84 forward norm cut**, not a
proof of the reverse positive-root cut. Its `root_form`, `first_form`,
sum-of-squares extraction, casts, inherited signed divisibility/reflection,
source/object providers and axiom commands are all unelaborated. The reverse
84→87 witness, exact endpoint bridge and physical compact-port/PDF binding
remain separate open obligations.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive87-first-norm-binding-independent/check.py
```

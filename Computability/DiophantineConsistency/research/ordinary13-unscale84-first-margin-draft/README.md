# Unscaling first-root strict margin: fact-level draft

`UnscaleFirstMargin.lean.src` is an **unelaborated source proposal**, not a
checked Lean theorem, graph-zero map, provider replay or iPRA endpoint. It
isolates the strict first-root margin needed for a positive 84→87/36 witness.

The first theorem states the general inequality in an arbitrary intended
IΣ₁ model, for model-natural tau, ell, k and s:

```
tau² = 1 + ell*(ell+k),   3*s ≤ k,   s ≤ ell
    imply ell+s < tau.
```

No positivity assumption on s or ell is needed beyond model-natural
nonnegativity. The difference-ring proof adapts the **private** `tau_gt`
lemma in [`P73Converse.lean`](../../Lean/DiophantineConsistency/Compact44/P73Converse.lean),
attributed by repository `git blame` to Vladimir Reshetnikov, commit
`0b43cf4a7750f861bacc45ab3f18dccd4ec10034`. Since that source lemma is
private, this is a separate proposed declaration rather than an import of it.
The mathematical inequality follows from

```
1+ell*(ell+k)−(ell+s)² = 1+ell*(k−3s)+s*(ell−s) > 0.
```

The displayed subtraction is in the associated signed difference ring, not
model-natural truncated subtraction. The source uses casts and ordered-ring
inequalities as in the attributed proof. Its model instances, coercions,
`nlinarith` and all imports remain untested.

`margin_of_first_norm` specializes the lemma to `ell=m*k` and
`tau²=1+m*(m+1)*k²`, with the explicit hypotheses `s≤m` and
`8*m+4≤k`. It does not require m or s to be strictly positive. The
`qcube_margin` specialization additionally assumes

```
1≤q, 1≤X, 0<s, Y=q*q*q*s,
8*X*Y*Y+4≤k,
tau²=1+(X*Y*Y)*(X*Y*Y+1)*k*k.
```

It proposes `X*Y*Y*k+s<tau`. These are all fact-level premises; in
particular the graph zero, model beta/port casts, positivity, first-norm
quotient, and large-k source must be bound separately. No equality between
distinct first-root witnesses is asserted. Once a graph client supplies
those facts, this inequality can justify the natural positive difference
`tau-(ell+s)` in the fresh 87/36 root construction; a positive represented
first-carrier quotient and the graph identity remain separate obligations.

The deterministic receipt pins the exact private source and actual 84 graph
rows, proves the displayed polynomial identity symbolically, checks two
boundary examples showing the need for the general lemma's inequalities,
and checks a bounded collection of exact natural Pell solutions, including a
q³ example. These are external evidence, not Lean elaboration or a proof for
arbitrary models.

From `Computability/DiophantineConsistency`, reproduce the receipt:

```
python3 -I -S -B research/ordinary13-unscale84-first-margin-draft/check.py
```

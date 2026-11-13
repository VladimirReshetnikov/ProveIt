# Proposed 87 first-norm binding for q³ unscaling

This unelaborated source-only client proposes to discharge the existing
`ForwardNormBinding` cut for the exact positive 87/36 graph at any natural
four-port tuple. It pins the current unscaling graph and transfer source
bytes. No Lean build, axiom report, provider replay, endpoint or physical PDF
binding is claimed; in particular any later repair to the unscaling draft
requires reassessing and repinning this client.

For `b=J*beta`, `h=(1+b)^3`, `k=eta+zeta`, and
`ell=X*Y*(Y*k)`, its proposed `root_form` binds the actual signed root as

```
Z=h*b*(ell+k+r-k*Bt)+Y*b-h*Bt.
```

Its `first_form` binds the actual first residual as
`Z²−(h*b)²*(1+ell*(ell+k))`. A graph output zero makes this first residual
zero because the output is a sum of four squares; `cut_of_zero` proposes to
extract both equations for the exact graph root and Bt. Natural port casting
uses the existing `P72Root.cast_port` source. The source then calls the
unscaling packet's unelaborated `forward_of_norm_binding`, which calls the
separate signed-square/divisibility quotient proposal. Thus the claimed
forward cut remains conditional on every source proof and provider actually
checking. Positivity of beta is not needed by this particular quotient lemma;
the positive 87 witness supplies Y>0.

Nothing here proves the converse: the 84→87 positive first-root replacement
remains an explicit `ReverseRootCut`, including its positive carrier,
divisibility, same-root norm and strict margin dependencies. The previous
unscale packet's conditional zero equivalence and the retained parent
endpoint remain separate. No provider compatibility or axiom conclusion is
inferred from source text.

The checker pins exact source bytes, inspects the key JSON rows and exercises
500 model-natural scalar graph assignments against both displayed formulas.
Those controls do not establish an arbitrary-model equality or tactic
elaboration. Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-positive87-first-norm-binding-draft/check.py | cmp - research/ordinary13-positive87-first-norm-binding-draft/receipt.json
```

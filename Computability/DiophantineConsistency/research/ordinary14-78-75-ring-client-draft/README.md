# Same-coordinate 78→75 factor identities — source draft

This source-only ring client compares the reviewed literal `P78AuxRoot` and
`P75NegativePell` draft graphs at identical coordinates and arbitrary signed
integer ports. It proposes the identities

```
F0 = 1 + A0       F1 = 1 + A1       Fa = aux
Fs = 1 + gap      Fg = 1 + guardResidual
```

The four nonfirst factor identities are literal expression equalities; F0
requires the elementary ring identity `r²−ell*(ell+k)=1+[r²−(1+ell*(ell+k))]`.
No positivity, beta or K bound, graph zero or fixed-port assumption is used
in these five identities. The source imports both unelaborated literal graph
drafts; `rfl`, simplification, ring normalization and provider compatibility
are not Lean-checked. This packet does not assert the reverse product-zero
implication, a positive-model comparison, an iPRA endpoint, graph degree or
physical byte/PDF binding. The separately reviewed external comparison and
its `beta>0` positive-domain hypotheses remain distinct.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary14-78-75-ring-client-draft/check_source.py | cmp - research/ordinary14-78-75-ring-client-draft/observation.json
```

The checker compares the five factor dependency DAGs, runs 500 signed
controls, and reproduces both literal graph-generation receipts. The finite
controls and DAG comparison do not elaborate the Lean statements.

Independent source review: [78/75 ring factor identities](../../reviews/ordinary14-78-75-ring-client-independent/README.md).

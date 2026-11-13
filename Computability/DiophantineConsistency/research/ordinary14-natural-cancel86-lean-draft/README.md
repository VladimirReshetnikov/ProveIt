# Literal natural cancel-86 graph — source draft

`P86NaturalCancel.lean` is a source-only transcription of the independently
reviewed [natural-input 86-operation SLP](../ordinary14-root74-natural-cancel86/).
Its 86 listed arithmetic rows and their original order are preserved, with
natural-input coordinates `n_J,n_F,n_alpha,n_f,n_i,n_T,n_w,n_s,n_r,n_eta,
n_zeta,n_y,n_gamma,n_h` at slots 0–13 and ports `beta,K0,MC,MF` at 0–3.
Exposed factor and cut projections are existing expressions, not extra gates.
`output_shape` is proposed source text and has not been elaborated.

The independent standard-integer SLP proof establishes an 86-operation upper
bound and exact equality to the natural shift of the 74 parent, but this Lean
source by itself does not bind its syntax or zero set to that parent, establish
an operation-count theorem, verify Lean/provider compatibility, prove an iPRA
endpoint, or bind physical coefficient bytes/PDF. No Lean run occurred.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-natural-cancel86-lean-draft/make_graph.py --check | cmp - research/ordinary14-natural-cancel86-lean-draft/observation.json
```

Independent source review: [literal natural cancel-86 graph](../../reviews/ordinary14-natural-cancel86-lean-independent/README.md).

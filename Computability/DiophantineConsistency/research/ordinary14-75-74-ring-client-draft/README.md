# Literal 75→74 guard-shift ring client — source draft

This source-only client compares the two literal graph drafts in every
commutative ring, with arbitrary signed integer ports. Its proposed slot-13
update is `h ↦ h+1`; the four restricted factors are shared and omit that
slot, and the guard factors agree after the update. The exact scalar identity
is `C*(X+K)+(1+b−F)−b*(h+1)=1+(C*(X+K)−F−b*h)`. The output equality follows
from the two literal product shapes.

The script and both graph sources are unelaborated. This identity does not
itself establish positive-coordinate reverse transfer, extraction of factors
from a zero, a model/halting bridge, provider compatibility, iPRA, or byte/PDF
binding. In particular the reverse map still needs `h>1` from the candidate's
own zero and the explicit hypotheses in the independently reviewed
[shifted guard fact](../ordinary14-positive-guard74-model-fact-draft/).
No Lean run was performed.

Run the literal graph receipt and finite signed controls from
`Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-75-74-ring-client-draft/check_source.py | cmp - research/ordinary14-75-74-ring-client-draft/observation.json
```

Independent source review: [75 to 74 ring client](../../reviews/ordinary14-75-74-ring-client-independent/README.md).

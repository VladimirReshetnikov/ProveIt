# Independent review: mixed-domain shifted guard

**PASS, external integer arithmetic.** For arbitrary integer ports, the
14-input 74-operation graph has the same zero existence as the all-positive
75-operation parent when its input F is nonnegative and its other thirteen
inputs are strictly positive. The pointwise polynomial identity holds for
all signed integer assignments under `F_old=F+1`. The authenticated graph
has exact degree 107. This is a mixed-domain equation, not a 74-operation
all-positive equation, Lean/iPRA theorem, PDF/JSON binding or global minimum.
The parent's endpoint and provider qualifications are inherited.

The map `F_old=F+1` bijects nonnegative F with positive `F_old`. With
`q=1+b`, the parent scalar becomes
`q−F_old=(1+b)−(F+1)=b−F`, exactly the new scalar. The other affected input
use is the parent guard `C(X+K0)−F_old−bh`; adding its product factor's 1
gives `C(X+K0)−F−bh`, exactly the new guard. The source graph has no other
uses of F, so every other downstream field agrees and the complete outputs
are equal under the shift. No sign condition on ports enters this identity.

The checker reconstructs the exact 75-to-74 source delta and liveness,
proves both shift identities in a sparse integer polynomial ring, checks
that F has only those two direct uses, and independently compares the
remaining DAGs after the two proved cut identities. It replays the author
receipt and authenticates the compact44 P72/P115 bytes. Affine translation
does not increase the parent's degree-107 upper bound; a distinct weighted
ray modulo 1,000,000,009 has degree 107 and proves the matching lower bound.
Finite controls and the source comparison do not add a model or file-binding
theorem. No Lean process is run.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-mixed-guard74-independent/check.py
```

Compare stdout with `result.json`.

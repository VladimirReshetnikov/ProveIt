# Independent source review: X=0 arithmetic obstruction

The fact-level argument and its free-ring certificates have the correct signs. From `z=U*a*c+H*t`, `z²=U²*(1+(H+a²)c²)` and `U!=0`, the pinned signed-square theorem gives a possibly negative d with `z=U*d`. Cancelling U² gives `(d-a*c)(d+a*c)=1+H*c²`, and the root shape gives `H|U*(d-a*c)`. The explicit certificate combines these to give `H|U`; no sign assumption on d or extra coprimality premise is used. The checker independently verifies the `linear_combination` signs and the identity behind the cancellation.

At the stated X=0 specialization, `U=Y*q²`, `H=3+4Y`, `q>=2`, `Y>=q³`; the signed certificate gives `H|3q²`. The pinned signed-to-natural reflection gives natural divisibility, which is impossible because `0<3q²<H`. The second signed certificate, its witness orientation, and finite size controls were independently checked. The order cancellation requires the indicated nonzero U, established from q and Y positivity in the draft.

This is an arithmetic client with explicit signed root and norm hypotheses. It does not by itself derive them from the actual 13/90 graph, supply port representations or authenticate the compact fixed kernel. The source, referenced providers, tactics, axiom reports and graph/model/iPRA endpoint remain unelaborated. The author's bounded receipt reproduces.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue90-xzero-model-independent/check.py | cmp - reviews/ordinary13-residue90-xzero-model-independent/result.json
python3 -I -S -B research/ordinary13-residue90-xzero-model-draft/check.py | cmp - research/ordinary13-residue90-xzero-model-draft/receipt.json
```

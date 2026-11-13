# Independent source review: 84↔79 first-root graph client

**Source review passes; not elaborated.** The proposed fixed-other-coordinate
client has the right fact-level mathematical shape: both source graphs use
the same four other fields, those fields do not depend on slot 8, and the
first residuals are respectively `M²((P−r)²−D)` and `r²−D`. The explicit
port representation `(p 0 : DiffRing V)=ι beta`, and positivity of beta and
slot 0, make `M=q³(J beta)>0`. The radicand `D=1+ell(ell+k)` is positive.
The separately drafted generic bridge then has the required hypotheses.

The comparison fixes the other thirteen coordinates. It does not itself
assert that those coordinates are positive; a global existential client must
use the separate update-positivity lemma and an update-back identity. It also
does not bind the abstract port to the compact44 bytes. The generic and both
graph imports are uncompiled draft sources, and the proposed overlay and
provider ancestry have not been authenticated.

The independent checker pins the client, generic bridge and graph source
bytes, checks both literal graph generators against their recorded receipts,
and compares hashes of the exact DAGs for all four common fields. Dependency
sets show that those fields omit `r`. A sparse polynomial-ring calculation
verifies the first-residual factorization exactly, and the author inventory
and 100 finite controls are replayed. These checks do not elaborate Lean or
prove a theorem in a model; `simp`, `ring`, reduction of the graph definitions,
and the proposed rewrite steps remain untested. No graph/iPRA endpoint or
PDF/JSON semantics follows from this review.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-direct-first-root-graph-client-draft-independent/check.py
```

Compare stdout with `result.json`. The checker does not invoke Lean.

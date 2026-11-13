# Independent review: 71-operation, degree-60 ordinary sphere graph

The read-only [checker](check.py) exited 0 and produced [result.json](result.json).
It compares the first 61 candidate gates with the pinned 67/94 graph, checks
the entire ten-gate tail against `P² + U² + (QW−1)² + H² − 2`, verifies every
row is topological and live, and finds all 14 witnesses and four fixed ports
live. The 71 operations are 38 multiplications, 19 additions and 14
subtractions. The port paths now resolve relative to the candidate graph, and
the compressed and decompressed hashes, sizes and bit lengths all match the
current2011 metadata, totalling 47,313 raw bytes.

The graph's first published revision incorrectly named a local
`coefficients/` directory that did not exist. The corrected graph changes
only this path to the existing `../fourteen-nonzero-spheres/coefficients/`;
the original graph and other first-revision artifacts remain under the
author packet's `history/initial/`. The checker verifies the corrected and
original graph structures are otherwise identical.

Independently of the author's inherited leader certificate, this checker
propagates syntactic degrees from the 14 witness leaves and verifies the
precise gate shapes needed to expand the main norm as

`N1 = X² + 2*X*a*c + 2*gamma*H*(X+a*c) + gamma²*H² - H*c²`.

That cancellation gives `N1` degree at most 18 and the complete graph degree
at most 60. Substituting `t` for all witnesses and the recorded fixed integers
for all ports gives a nonzero coefficient **176,981,100 modulo
1,000,000,007** on `t^60`. Consequently the graph at those recorded fixed
integers has exact total degree 60. This is an external finite argument, not
a Lean `totalDegree` theorem or a Lean proof relating the serialized bytes
to the port tuple. The author's check was rerun and matched its frozen result.

This review does not prove that the graph has the same zeros as the 67/94
equation, a model theorem, or an iPRA derivation. Those are separate proof
obligations and must be checked independently before calling the candidate a
consistency equation.

Reproduce from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current2011-ordinary71-60-graph-independent/check.py
```

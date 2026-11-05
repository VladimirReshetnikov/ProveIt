# Independent review: 70-operation, degree-84 ordinary sphere graph

The read-only [checker](check.py) exited 0 and produced [result.json](result.json).
It compares the first 61 candidate gates with the pinned 67/94 graph, checks
the complete nine-gate tail against `U² + (PQW−1)² + H² − 1`, verifies
topology and liveness of all rows and inputs, and checks the four compressed
and decompressed current2011 port payloads through the graph's actual relative
path. The 70 operations are 38 multiplications, 18 additions and 14
subtractions; all 14 positive witness leaves and four port leaves are live.

Independently of the author's inherited degree certificate, this checker
propagates degree bounds and verifies the exact graph shapes for the main
norm cancellation

`N1 = X² + 2*X*a*c + 2*gamma*H*(X+a*c) + gamma²*H² - H*c²`.

This gives a graph degree upper bound of 84. Substituting one variable `t`
for all witnesses and the recorded fixed integers for the ports yields
coefficient **589,155,221 modulo 1,000,000,007** on `t^84`, establishing
the matching lower bound for those integers. The author's checker reran and
matched its frozen output. Degree and serialized-port comparison are external
finite checks, not Lean theorems about degree or gzip/file semantics.

This review does not prove zero equivalence, an IΣ₁-model bridge, or an iPRA
endpoint. Those are separate obligations; this check alone does not establish
the candidate as a consistency equation.

Reproduce from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current2011-ordinary70-84-graph-independent/check.py
```

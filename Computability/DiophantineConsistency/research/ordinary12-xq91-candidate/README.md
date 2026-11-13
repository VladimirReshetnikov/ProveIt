# A 91-operation fixed-port candidate

Replace the 92-graph witness `X` by `q w`, where `q=1+Jβ` and the new
witness `w` is positive. The existing `Y=q³s` substitution remains. Two
exact polynomial identities reduce the resulting live graph:

```
C*(q*w + K0*q) - F*q = q*(C*(K0+w)-F)
U*gamma + E*q = U*(gamma+w),  where E=(q*w)*Y and U=Y*q².
```

The [complete graph](candidate.json) has 12 positive witnesses and 91 live
binary integer-leaf operations: 50 multiplications, 24 additions and 17
subtractions. [check_graph.py](check_graph.py) checks every transformed row,
the witness/port correspondence, topological order and liveness, then tests
all residuals and the output on 30 exact integer substitutions. The static
graph and test samples are external checks, not a Lean theorem about JSON.

The [degree checker](check_degree.py) verifies the identity
`h=(V+n)²−1−Q*n*(2V+n)`, giving total degree at most 172. It authenticates
the retained fixed-port coefficient bytes and finds a nonzero leading
coefficient `960910299` modulo `1000000007` after a linear witness
substitution. Thus the fixed-port graph has exact degree 172 by this external
certificate. The syntactic bound before cancellation is 200.

The proposed model-equivalence argument uses the earlier checked 92-to-95
positive-zero map. For the compact fixed ports, the existing
`FreeJCompactBeta.compact_graph_alignment` theorem applies in every `IΣ₁`
model to a positive 95-graph zero: the checked fixed-beta bound supplies
`β>0`, `MC<β` and `MF<2β`, while `β=2^(67*8807)−1=2^590069−1` supplies the
exact beta premise. It yields `X=q w`; positivity of `X` forces `w>0`.
Conversely, any positive new witness maps to a positive old witness by
`X=q w`. Nonstandard witnesses are included in this model-level route.
This use of compact-beta alignment is **specific to the fixed ports and their
proved bounds**; the converse is not claimed for arbitrary ports.

The ring residual comparisons have passed Lean; see [ALGEBRA.md](ALGEBRA.md).
A separate guarded all-model proof now establishes the fixed-port positive
zero/halt equivalence and its shifted byte-recipe version; see [HALT.md](HALT.md)
for its exact scope and provider evidence. The JSON-to-Lean comparison is an
external source check. This packet does **not** claim an iPRA derivation, a
Lean interpretation of JSON/gzip/PDF, or global minimality.

From this directory, run:

```sh
python3 -I -S -B check_graph.py
python3 -I -S -B check_degree.py
```

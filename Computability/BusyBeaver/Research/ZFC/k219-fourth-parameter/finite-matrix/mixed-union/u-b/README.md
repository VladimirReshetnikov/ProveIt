# U=B remains unresolved by these diagnostics

These searches concern the retained native calculus and its literal full
gated bundle with both restricted rho8 rows `U=R(A,B)` and `U=B`. They do
not establish consistency, calibration, or a state-count improvement.

The [schema run](results/schema-result.json) completed five rounds: 393
schemas, 40,000 cumulative major/minor pairs and 22 size rejections, with
limits of 160 nodes, 1,500 schemas and 12 seconds. It found none of its listed
generic targets: falsity, identity, K, S, Peirce, explosion or `A → truth`.
Each retained positive witness is an instantiated numerical-constructor
schema with its gate conditions and the native `I(0,0)=0` alias. The search
does not assume arbitrary theorem substitution and is not complete for
native proofs. Its [proof witnesses](results/schema-proofs.json.gz) are
compressed without changing the JSON; the uncompressed identity is in
[summary.json](summary.json).

Eight heuristic matrix runs used three or four values and one or two
designated values, five seconds per run. Four retained K as an additional
axiom; four omitted it. Across 22,828,000 proposals and 40.00748 seconds,
none found a model. The exact best unsuccessful tables and failure scores
are retained under `results/`. This mutation search is not exhaustive, even
for those small carriers. The literal bundle keeps its matrix/private-code
coupling; it is not replaced by independent matrix and private-label values.

The programs derive from Opening's
[constructor-schema search](../../../six-orientations/evidence/condensed_v2.py)
and [code-dependent model search](../../../../k218-k-membership-obstruction/search.cpp).
The first adaptation adds only the universally quantified `U=B` root.
The C++ adaptation adds its corresponding score constraint, with a separate
successor omitting K. Original attribution, identities and exact diffs are
retained beside the sources. No supplied package code is imported.

Optional bounded reproduction from the repository root (use fresh output
paths; timing-limited proposal counts may vary):

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-fourth-parameter/finite-matrix/mixed-union/u-b/condensed-rab-b.py \
  --variant ab --bundle --out /tmp/mixed-ub-schema-new \
  --rounds 5 --max-schemas 1500 --max-nodes 160 --seconds 12
g++ -std=c++17 -O2 Computability/BusyBeaver/Research/ZFC/k219-fourth-parameter/finite-matrix/mixed-union/u-b/search-rab-hb-only.cpp \
  -o /tmp/mixed-ub-search
/tmp/mixed-ub-search 5 3 1 222 > /tmp/mixed-ub-new.json 2> /tmp/mixed-ub-new.log
```

The C++ arguments are seconds, carrier size, designated count and seed.
The [without-K commands](search-only-runs.json) used `(3,1,222)`,
`(3,2,223)`, `(4,1,224)`, `(4,2,225)`; the
[with-K commands](search-runs.json) used seeds 218–221 with the same four
size/count pairs and `search-rab-hb.cpp`. Every actual run returned zero
under a ten-second external cap. No binary is committed and no bounded
search was rerun to prepare this publication.
